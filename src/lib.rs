//! SAS parser plugin — full-parse mode.
//!
//! Handles `.sas` files using case-insensitive line scanning.
//! SAS programs are structured around macro definitions, DATA steps, and PROC steps.
//!
//! Semantic nodes produced:
//!   sas_program — root
//!   macro       — %MACRO … %MEND block (label = macro name)
//!   data_step   — DATA … RUN/QUIT block (label = dataset name)
//!   proc_step   — PROC … RUN/QUIT block (label = "PROCNAME" or "PROCNAME (DATA=ds)")

use intentumdiff_plugin_sdk::tree::{SemanticNode, SemanticNodeBuilder};

wit_bindgen::generate!({
    path: "wit/plugin.wit",
    world: "parser-plugin",
});

use crate::exports::intentdiff::plugin::parser::ExamplePair;
use crate::exports::intentdiff::plugin::parser::Guest;
use crate::exports::intentdiff::plugin::parser::LanguageInfoRecord;
use crate::exports::intentdiff::plugin::parser::ParserMode;

const PLUGIN_METADATA: &str = include_str!("../plugin_metadata.info");

fn language_info_for(ids: Vec<String>) -> Vec<LanguageInfoRecord> {
    let metadata = intentumdiff_plugin_sdk::metadata::parse_plugin_metadata(PLUGIN_METADATA);
    ids.into_iter()
        .map(|language_id| {
            let info = metadata.language_or_default(&language_id);
            LanguageInfoRecord {
                language_id: info.language_id,
                language_name: info.language_name,
                language_short_name: info.language_short_name,
                monaco_language: info.monaco_language,
                default_filename: info.default_filename,
                language_file_extensions: info.language_file_extensions,
                author: metadata.author().to_string(),
                plugin_version: metadata.plugin_version().to_string(),
                last_updated: metadata.last_updated().to_string(),
            }
        })
        .collect()
}
struct SasParser;

// ---------------------------------------------------------------------------
// Language detection
// ---------------------------------------------------------------------------

pub(crate) fn detect_language_impl(filename: &str, _content: &str) -> String {
    if filename.to_lowercase().ends_with(".sas") {
        "sas".to_string()
    } else {
        String::new()
    }
}

// ---------------------------------------------------------------------------
// Parser
// ---------------------------------------------------------------------------

// Replace comments with spaces, preserving UTF-8 byte offsets and line breaks.
// Quote tracking prevents comment-looking macro values from being discarded.
fn without_comments(source: &str) -> Result<String, &'static str> {
    let bytes = source.as_bytes();
    let mut output = bytes.to_vec();
    let mut i = 0;
    let mut quote = None;
    let mut statement_start = true;
    while i < bytes.len() {
        if let Some(q) = quote {
            if bytes[i] == q {
                if bytes.get(i + 1) == Some(&q) {
                    i += 2;
                    continue;
                }
                quote = None;
            }
            i += 1;
            continue;
        }
        let block = bytes[i..].starts_with(b"/*");
        let statement_comment =
            bytes[i..].starts_with(b"%*") || (statement_start && bytes[i] == b'*');
        if block || statement_comment {
            let start = i;
            i += if block || bytes[start] == b'%' { 2 } else { 1 };
            while i < bytes.len()
                && !(if block {
                    bytes[i..].starts_with(b"*/")
                } else {
                    bytes[i] == b';'
                })
            {
                i += 1;
            }
            if i == bytes.len() {
                return Err("Unterminated SAS comment");
            }
            i += if block { 2 } else { 1 };
            for byte in &mut output[start..i] {
                if !matches!(*byte, b'\n' | b'\r') {
                    *byte = b' ';
                }
            }
            continue;
        }
        if matches!(bytes[i], b'\'' | b'"') {
            quote = Some(bytes[i]);
        }
        if bytes[i] == b';' {
            statement_start = true;
        } else if !bytes[i].is_ascii_whitespace() {
            statement_start = false;
        }
        i += 1;
    }
    String::from_utf8(output).map_err(|_| "Invalid SAS comment boundary")
}

/// One semicolon-terminated SAS statement, located in the original source.
struct Statement {
    /// Statement text without its terminating `;`, whitespace runs outside
    /// quoted strings collapsed to one space (layout is not semantics).
    text: String,
    start: (u32, u32),
    end: (u32, u32),
}

/// Byte offset -> (0-based row, UTF-8 byte column).
struct LineIndex {
    starts: Vec<usize>,
}

impl LineIndex {
    fn new(source: &str) -> Self {
        let mut starts = vec![0];
        starts.extend(
            source
                .bytes()
                .enumerate()
                .filter(|(_, b)| *b == b'\n')
                .map(|(i, _)| i + 1),
        );
        LineIndex { starts }
    }

    fn at(&self, offset: usize) -> (u32, u32) {
        let row = self.starts.partition_point(|&s| s <= offset) - 1;
        (row as u32, (offset - self.starts[row]) as u32)
    }
}

fn starts_with_ignore_case(bytes: &[u8], prefix: &[u8]) -> bool {
    bytes.len() >= prefix.len() && bytes[..prefix.len()].eq_ignore_ascii_case(prefix)
}

/// Collapse whitespace outside quoted strings; quoted content is kept verbatim.
fn normalize_statement(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut quote: Option<char> = None;
    let mut pending_space = false;
    for ch in text.chars() {
        if let Some(q) = quote {
            out.push(ch);
            if ch == q {
                quote = None;
            }
            continue;
        }
        if ch.is_whitespace() {
            pending_space = !out.is_empty();
            continue;
        }
        if pending_space {
            out.push(' ');
            pending_space = false;
        }
        if ch == '\'' || ch == '"' {
            quote = Some(ch);
        }
        out.push(ch);
    }
    out
}

/// Split comment-free SAS source into statements. A `;` ends a statement
/// unless it is inside a quoted string or a `%str(...)` / `%nrstr(...)`
/// macro quoting function. Several statements may share one line and one
/// statement may span several lines; text after the last `;` is kept as a
/// final unterminated statement so no source is silently dropped.
fn split_statements(source: &str) -> Vec<Statement> {
    let bytes = source.as_bytes();
    let index = LineIndex::new(source);
    let mut statements = Vec::new();
    let mut i = 0;
    while i < bytes.len() {
        while i < bytes.len() && bytes[i].is_ascii_whitespace() {
            i += 1;
        }
        if i >= bytes.len() {
            break;
        }
        let start = i;
        let mut quote: Option<u8> = None;
        let mut macro_paren_depth = 0usize;
        let mut terminator = None;
        while i < bytes.len() {
            let b = bytes[i];
            if let Some(q) = quote {
                if b == q {
                    quote = None;
                }
                i += 1;
                continue;
            }
            match b {
                b'\'' | b'"' => quote = Some(b),
                b'%' if macro_paren_depth == 0
                    && (starts_with_ignore_case(&bytes[i..], b"%str(")
                        || starts_with_ignore_case(&bytes[i..], b"%nrstr(")) =>
                {
                    let open = i + bytes[i..].iter().position(|&c| c == b'(').unwrap_or(0);
                    macro_paren_depth = 1;
                    i = open + 1;
                    continue;
                }
                b'(' if macro_paren_depth > 0 => macro_paren_depth += 1,
                b')' if macro_paren_depth > 0 => macro_paren_depth -= 1,
                b';' if macro_paren_depth == 0 => {
                    terminator = Some(i);
                    break;
                }
                _ => {}
            }
            i += 1;
        }
        let (body_end, end) = match terminator {
            Some(semi) => (semi, semi + 1),
            None => {
                let trimmed = source[start..].trim_end().len();
                (start + trimmed, start + trimmed)
            }
        };
        i = end;
        let text = normalize_statement(&source[start..body_end]);
        statements.push(Statement {
            text,
            start: index.at(start),
            end: index.at(end),
        });
    }
    statements
}

/// An open container (root, %MACRO, DATA step or PROC step) being filled.
struct Frame {
    id: String,
    node_type: &'static str,
    label: String,
    start: (u32, u32),
    end: (u32, u32),
    children: Vec<SemanticNode>,
}

impl Frame {
    fn next_id(&self) -> String {
        format!("{}.{}", self.id, self.children.len())
    }

    fn is_step(&self) -> bool {
        matches!(self.node_type, "data_step" | "proc_step")
    }

    fn push_statement(&mut self, stmt: &Statement) {
        let id = self.next_id();
        self.children.push(
            SemanticNodeBuilder::new(
                &id,
                "sas_statement",
                &stmt.text,
                stmt.start.0,
                stmt.start.1,
                stmt.end.0,
                stmt.end.1,
                String::new(),
            )
            .build(),
        );
        self.end = stmt.end;
    }

    fn into_node(self) -> SemanticNode {
        SemanticNodeBuilder::new(
            &self.id,
            self.node_type,
            &self.label,
            self.start.0,
            self.start.1,
            self.end.0,
            self.end.1,
            String::new(),
        )
        .children(self.children)
        .build()
    }
}

/// Pop the innermost frame into its parent. The root frame is never popped.
fn close_top(stack: &mut Vec<Frame>) {
    if stack.len() > 1 {
        let frame = stack.pop().expect("stack has a non-root frame");
        let parent = stack.last_mut().expect("root frame remains");
        parent.end = frame.end;
        parent.children.push(frame.into_node());
    }
}

/// Open a block whose opening statement is kept verbatim as its first child,
/// so header-only edits (macro parameter defaults, PROC/DATA options) are
/// visible as content changes rather than vanishing into the block label.
fn open_block(stack: &mut Vec<Frame>, node_type: &'static str, label: String, header: &Statement) {
    let id = stack.last().expect("root frame").next_id();
    let mut frame = Frame {
        id,
        node_type,
        label,
        start: header.start,
        end: header.end,
        children: Vec::new(),
    };
    frame.push_statement(header);
    stack.push(frame);
}

pub(crate) fn parse_sas(source: &str) -> String {
    let uncommented = match without_comments(source) {
        Ok(text) => text,
        Err(error) => return serde_json::json!({"error": error}).to_string(),
    };
    let total_lines = source.lines().count().saturating_sub(1) as u32;
    let mut stack = vec![Frame {
        id: "0".to_string(),
        node_type: "sas_program",
        label: "sas_program".to_string(),
        start: (0, 0),
        end: (0, 0),
        children: Vec::new(),
    }];

    for stmt in split_statements(&uncommented) {
        let upper = stmt.text.to_uppercase();
        let words: Vec<&str> = upper.split_whitespace().collect();
        let Some(&first) = words.first() else {
            continue;
        };
        match first {
            "%MACRO" => {
                let name = words
                    .get(1)
                    .and_then(|w| w.split('(').next())
                    .filter(|w| !w.is_empty())
                    .unwrap_or("(anonymous)")
                    .to_string();
                open_block(&mut stack, "macro", name, &stmt);
            }
            "%MEND" if stack.iter().any(|f| f.node_type == "macro") => {
                while let Some(top) = stack.last_mut() {
                    let is_macro = top.node_type == "macro";
                    top.end = stmt.end;
                    close_top(&mut stack);
                    if is_macro {
                        break;
                    }
                }
            }
            "DATA" | "PROC" if first == "DATA" || words.len() >= 2 => {
                // A DATA or PROC statement implicitly ends the previous step.
                if stack.last().is_some_and(Frame::is_step) {
                    close_top(&mut stack);
                }
                let (node_type, label) = if first == "DATA" {
                    let name = words.get(1).copied().unwrap_or("(anonymous)");
                    ("data_step", name.to_string())
                } else {
                    let proc_name = words[1];
                    let label = match words.iter().find(|w| w.starts_with("DATA=")) {
                        Some(arg) => format!("{} (DATA={})", proc_name, &arg["DATA=".len()..]),
                        None => proc_name.to_string(),
                    };
                    ("proc_step", label)
                };
                open_block(&mut stack, node_type, label, &stmt);
            }
            "RUN" | "QUIT" if stack.last().is_some_and(Frame::is_step) => {
                let top = stack.last_mut().expect("step frame");
                if words.len() > 1 {
                    // `RUN CANCEL;` and friends change behaviour: keep them.
                    top.push_statement(&stmt);
                }
                top.end = stmt.end;
                close_top(&mut stack);
            }
            _ => stack.last_mut().expect("root frame").push_statement(&stmt),
        }
    }

    // Drain unclosed blocks.
    while stack.len() > 1 {
        close_top(&mut stack);
    }
    let mut root = stack.pop().expect("root frame");
    root.start = (0, 0);
    root.end = (total_lines, 0);
    let root = root.into_node();

    match serde_json::to_string(&root) {
        Ok(s) => s,
        Err(e) => format!(r#"{{"error":"Serialisation error: {}"}}"#, e),
    }
}

// ---------------------------------------------------------------------------
// WIT guest impl
// ---------------------------------------------------------------------------

impl Guest for SasParser {
    fn get_parser_mode() -> ParserMode {
        ParserMode::FullParse
    }
    fn grammar_id() -> String {
        "sas".to_string()
    }
    fn detect_language(filename: String, content: String) -> String {
        detect_language_impl(&filename, &content)
    }
    fn preprocess_source(source: String) -> String {
        source
    }
    fn example(_language: String) -> ExamplePair {
        ExamplePair {
            old: "data work.greeting;\n  name = \"World\";\n  message = cats(\"Hello, \", name);\n  put message;\nrun;\n".to_string(),
            new: "%let target = World;\n\ndata work.greeting;\n  name    = \"&target\";\n  suffix  = \"!\";\n  message = cats(\"Hello, \", name, suffix);\n  length  = lengthn(message);\n  put message= length=;\nrun;\n\nproc print data=work.greeting; run;\n".to_string(),
        }
    }
    fn process(input: String, _language: String, _filename: String) -> String {
        parse_sas(&input)
    }
    fn trivia_node_types() -> Vec<String> {
        vec![]
    }
    fn language_ids() -> Vec<String> {
        vec!["sas".to_string()]
    }
    fn language_info() -> Vec<LanguageInfoRecord> {
        language_info_for(Self::language_ids())
    }
    fn priority() -> i32 {
        0
    }
}

export!(SasParser);

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    intentumdiff_plugin_sdk::plugin_compliance_tests! {
        process: parse_sas,
        detect_fn: detect_language_impl,
        detect_cases: [
            ("analysis.sas", "", "sas"),
            ("ANALYSIS.SAS", "", "sas"),
            ("script.sql",   "", ""),
            ("script.txt",   "", ""),
        ],
        grammar_id: "sas",
        language_ids: ["sas"],
    }

    #[test]
    fn interior_statement_spans_cover_changed_bytes_in_utf8_source() {
        for (before, after, start_col) in [
            (
                "data work.metrics;\n  attempts = 4;\nrun;\n",
                "data work.metrics;\n  attempts = 5;\nrun;\n",
                2,
            ),
            (
                "proc print;\n    note = 'café' || 4;\nrun;\n",
                "proc print;\n    note = 'café' || 5;\nrun;\n",
                4,
            ),
        ] {
            let old: serde_json::Value = serde_json::from_str(&parse_sas(before)).unwrap();
            let new: serde_json::Value = serde_json::from_str(&parse_sas(after)).unwrap();
            // Child 0 is the step's opening statement; the edit is child 1.
            let old_leaf = &old["children"][0]["children"][1];
            let new_leaf = &new["children"][0]["children"][1];
            assert_ne!(old_leaf["label"], new_leaf["label"]);
            let old_col = before.lines().nth(1).unwrap().find('4').unwrap() as u32;
            let new_col = after.lines().nth(1).unwrap().find('5').unwrap() as u32;
            for (leaf, col) in [(old_leaf, old_col), (new_leaf, new_col)] {
                assert_eq!(leaf["node_type"], "sas_statement");
                assert_eq!(leaf["position"]["start_line"], 1);
                assert_eq!(leaf["position"]["end_line"], 1);
                assert_eq!(leaf["position"]["start_col"], start_col);
                assert!(
                    leaf["position"]["start_col"].as_u64().unwrap() <= col as u64
                        && leaf["position"]["end_col"].as_u64().unwrap() > col as u64,
                    "the changed byte at column {col} must fall inside {leaf:?}"
                );
            }
        }
    }

    #[test]
    fn top_level_macro_assignment_retains_value_and_source_span() {
        let before = "\n  %let target = World;\ndata _null_;\n  put \"&target\";\nrun;\n";
        let after = before.replace("World", "Other");
        let old: serde_json::Value = serde_json::from_str(&parse_sas(before)).unwrap();
        let new: serde_json::Value = serde_json::from_str(&parse_sas(&after)).unwrap();
        assert_eq!(old["children"][0]["label"], "%let target = World");
        assert_eq!(new["children"][0]["label"], "%let target = Other");
        assert_eq!(
            new["children"][0]["position"],
            serde_json::json!({
                "start_line": 1, "start_col": 2, "end_line": 1, "end_col": 22
            })
        );
        assert_eq!(new["children"][1]["node_type"], "data_step");
        assert_eq!(
            new["children"][1]["children"][1]["label"],
            "put \"&target\""
        );
    }

    #[test]
    fn top_level_statements_survive_between_steps_and_at_eof() {
        let source =
            "data first;\nrun;\n%let target = café;\nproc print data=first;\nrun;\n%put &target;\n";
        let tree: serde_json::Value = serde_json::from_str(&parse_sas(source)).unwrap();
        let nodes = tree["children"].as_array().unwrap();
        assert_eq!(nodes.len(), 4);
        assert_eq!(nodes[1]["label"], "%let target = café");
        assert_eq!(nodes[3]["label"], "%put &target");
        assert_eq!(nodes[1]["position"]["start_line"], 2);
        assert_eq!(nodes[1]["position"]["end_col"], "%let target = café;".len());
        let ids: std::collections::HashSet<_> =
            nodes.iter().map(|n| n["id"].as_str().unwrap()).collect();
        assert_eq!(ids.len(), nodes.len());
        assert_eq!(parse_sas(source), parse_sas(source));
    }

    #[test]
    fn global_comments_are_trivia_but_quoted_comment_markers_are_values() {
        for (old, new) in [
            ("/* old */\n%let x = 1;", "/* new */\n%let x = 1;"),
            ("%* old;\n%let x = 1;", "%* new;\n%let x = 1;"),
            (
                "/* old\n comment */ %let x = 1;",
                "/* new\n comment */ %let x = 1;",
            ),
            (
                "%* old\n comment; %let x = 1;",
                "%* new\n comment; %let x = 1;",
            ),
        ] {
            assert_eq!(parse_sas(old), parse_sas(new));
        }
        let tree: serde_json::Value =
            serde_json::from_str(&parse_sas("%let x = '/* value */';")).unwrap();
        assert_eq!(tree["children"][0]["label"], "%let x = '/* value */'");
    }

    const SAMPLE: &str = "%MACRO calculate(dataset=);\n\
        PROC MEANS DATA=&dataset;\n\
        RUN;\n\
        %MEND calculate;\n\
        \n\
        DATA work_data;\n\
          SET input_data;\n\
        RUN;\n\
        \n\
        PROC PRINT DATA=work_data;\n\
        RUN;\n";

    #[test]
    fn test_valid_json_no_error() {
        let out = parse_sas(SAMPLE);
        intentumdiff_plugin_sdk::testing::assert_valid_json(&out, "SAMPLE");
        intentumdiff_plugin_sdk::testing::assert_no_error(&out, "SAMPLE");
    }

    #[test]
    fn test_root_is_sas_program() {
        let out = parse_sas(SAMPLE);
        intentumdiff_plugin_sdk::testing::assert_root_node_type(&out, "sas_program", "SAMPLE");
    }

    #[test]
    fn test_macro_found() {
        let out = parse_sas(SAMPLE);
        intentumdiff_plugin_sdk::testing::assert_contains_node_type(&out, "macro", "macro");
    }

    #[test]
    fn test_data_step_found() {
        let out = parse_sas(SAMPLE);
        intentumdiff_plugin_sdk::testing::assert_contains_node_type(&out, "data_step", "data_step");
    }

    #[test]
    fn test_proc_step_found() {
        let out = parse_sas(SAMPLE);
        intentumdiff_plugin_sdk::testing::assert_contains_node_type(&out, "proc_step", "proc_step");
    }

    #[test]
    fn test_proc_label_includes_data() {
        let src = "PROC PRINT DATA=mydata;\nRUN;";
        let out = parse_sas(src);
        let v: serde_json::Value = serde_json::from_str(&out).unwrap();
        let children = v["children"].as_array().unwrap();
        let label = children
            .iter()
            .find(|c| c["node_type"].as_str() == Some("proc_step"))
            .and_then(|c| c["label"].as_str())
            .unwrap_or("");
        assert!(
            label.contains("DATA="),
            "proc label should include DATA= arg, got {:?}",
            label
        );
    }

    #[test]
    fn test_simple_macro() {
        let src = "%MACRO greet;\n  %PUT Hello;\n%MEND greet;";
        let out = parse_sas(src);
        intentumdiff_plugin_sdk::testing::assert_contains_node_type(&out, "macro", "simple macro");
    }

    #[test]
    fn test_labels_nonempty() {
        let out = parse_sas(SAMPLE);
        intentumdiff_plugin_sdk::testing::assert_labels_nonempty(&out, "macro", "labels");
        intentumdiff_plugin_sdk::testing::assert_labels_nonempty(&out, "data_step", "labels");
        intentumdiff_plugin_sdk::testing::assert_labels_nonempty(&out, "proc_step", "labels");
    }

    #[test]
    fn interior_statements_anchor_labels_to_original_utf8_bytes() {
        let source = "data work.greeting;\n  message = cats(\"Olá\", name);\n  attempts = 4;\nrun;\n\ndata work.audit;\n  checked = 9;\nrun;\n";
        let tree: serde_json::Value = serde_json::from_str(&parse_sas(source)).unwrap();
        let steps = tree["children"].as_array().unwrap();
        for (step, child, line, label) in [
            (0, 1, 1, "message = cats(\"Olá\", name)"),
            (0, 2, 2, "attempts = 4"),
            (1, 1, 6, "checked = 9"),
        ] {
            let node = &steps[step]["children"][child];
            assert_eq!(node["label"], label);
            let span = &node["position"];
            assert_eq!(span["start_line"].as_u64(), Some(line));
            assert_eq!(span["end_line"].as_u64(), Some(line));
            let raw = source.lines().nth(line as usize).unwrap();
            let start = span["start_col"].as_u64().unwrap() as usize;
            let end = span["end_col"].as_u64().unwrap() as usize;
            assert!(start < end && end <= raw.len(), "{node:?}");
            assert_eq!(raw[start..end].trim_end_matches(';'), label);
            assert_eq!(start, 2);
            assert_eq!(end, raw.len());
        }
    }

    #[test]
    fn inline_proc_has_nonempty_original_utf8_source_extent() {
        // The same-line PROC/RUN fixture previously had (18,0)-(18,0).
        let source = "  proc print data=work.greeting; run;\n";
        let tree: serde_json::Value = serde_json::from_str(&parse_sas(source)).unwrap();
        let nodes = tree["children"].as_array().unwrap();
        assert_eq!(nodes.len(), 1);
        assert_eq!(nodes[0]["node_type"], "proc_step");
        assert_eq!(nodes[0]["label"], "PRINT (DATA=WORK.GREETING)");
        assert_eq!(nodes[0]["position"]["start_line"].as_u64(), Some(0));
        assert_eq!(nodes[0]["position"]["start_col"].as_u64(), Some(2));
        assert_eq!(nodes[0]["position"]["end_line"].as_u64(), Some(0));
        assert_eq!(
            nodes[0]["position"]["end_col"].as_u64(),
            Some(source.trim_end().len() as u64)
        );
    }

    // -- #9: macro defaults, PROC options and inline statements ---------------

    fn tree(source: &str) -> serde_json::Value {
        let out = parse_sas(source);
        intentumdiff_plugin_sdk::testing::assert_no_error(&out, source);
        serde_json::from_str(&out).unwrap()
    }

    /// Every node as (node_type, label, [start_line, start_col, end_line, end_col]).
    fn flatten(node: &serde_json::Value, out: &mut Vec<(String, String, [u64; 4])>) {
        let p = &node["position"];
        out.push((
            node["node_type"].as_str().unwrap().to_string(),
            node["label"].as_str().unwrap().to_string(),
            [
                p["start_line"].as_u64().unwrap(),
                p["start_col"].as_u64().unwrap(),
                p["end_line"].as_u64().unwrap(),
                p["end_col"].as_u64().unwrap(),
            ],
        ));
        for child in node["children"].as_array().unwrap() {
            flatten(child, out);
        }
    }

    fn nodes(source: &str) -> Vec<(String, String, [u64; 4])> {
        let mut out = Vec::new();
        flatten(&tree(source), &mut out);
        out
    }

    /// Source text covered by a single-line span.
    fn span_text<'a>(source: &'a str, span: [u64; 4]) -> &'a str {
        assert_eq!(span[0], span[2], "single-line span expected");
        let line = source.lines().nth(span[0] as usize).unwrap();
        &line[span[1] as usize..span[3] as usize]
    }

    /// The statements that differ between two sources, with their spans.
    fn changed_statements(old: &str, new: &str) -> Vec<((String, [u64; 4]), (String, [u64; 4]))> {
        let pick = |source: &str| -> Vec<(String, [u64; 4])> {
            nodes(source)
                .into_iter()
                .filter(|(t, _, _)| t == "sas_statement")
                .map(|(_, l, s)| (l, s))
                .collect()
        };
        let (a, b) = (pick(old), pick(new));
        assert_eq!(a.len(), b.len(), "{a:?} vs {b:?}");
        a.into_iter().zip(b).filter(|(x, y)| x.0 != y.0).collect()
    }

    #[test]
    fn exact_issue_9_pairs_change_one_statement_with_source_spans() {
        for (old, new, old_label, new_label, old_text, new_text) in [
            (
                "%macro greet(x=one);\n  %put &x;\n%mend;\n%greet();\n",
                "%macro greet(x=two);\n  %put &x;\n%mend;\n%greet();\n",
                "%macro greet(x=one)",
                "%macro greet(x=two)",
                "%macro greet(x=one);",
                "%macro greet(x=two);",
            ),
            (
                "%macro f(x=1);\n%put &x;\n%mend;\n",
                "%macro f(x=2);\n%put &x;\n%mend;\n",
                "%macro f(x=1)",
                "%macro f(x=2)",
                "%macro f(x=1);",
                "%macro f(x=2);",
            ),
            (
                "proc sort data=work.input out=work.output;\n  by id;\nrun;\n",
                "proc sort data=work.input out=work.output nodupkey;\n  by id;\nrun;\n",
                "proc sort data=work.input out=work.output",
                "proc sort data=work.input out=work.output nodupkey",
                "proc sort data=work.input out=work.output;",
                "proc sort data=work.input out=work.output nodupkey;",
            ),
            (
                "proc sort data=work.a;\n by x;\nrun;\n",
                "proc sort data=work.a nodupkey;\n by x;\nrun;\n",
                "proc sort data=work.a",
                "proc sort data=work.a nodupkey",
                "proc sort data=work.a;",
                "proc sort data=work.a nodupkey;",
            ),
            (
                "data a; x=1; run;\n",
                "data a; x=2; run;\n",
                "x=1",
                "x=2",
                "x=1;",
                "x=2;",
            ),
        ] {
            let changed = changed_statements(old, new);
            assert_eq!(changed.len(), 1, "{old:?} -> {new:?}: {changed:?}");
            let ((ol, os), (nl, ns)) = &changed[0];
            assert_eq!((ol.as_str(), nl.as_str()), (old_label, new_label));
            assert_eq!(span_text(old, *os), old_text);
            assert_eq!(span_text(new, *ns), new_text);
        }
    }

    #[test]
    fn inline_step_statements_are_split_on_semicolons_with_byte_columns() {
        let source = "data a; x=1; run;\n";
        let all = nodes(source);
        assert_eq!(
            all,
            vec![
                ("sas_program".into(), "sas_program".into(), [0, 0, 0, 0]),
                ("data_step".into(), "A".into(), [0, 0, 0, 17]),
                ("sas_statement".into(), "data a".into(), [0, 0, 0, 7]),
                ("sas_statement".into(), "x=1".into(), [0, 8, 0, 12]),
            ]
        );
        // The same constructs on multiple lines and with UTF-8 before them.
        let multi = "data a;\n  é = 'x;y'; x\n   = 1;\nrun;\n";
        let all = nodes(multi);
        assert_eq!(all[3].1, "é = 'x;y'");
        assert_eq!(span_text(multi, all[3].2), "é = 'x;y';");
        assert_eq!(all[4].1, "x = 1");
        assert_eq!(all[4].2, [1, 14, 2, 7]);
    }

    #[test]
    fn multiline_headers_keep_every_option_and_parameter() {
        let old = "%macro greet(\n  x=one,\n  y=2\n);\n%mend greet;\nproc sort\n  data=a\n  out=b;\n  by id;\nrun;\n";
        let new = old
            .replace("y=2", "y=3")
            .replace("out=b;", "out=b nodupkey;");
        let a = nodes(old);
        let b = nodes(&new);
        assert_eq!(a[1], ("macro".into(), "GREET".into(), [0, 0, 4, 12]));
        assert_eq!(a[2].1, "%macro greet( x=one, y=2 )");
        assert_eq!(b[2].1, "%macro greet( x=one, y=3 )");
        assert_eq!(
            a[3],
            ("proc_step".into(), "SORT (DATA=A)".into(), [5, 0, 9, 4])
        );
        assert_eq!(a[4].1, "proc sort data=a out=b");
        assert_eq!(b[4].1, "proc sort data=a out=b nodupkey");
    }

    #[test]
    fn quoted_and_macro_quoted_delimiters_do_not_split_statements() {
        let source = "%let a = %str(x;y);\n%let b = \"p;/*q*/\";\ndata d; s = 'it''s;'; run;\n";
        let labels: Vec<String> = nodes(source).into_iter().map(|n| n.1).collect();
        assert_eq!(
            labels,
            vec![
                "sas_program",
                "%let a = %str(x;y)",
                "%let b = \"p;/*q*/\"",
                "D",
                "data d",
                "s = 'it''s;'",
            ]
        );
    }

    #[test]
    fn whitespace_and_comment_only_edits_are_not_content_changes() {
        for (old, new) in [
            ("data a; x=1; run;\n", "data a;\n  x=1;\nrun;\n"),
            ("data a; x=1; run;\n", "data   a;   x=1;   run;"),
            (
                "%macro greet(x=one);\n  %put &x;\n%mend;\n",
                "%macro greet(x=one); /* note */\n%put &x; %* why;\n%mend;\n",
            ),
            (
                "proc sort data=work.a out=work.b;\n  by id;\nrun;\n",
                "proc sort\n  data=work.a /* in */\n  out=work.b;\n* sort key;\n  by id;\nrun;\n",
            ),
        ] {
            let strip = |s: &str| -> Vec<(String, String)> {
                nodes(s).into_iter().map(|(t, l, _)| (t, l)).collect()
            };
            assert_eq!(strip(old), strip(new), "{old:?} vs {new:?}");
        }
    }

    #[test]
    fn steps_nest_in_macros_and_data_or_proc_implicitly_end_a_step() {
        let source = "%macro m;\n  proc print data=a;\n  run;\n  data b; x=1;\n%mend m;\nproc means data=b;\nproc print;\nrun cancel;\n%put done;\n";
        let tree = tree(source);
        let top = tree["children"].as_array().unwrap();
        let types: Vec<&str> = top
            .iter()
            .map(|n| n["node_type"].as_str().unwrap())
            .collect();
        assert_eq!(types, ["macro", "proc_step", "proc_step", "sas_statement"]);
        let inner: Vec<&str> = top[0]["children"]
            .as_array()
            .unwrap()
            .iter()
            .map(|n| n["node_type"].as_str().unwrap())
            .collect();
        assert_eq!(inner, ["sas_statement", "proc_step", "data_step"]);
        assert_eq!(top[0]["position"]["end_line"], 4);
        // A RUN with options alters behaviour, so it is retained.
        assert_eq!(top[2]["children"][1]["label"], "run cancel");
        assert_eq!(top[3]["label"], "%put done");
        let mut ids = std::collections::HashSet::new();
        let mut all = vec![&tree];
        while let Some(n) = all.pop() {
            assert!(
                ids.insert(n["id"].as_str().unwrap().to_string()),
                "duplicate id"
            );
            all.extend(n["children"].as_array().unwrap());
        }
        assert_eq!(parse_sas(source), parse_sas(source));
    }

    #[test]
    fn unterminated_trailing_text_is_preserved_not_dropped() {
        let a = nodes("data a; x=1; run;\n%greet()\n");
        let b = nodes("data a; x=1; run;\n%greet(y)\n");
        assert_eq!(a.last().unwrap().1, "%greet()");
        assert_eq!(b.last().unwrap().1, "%greet(y)");
        assert_eq!(a.last().unwrap().2, [1, 0, 1, 8]);
    }
}
