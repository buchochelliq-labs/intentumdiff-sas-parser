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
// Node helpers
// ---------------------------------------------------------------------------

fn block_node(id: &str, node_type: &str, label: &str, start: u32, end: u32) -> SemanticNode {
    SemanticNodeBuilder::new(id, node_type, label, start, 0, end, 0, String::new()).build()
}

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

struct Step {
    statements: Vec<SemanticNode>,
    id: String,
    node_type: &'static str,
    label: String,
    start_line: u32,
}

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

pub(crate) fn parse_sas(source: &str) -> String {
    let uncommented = match without_comments(source) {
        Ok(text) => text,
        Err(error) => return serde_json::json!({"error": error}).to_string(),
    };
    let source = uncommented.as_str();
    let mut children: Vec<SemanticNode> = Vec::new();
    let mut counter: usize = 0;
    let mut current: Option<Step> = None;
    let total_lines = source.lines().count().saturating_sub(1) as u32;

    let close_current =
        |current: &mut Option<Step>, children: &mut Vec<SemanticNode>, end_line: u32| {
            if let Some(step) = current.take() {
                let mut block = block_node(
                    &step.id,
                    step.node_type,
                    &step.label,
                    step.start_line,
                    end_line,
                );
                block.children = step.statements;
                children.push(block);
            }
        };

    for (idx, raw_line) in source.lines().enumerate() {
        let lineno = idx as u32;
        let trimmed = raw_line.trim();
        if trimmed.is_empty() || trimmed.starts_with('*') {
            continue;
        }

        let upper = trimmed.to_uppercase();
        let words: Vec<&str> = upper.split_whitespace().collect();
        if words.is_empty() {
            continue;
        }

        // %MACRO opens a macro block
        if words[0] == "%MACRO" {
            close_current(&mut current, &mut children, lineno.saturating_sub(1));
            let name = words
                .get(1)
                .copied()
                .unwrap_or("(anonymous)")
                .split('(')
                .next()
                .unwrap_or("(anonymous)")
                .to_string();
            let id = format!("0.{}", counter);
            counter += 1;
            current = Some(Step {
                statements: Vec::new(),
                id,
                node_type: "macro",
                label: name,
                start_line: lineno,
            });
            continue;
        }

        // %MEND closes a macro block
        if words[0] == "%MEND" {
            close_current(&mut current, &mut children, lineno);
            continue;
        }

        // DATA opens a data step
        if words[0] == "DATA" && current.is_none() {
            let name = words
                .get(1)
                .copied()
                .unwrap_or("(anonymous)")
                .trim_end_matches(';')
                .to_string();
            let id = format!("0.{}", counter);
            counter += 1;
            current = Some(Step {
                statements: Vec::new(),
                id,
                node_type: "data_step",
                label: name,
                start_line: lineno,
            });
            continue;
        }

        // PROC opens a proc step
        if words[0] == "PROC" && current.is_none() && words.len() >= 2 {
            let proc_name = words[1].to_string();
            // Look for DATA=<name>
            let data_arg = upper
                .split_whitespace()
                .find(|w| w.starts_with("DATA="))
                .map(|w| w.trim_end_matches(';').to_string());
            let label = if let Some(d) = data_arg {
                let ds = d.trim_start_matches("DATA=");
                format!("{} (DATA={})", proc_name, ds)
            } else {
                proc_name
            };
            let id = format!("0.{}", counter);
            counter += 1;
            current = Some(Step {
                statements: Vec::new(),
                id,
                node_type: "proc_step",
                label,
                start_line: lineno,
            });
            continue;
        }

        // RUN; or QUIT; closes the current step
        if words[0] == "RUN;" || words[0] == "RUN" || words[0] == "QUIT;" || words[0] == "QUIT" {
            close_current(&mut current, &mut children, lineno);
            continue;
        }

        // #46: interior statement lines are review content — carry them as children so a
        // value edit inside a step (`attempts = 4;` -> `5`) surfaces instead of vanishing.
        if let Some(step) = current.as_mut() {
            let stmt = trimmed.trim_end_matches(';').trim();
            if !stmt.is_empty() {
                let id = format!("{}.{}", step.id, step.statements.len());
                step.statements
                    .push(block_node(&id, "sas_statement", stmt, lineno, lineno));
            }
        } else {
            // Global statements (notably %LET) affect later steps too. Dropping
            // them makes value edits indistinguishable from unchanged source.
            let stmt = trimmed.trim_end_matches(';').trim();
            if !stmt.is_empty() {
                let id = format!("0.{}", counter);
                counter += 1;
                let start_col = raw_line.len() - raw_line.trim_start().len();
                children.push(
                    SemanticNodeBuilder::new(
                        &id,
                        "sas_statement",
                        stmt,
                        lineno,
                        start_col as u32,
                        lineno,
                        (start_col + trimmed.len()) as u32,
                        String::new(),
                    )
                    .build(),
                );
            }
        }
    }

    // Drain unclosed step
    close_current(&mut current, &mut children, total_lines);

    let root = SemanticNodeBuilder::new(
        "0",
        "sas_program",
        "sas_program",
        0,
        0,
        total_lines,
        0,
        String::new(),
    )
    .children(children)
    .build();

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
            new["children"][1]["children"][0]["label"],
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
}
