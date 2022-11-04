use serde::{Deserialize, Serialize};
use serde_json::{json, Result, Value};
use std::fs;
use std::fs::File;
use std::io::{self, BufRead, Write};
use std::path::Path;
use std::process;
use std::process::Command;
use std::str;

pub fn run_mythril(
    project_root_path_abs: &str,
    security_scan_path_rel: &str,
    contract_source_path_rel: &str,
    contract_name: &str,
    solc_version: &str,
    remappings: &Vec<String>,
) -> String {
    let mut remappings_formatted = "".to_owned();
    for r in remappings {
        remappings_formatted.push_str(format!("{r} ").as_str());
    }
    remappings_formatted = format!("'{remappings_formatted}'");

    let command = format!(
        "{project_root_path_abs}/{security_scan_path_rel}/mythril/run-mythril.sh {} {} {} {} {} {}",
        project_root_path_abs,
        security_scan_path_rel,
        contract_source_path_rel,
        contract_name,
        solc_version,
        remappings_formatted
    );

    let result = Command::new("sh")
        .arg("-c")
        .arg(command)
        .output()
        .expect("failed to execute process");

    let output = match str::from_utf8(&result.stdout) {
        Ok(v) => v,
        Err(e) => panic!("Invalid UTF-8 sequence: {}", e),
    };

    return output.to_string();
}

// Reverse engineerd from this:
//  https://github.com/ConsenSys/mythril/blob/21b3e92747f6b5ef1e22825756ba63f5b1c58621/mythril/analysis/report.py#L313

#[derive(Serialize, Deserialize)]
struct MythrilJsonV2 {
    issues: Vec<MythrilJsonV2Issue>,
    // TODO: Look further into the meta field
    meta: Value, //MythrilJsonV2Meta
    sourceFormat: String,
    sourceList: Value, //Vec<String>,
    sourceType: String,
}

// Issues
#[derive(Serialize, Deserialize)]
struct MythrilJsonV2Issue {
    description: MythrilJsonV2IssueDescriptions,
    extra: MythrilJsonV2IssueExtra,
    locations: Vec<MythrilJsonV2IssueLocations>,
    severity: String,
    swcID: String,
    swcTitle: String,
}

#[derive(Serialize, Deserialize)]
struct MythrilJsonV2IssueDescriptions {
    head: String,
    tail: String,
}

#[derive(Serialize, Deserialize)]
struct MythrilJsonV2IssueExtra {
    discoveryTime: i64,
    testCases: Vec<Value>,
}

#[derive(Serialize, Deserialize)]
struct MythrilJsonV2IssueLocations {
    sourceMap: String,
}

// Meta
#[derive(Serialize, Deserialize)]
struct MythrilJsonV2Meta {
    logs: Option<MythrilJsonV2MetaLogs>,
    mythril_execution_info: MythrilJsonV2MetaExecutionInfo,
}

#[derive(Serialize, Deserialize)]
struct MythrilJsonV2MetaLogs {
    level: String,
    hidden: bool,
    // Determine what msg really is https://github.com/ConsenSys/mythril/blob/21b3e92747f6b5ef1e22825756ba63f5b1c58621/mythril/analysis/report.py#L305
    msg: String,
}

#[derive(Serialize, Deserialize)]
struct MythrilJsonV2MetaExecutionInfo {
    analysis_duration: i32,
    execution_info: Value,
}

pub fn format_output_to_markdown(
    project_root_path_abs: &str,
    security_scan_path_rel: &str,
    contract_name: &str,
) -> Result<String> {
    let mythril_output_path =
        format!("{project_root_path_abs}/{security_scan_path_rel}/mythril/results/{contract_name}/{contract_name}-Mythril.result");

    let contents = fs::read_to_string(&mythril_output_path).expect(&format!(
        "Should have been able to read the file {mythril_output_path}"
    ));

    let mut mythril_jsonv2_string: String = "".to_string();
    if let Ok(lines) = read_lines(mythril_output_path) {
        let mythril_jsonv2_result = match lines.last() {
            Some(l) => l,
            _ => {
                println!("\nERROR: Could not get last line of mythril output\n");
                process::exit(1);
            }
        };

        match mythril_jsonv2_result {
            Ok(s) => mythril_jsonv2_string.push_str(rem_first_and_last(&s)),
            _ => {
                println!("\nERROR: Could not parse mythril jsonv2\n");
                process::exit(1);
            }
        };

        let result: MythrilJsonV2 = serde_json::from_str(&mythril_jsonv2_string)?;
    }

    return Ok(mythril_jsonv2_string.to_string());
}

fn read_lines<P>(filename: P) -> io::Result<io::Lines<io::BufReader<File>>>
where
    P: AsRef<Path>,
{
    let file = File::open(filename)?;
    Ok(io::BufReader::new(file).lines())
}

fn rem_first_and_last(value: &str) -> &str {
    let mut chars = value.chars();
    chars.next();
    chars.next_back();
    chars.as_str()
}
