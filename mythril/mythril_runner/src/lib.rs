use serde::{Deserialize, Serialize};
use serde_json::{json, Result, Value};
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

    // TODO: see if sudo can be removed
    let command = format!(
        "sudo {project_root_path_abs}/{security_scan_path_rel}/mythril/run-mythril.sh {} {} {} {} {} {}",
        project_root_path_abs, security_scan_path_rel, contract_source_path_rel, contract_name, solc_version, remappings_formatted
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
struct MythrilJsonV2Top {
    JSON: Vec<MythrilJsonV2>,
}

#[derive(Serialize, Deserialize)]
struct MythrilJsonV2 {
    issues: Vec<MythrilJsonV2Issue?,
    sourceType: String,
    sourceFormat: String,
    sourceList: Vec<String>,
    // TODO: Look further into the meta field
    meta: MythrilJsonV2Meta,
}

// Issues
#[derive(Serialize, Deserialize)]
struct MythrilJsonV2Issue {
    description: MythrilJsonV2IssueDescriptions,
    extra: MythrilJsonV2OIssueExtra,
    locations: Vec<MythrilJsonV2IssueLocations>,
    severity: String,
    swsID: String,
    swsTitle: String,
}

#[derive(Serialize, Deserialize)]
struct MythrilJsonV2IssueDescriptions {
    head: String,
    tail: String,
}

#[derive(Serialize, Deserialize)]
struct MythrilJsonV2IssueExtra {
    discoveryTime: i32,
    testCases: Option<Vec<Value>>,
}

#[derive(Serialize, Deserialize)]
struct MythrilJsonV2IssueLocations {
    sourceMap: String,
}

// Meta
#[derive(Serialize, Deserialize)]
struct MythrilJsonV2Meta {
    logs: Options<MythrilJsonV2MetaLogs>,
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
    execution_info: Value
}

pub fn format_output_to_markdown(
    project_root_path_abs: &str,
    security_scan_path_rel: &str,
    contract_name: &str,
) -> Result<String> {
    let slither_json_path =
        format!("{project_root_path_abs}/{security_scan_path_rel}/slither/results/{contract_name}/{contract_name}-output.json");

    let contents =
        fs::read_to_string(&slither_json_path).expect("Should have been able to read the file");

    let result: SlitherOutput = serde_json::from_str(&contents)?;

    if !result.success {
        println!("\nERROR: Slither had an error while running!\nSee {slither_json_path} for more info.\n");
        process::exit(1);
    }