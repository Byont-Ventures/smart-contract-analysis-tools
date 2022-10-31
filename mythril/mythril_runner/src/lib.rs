use std::process::Command;
use std::str;

pub fn run_mythril(
    project_root_path_abs: &str,
    security_scan_path_rel: &str,
    contract_source_path_rel: &str,
    contract_name: &str,
) -> String {
    // TODO: see if sudo can be removed
    let command = format!(
        "sudo {project_root_path_abs}/{security_scan_path_rel}/mythril/run-mythril.sh {} {} {} {}",
        project_root_path_abs, security_scan_path_rel, contract_source_path_rel, contract_name
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
