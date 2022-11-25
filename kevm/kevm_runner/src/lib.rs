// use std::process::Command;
// use std::str;

// pub fn run_kevm(
//     project_root_path_abs: &str,
//     security_scan_path_rel: &str,
//     contract_source_path_rel: &str,
//     contract_name: &str,
//     solc_version: &str,
// ) -> String {
//     let mut remappings_formatted = "".to_owned();
//     for r in remappings {
//         remappings_formatted.push_str(format!("{r} ").as_str());
//     }
//     remappings_formatted = format!("'{remappings_formatted}'");

//     let command = format!(
//         "{project_root_path_abs}/{security_scan_path_rel}/SMTChecker/run-SMTChecker.sh {} {} {} {} {} {}",
//         project_root_path_abs, security_scan_path_rel, contract_source_path_rel, contract_name, solc_version, remappings_formatted
//     );

//     let result = Command::new("sh")
//         .arg("-c")
//         .arg(command)
//         .output()
//         .expect("failed to execute process");

//     let output = match str::from_utf8(&result.stdout) {
//         Ok(v) => v,
//         Err(e) => panic!("Invalid UTF-8 sequence: {}", e),
//     };

//     return output.to_string();
// }
