use serde_derive::Deserialize;
use std::env;
use std::fs;
use std::fs::File;
use std::io::prelude::*;
use std::process;

// Import the different tools
use mythril_runner as mythril;
use slither_runner as slither;
use smtchecker_runner as smtchecker;

#[derive(Debug, Deserialize)]
struct Config {
    environment: ConfigEnvironment,
    report: ConfigReport,
    mythril: ConfigMythril,
    slither: ConfigSlither,
    smtchecker: ConfigSmtchecker,
}

#[derive(Debug, Deserialize)]
struct ConfigEnvironment {
    project_root: String,
    security_scans_rel_path: String,
    source_rel_path: String,
    remappings: Option<Vec<String>>,
    solc_version: Option<String>,
}

#[derive(Debug, Deserialize)]
struct ConfigReport {
    report_output_rel_path: String,
    contract: Vec<ConfigReportConfig>,
}

#[derive(Debug, Deserialize)]
struct ConfigReportConfig {
    name: String,
    report_custom_name: Option<String>,
}

#[derive(Debug, Deserialize)]
struct ConfigMythril {
    enabled: bool,
}

#[derive(Debug, Deserialize)]
struct ConfigSlither {
    enabled: bool,
}

#[derive(Debug, Deserialize)]
struct ConfigSmtchecker {
    enabled: bool,
}

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() <= 1 {
        println!("\nERROR: Please provide the required config file!\n");
        process::exit(1);
    }

    let config_path = &args[1];
    let config_str = fs::read_to_string(&config_path)
        .expect(&format!("ERROR: Cannot read config file at {config_path}"));

    let config: Config = match toml::from_str(&config_str) {
        Ok(c) => c,
        _ => {
            println!("{}", format!("\nERROR: Cannot parse config {config_str}\n"));
            process::exit(1);
        }
    };

    println!("{:#?}", config);

    // let filePath =
    //     format!("{project_root_path_abs}/{report_output_path_rel}/{contract_name}/report-{contract_name}.md");
    // let mut file = match create_file(&filePath) {
    //     Ok(f) => f,
    //     _ => {
    //         println!("\nERROR: Failed to create file: {}\n", filePath);
    //         process::exit(1);
    //     }
    // };

    // let main_header = "# Code report\n\n";
    // write_to_report(&mut file, &main_header);

    // //---------------
    // // Slither
    // //---------------

    // let slither_header = "## Slither\n\n";
    // write_to_report(&mut file, &slither_header);

    // let slither_result = slither::run_slither(
    //     project_root_path_abs,
    //     security_scan_path_rel,
    //     contract_source_path_rel,
    //     contract_name,
    // );

    // let slither_markdown_content = match slither::format_output_to_markdown(
    //     project_root_path_abs,
    //     security_scan_path_rel,
    //     contract_name,
    // ) {
    //     Ok(s) => s,
    //     _ => "".to_string(),
    // };

    // write_to_report(&mut file, &slither_markdown_content);

    // //---------------
    // // SMTChecker
    // //---------------

    // let smtchecker_header = "## SMTChecker\n\n";
    // write_to_report(&mut file, &smtchecker_header);

    // let smtchecker_result = smtchecker::run_smtchecker(
    //     project_root_path_abs,
    //     security_scan_path_rel,
    //     contract_source_path_rel,
    //     contract_name,
    // );

    // write_to_report(&mut file, &smtchecker_result.replace("\n", "\n\n"));

    // //---------------
    // // Mythril
    // //---------------

    // let mythril_header = "## Mythril\n\n";
    // write_to_report(&mut file, &mythril_header);

    // let mythril_result = mythril::run_mythril(
    //     project_root_path_abs,
    //     security_scan_path_rel,
    //     contract_source_path_rel,
    //     contract_name,
    // );

    // write_to_report(&mut file, &mythril_result.replace("\n", "\n\n"));
}

fn create_file(file_name: &str) -> std::io::Result<File> {
    let file = File::create(file_name)?;
    return Ok(file);
}

fn write_to_report(file: &mut File, content: &str) -> std::io::Result<()> {
    file.write_all(content.as_bytes())?;
    Ok(())
}
