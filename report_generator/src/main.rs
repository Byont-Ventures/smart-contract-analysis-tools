use serde_derive::Deserialize;
use std::env;
use std::fs;
use std::fs::File;
use std::io::prelude::*;
use std::path::Path;
use std::path::PathBuf;
use std::process;

// Import the different tools
use mythril_runner as mythril;
use slither_runner as slither;
use smtchecker_runner as smtchecker;

#[derive(Deserialize)]
struct Config {
    environment: ConfigEnvironment,
    report: ConfigReport,
    mythril: ConfigMythril,
    slither: ConfigSlither,
    smtchecker: ConfigSmtchecker,
}

#[derive(Deserialize)]
struct ConfigEnvironment {
    security_scans_rel_path: String,
    source_rel_path: String,
    remappings: Vec<String>,
    solc_version: String,
}

#[derive(Deserialize)]
struct ConfigReport {
    report_output_rel_path: String,
    contract: Vec<ConfigReportConfig>,
}

#[derive(Deserialize)]
struct ConfigReportConfig {
    name: String,
    report_custom_name: Option<String>,
}

#[derive(Deserialize)]
struct ConfigMythril {
    enabled: bool,
}

#[derive(Deserialize)]
struct ConfigSlither {
    enabled: bool,
}

#[derive(Deserialize)]
struct ConfigSmtchecker {
    enabled: bool,
}

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() <= 1 {
        println!("\nERROR: Please provide the required config file!\n");
        process::exit(1);
    }

    let base_root_abs = &args[1];
    let project_root_rel_base = &args[2];
    let config_path = &args[3];

    let config_str = fs::read_to_string(&config_path)
        .expect(&format!("ERROR: Cannot read config file at {config_path}"));

    let config: Config = match toml::from_str(&config_str) {
        Ok(c) => c,
        _ => {
            println!("{}", format!("\nERROR: Cannot parse config {config_str}\n"));
            process::exit(1);
        }
    };

    let mut project_root_path_abs_pathbuf = PathBuf::from(base_root_abs);
    project_root_path_abs_pathbuf.push(project_root_rel_base);
    let project_root_path_abs = match project_root_path_abs_pathbuf.to_str() {
        Some(s) => s,
        _ => {
            println!("{}", format!("\nERROR: Converting root path to string\n"));
            process::exit(1);
        }
    };

    let report_rel_path: String = config.report.report_output_rel_path;
    let security_scan_path_rel_from_project: String = config.environment.security_scans_rel_path;
    let contract_source_path_rel_from_project: String = config.environment.source_rel_path;

    for contract in config.report.contract {
        let contract_name = contract.name;
        let contract_report_extra_name = match contract.report_custom_name {
            Some(s) => s,
            _ => "".to_string(),
        };

        let filePath =
        format!("{project_root_path_abs}/{report_rel_path}/{contract_name}/report-{contract_name}{contract_report_extra_name}.md");
        let mut file = match create_file(&filePath) {
            Ok(f) => f,
            _ => {
                println!("\nERROR: Failed to create file: {}\n", filePath);
                process::exit(1);
            }
        };

        let main_header = "# Code report\n\n";
        write_to_report(&mut file, &main_header);

        //---------------
        // Slither
        //---------------
        if config.slither.enabled {
            let slither_header = "## Slither\n\n";
            write_to_report(&mut file, &slither_header);

            let slither_result = slither::run_slither(
                &base_root_abs,
                &project_root_rel_base,
                &security_scan_path_rel_from_project,
                &contract_source_path_rel_from_project,
                &contract_name,
                &config.environment.solc_version,
                &config.environment.remappings,
            );

            let slither_markdown_content = match slither::format_output_to_markdown(
                &base_root_abs,
                &project_root_path_abs,
                &security_scan_path_rel_from_project,
                &contract_name,
            ) {
                Ok(s) => s,
                _ => "".to_string(),
            };

            write_to_report(&mut file, &slither_markdown_content);
        }

        // //---------------
        // // SMTChecker
        // //---------------
        // if config.smtchecker.enabled {
        //     let smtchecker_header = "## SMTChecker\n\n";
        //     write_to_report(&mut file, &smtchecker_header);

        //     let smtchecker_result = smtchecker::run_smtchecker(
        //         &project_root_path_abs,
        //         &security_scan_path_rel,
        //         &contract_source_path_rel,
        //         &contract_name,
        //         &config.environment.solc_version,
        //         &config.environment.remappings,
        //     );

        //     write_to_report(&mut file, &smtchecker_result.replace("\n", "\n\n"));
        // }

        // //---------------
        // // Mythril
        // //---------------
        // if config.mythril.enabled {
        //     let mythril_header = "## Mythril\n\n";
        //     write_to_report(&mut file, &mythril_header);

        //     let mythril_result = mythril::run_mythril(
        //         &project_root_path_abs,
        //         &security_scan_path_rel,
        //         &contract_source_path_rel,
        //         &contract_name,
        //         &config.environment.solc_version,
        //         &config.environment.remappings,
        //     );

        //     let mythril_markdown_content = match mythril::format_output_to_markdown(
        //         &project_root_path_abs,
        //         &security_scan_path_rel,
        //         &contract_name,
        //     ) {
        //         Ok(s) => s,
        //         _ => "".to_string(),
        //     };

        //     write_to_report(&mut file, &mythril_markdown_content.replace("\n", "\n\n"));
        // }
    }
}

fn create_file(file_name: &str) -> std::io::Result<File> {
    let pathOfReport = match Path::new(file_name).parent() {
        Some(p) => p,
        _ => {
            println!(
                "{}",
                format!("\nERROR: Could not get parent path {file_name}!\n")
            );
            process::exit(1);
        }
    };
    fs::create_dir_all(pathOfReport)?;
    let file = File::create(file_name)?;
    return Ok(file);
}

fn write_to_report(file: &mut File, content: &str) -> std::io::Result<()> {
    file.write_all(content.as_bytes())?;
    Ok(())
}
