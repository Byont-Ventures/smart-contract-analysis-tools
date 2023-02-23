use serde::{Deserialize, Serialize};
use serde_json::{json, Result, Value};
use std::any::type_name;
use std::fs;
use std::fs::File;
use std::io::{self, BufRead, Write};
use std::path::Path;
use std::process;
use std::process::Command;
use std::str;

fn type_of<T>(_: T) -> &'static str {
    type_name::<T>()
}

#[derive(Serialize, Deserialize)]
struct SlitherConfig {
    filter_paths: String,
    solc_remaps: Vec<String>,
    printers_to_run: String,
    detectors_to_run: String,
}

pub fn run_slither(
    base_root: &str,
    project_root_path_rel_base: &str,
    security_scan_path_rel_project: &str,
    contract_source_path_rel_project: &str,
    contract_name: &str,
    solc_version: &str,
    remappings: &Vec<String>,
) -> String {
    let slither_config_path =
        format!("{base_root}/{project_root_path_rel_base}/{security_scan_path_rel_project}/slither/slither.config.json");

    let slither_config = fs::read_to_string(&slither_config_path)
        .expect(&format!("ERROR: Cannot read {slither_config_path}!"));

    let mut config: SlitherConfig = match serde_json::from_str(&slither_config) {
        Ok(c) => c,
        _ => {
            println!("\nERROR: Error parsing slither.config.json {slither_config}\n");
            process::exit(1);
        }
    };

    config.solc_remaps = remappings.to_vec();

    let mut file = match File::create(&slither_config_path) {
        Ok(f) => f,
        _ => {
            println!("\nERROR: Cannot open {slither_config_path}\n");
            process::exit(1);
        }
    };

    let json_string = json!(config).to_string();
    file.write_all(json_string.as_bytes());

    let command = format!(
        "{base_root}/{project_root_path_rel_base}/{security_scan_path_rel_project}/slither/run-slither.sh {} {} {} {} {}",
        base_root,
        format!("{project_root_path_rel_base}/{security_scan_path_rel_project}"),
        format!("{project_root_path_rel_base}/{contract_source_path_rel_project}"),
        contract_name,
        solc_version
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

// For Slither v0.9.0
// https://github.com/crytic/slither/tree/0.9.0
#[derive(Serialize, Deserialize)]
struct SlitherOutput {
    success: bool,
    error: Value,
    results: Value,
}

#[derive(Serialize, Deserialize)]
struct SlitherOutputHumanSummary {
    elements: Value,
    description: String,
    markdown: String,
    first_markdown_element: String,
    id: String,
    additional_fields: SlitherOutputHumanSummaryAdditionalFields,
    printer: String,
}

#[derive(Serialize, Deserialize)]
struct SlitherOutputHumanSummaryAdditionalFields {
    contracts: Value,
    number_lines: i32,
    number_lines_in_dependencies: i32,
    number_lines_assembly: i32,
    standard_libraries: Value,
    ercs: Vec<String>,
    number_findings: Value,
    detectors: Vec<SlitherOutputHumanSummaryAdditionalFieldsDetectors>,
    number_lines__dependencies: i32,
}

#[derive(Serialize, Deserialize)]
struct SlitherOutputHumanSummaryAdditionalFieldsDetectors {
    elements: Value,
    description: String,
    markdown: String,
    first_markdown_element: String,
    id: String,
    check: String,
    impact: String,
    confidence: String,
}

#[derive(Serialize, Deserialize)]
struct SlitherOutputHumanSummaryAdditionalFieldsDetectorsNonSolcVersionCheck {
    elements: Vec<SlitherOutputHumanSummaryAdditionalFieldsDetectorsElements>,
}

#[derive(Serialize, Deserialize)]
struct SlitherOutputHumanSummaryAdditionalFieldsDetectorsElements {
    r#type: String,
    name: String,
    source_mapping: SlitherOutputHumanSummaryAdditionalFieldsDetectorsElementsSourceMapping,
    type_specific_fields: Value,
}

#[derive(Serialize, Deserialize)]
struct SlitherOutputHumanSummaryAdditionalFieldsDetectorsElementsSourceMapping {
    start: i32,
    length: i32,
    filename_relative: String,
    filename_absolute: String,
    filename_short: String,
    is_dependency: bool,
    lines: Vec<i32>,
    starting_column: i32,
    ending_column: i32,
}

#[derive(Serialize, Deserialize)]
struct SlitherOutputHumanSummaryAdditionalFieldsTypePragma {}

#[derive(Serialize, Deserialize)]
struct SlitherOutputHumanSummaryAdditionalFieldsTypeContract {}

#[derive(Serialize, Deserialize)]
struct SlitherOutputHumanSummaryAdditionalFieldsTypeFunction {}

#[derive(Serialize, Deserialize)]
struct SlitherOutputHumanSummaryAdditionalFieldsTypeNode {}

// Out of date: https://github.com/crytic/slither/wiki/JSON-output
pub fn format_output_to_markdown(
    base_path_abs: &str,
    project_root_path_abs: &str,
    security_scan_path_rel: &str,
    contract_name: &str,
) -> Result<String> {
    let slither_json_path =
        format!("{project_root_path_abs}/{security_scan_path_rel}/slither/results/{contract_name}/{contract_name}-output.json");

    println!("{}", slither_json_path);

    let contents =
        fs::read_to_string(&slither_json_path).expect("Should have been able to read the file");

    let result: SlitherOutput = serde_json::from_str(&contents)?;

    if !result.success {
        println!("\nERROR: Slither had an error while running!\nSee {slither_json_path} for more info.\n");
        process::exit(1);
    }

    let mut slither_markdown = "".to_owned();

    let printers = &result.results["printers"];

    let printer_count = 1; // printers.len()
    for i in 0..printer_count {
        let current_printer = match printers[i]["printer"].as_str() {
            Some(s) => s,
            _ => "",
        };

        match current_printer {
            "human-summary" => {
                let tmp_string = serde_json::to_string(&printers[i])?;

                let human_summary_result: SlitherOutputHumanSummary =
                    serde_json::from_str(&*tmp_string)?;

                let human_summary_content = match format_printer_markdown_human_summary(
                    base_path_abs,
                    human_summary_result,
                ) {
                    Ok(s) => s,
                    _ => {
                        println!("\nERROR: Error while parsing {tmp_string}\n");
                        process::exit(1);
                    }
                };

                slither_markdown.push_str(&human_summary_content);
            }
            _ => println!("Printer ({}) not supported", current_printer),
        }
    }

    return Ok(slither_markdown);
}

fn format_printer_markdown_human_summary(
    base_path_abs: &str,
    json_data: SlitherOutputHumanSummary,
) -> Result<String> {
    let mut content = format!("{}\n", json_data.description.replace("\n", "\n\n"));
    content.push_str("\nFor more information about the detected items see the [Slither documentation](https://github.com/crytic/slither/wiki/Detector-Documentation).\n\n");

    let detector_items = json_data.additional_fields.detectors;

    for d in detector_items.iter() {
        content.push_str(&format!("\n### {}\n\n", d.check));
        content.push_str(&format!("- Impact: `{}`\n", d.impact));
        content.push_str(&format!("- Confidence: `{}`\n", d.confidence));
        content.push_str("\n");

        if d.elements != serde_json::Value::Null && d.elements[0]["type"] != "contract" {
            let tmp_string = serde_json::to_string(&d)?;
            let detector_elements: SlitherOutputHumanSummaryAdditionalFieldsDetectorsNonSolcVersionCheck =
                serde_json::from_str(&*tmp_string)?;

            for e in detector_elements.elements.iter() {
                let relative_path = &e.source_mapping.filename_relative;
                let source_path = format!("{base_path_abs}/{relative_path}");

                if e.r#type == "function" {
                    content.push_str("\n**In Function**\n");
                } else if e.r#type == "node" {
                    content.push_str("\n**Lines of relevance**\n");
                }

                let mut mappedSourceLineIndex = 0;

                content.push_str("\n```Solidity\n");
                content.push_str(&format!("// {relative_path}\n\n"));
                if let Ok(source_lines) = read_lines(source_path) {
                    // Consumes the iterator, returns an (Optional) String
                    let mut line_number = 1;
                    for line in source_lines {
                        if let Ok(source_line) = line {
                            if line_number == e.source_mapping.lines[mappedSourceLineIndex] {
                                content.push_str(&format!("{line_number} {}\n", source_line));
                                mappedSourceLineIndex += 1;
                                if mappedSourceLineIndex == e.source_mapping.lines.len() {
                                    break;
                                }
                            }
                        }
                        line_number += 1;
                    }
                }
                content.push_str("```\n");

                // TODO: read lines e.source_mapping.lines from prj_root_path/e.source_mapping.filename_relative
                //
            }
        }
    }

    return Ok(content);
}

// Source:  https://doc.rust-lang.org/rust-by-example/std_misc/file/read_lines.html
// The output is wrapped in a Result to allow matching on errors
// Returns an Iterator to the Reader of the lines of the file.
fn read_lines<P>(filename: P) -> io::Result<io::Lines<io::BufReader<File>>>
where
    P: AsRef<Path>,
{
    let file = File::open(filename)?;
    Ok(io::BufReader::new(file).lines())
}
