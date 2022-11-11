use serde::Deserialize;
use serde::Serialize;
use std::fs;
use std::error::Error;

#[derive(Default, Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Data {
    pub repository_link: String,
    pub commit: String,
    pub contract_path: String,
    pub solc_version: String,
    pub foundry_version: String,
    pub slither_version: String,
    pub mythrill_version: String,
    pub smtchecker_version: String,
    pub tools: Vec<Tool>,
    pub compiled_code_size: String,
    pub notes: String,
    #[serde(rename = "vulnerabilitiesPerSWC")]
    pub vulnerabilities_per_swc: i64,
    pub problems: Vec<Problem>,
}

#[derive(Default, Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Tool {
    pub name: String,
    pub nr_of_issues: i64,
    pub version: String,
    pub has_detectors: bool,
    pub detectors: Option<Vec<Detector>>,
}

#[derive(Default, Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Detector {
    pub name: String,
    pub impact: String,
    pub confidence: String,
    pub function: String,
    pub lines_of_relevance: Vec<String>,
}

#[derive(Default, Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Problem {
    pub line_numbers_of_interest: Vec<i64>,
    pub severity: String,
    pub rarity: String,
    pub swc_id: i64,
    pub transaction_flow: String,
    pub notes: String,
}

// May add a bit more proper error-handling if the library expands

pub fn read_json(path: &str) -> Result<Data, Box<dyn Error>> {
    let file = fs::read_to_string(path)?;

    let data: Data = serde_json::from_str(&file)?;

    Ok(data)
}