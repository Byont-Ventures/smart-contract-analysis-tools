## About
This repository is made for generating reports about smart contract analysis. This product was created for Byont Labs. The repository can still be changed, but at this moment it works as it is supposed to.

## Structure
Aside from usual folders and files for a Rust project, the project has "outputs" and "templates" folders and "input.json" file, as well as files in "src" folder that are worth mentioning.

### Outputs folder
This folder contains all the reports generated after running the program. At the moment the program will generate only one file, "full_report.md", as an output in the "outputs" folder, but that may be changed later.

### Templates folder
The template folder consists of templates used for generation reports. It has one initial template, "full_report_template.md", and three "macros". Macros are special Tera-specific templates that can be reused inside other templates and where you can pass values from parent-templates. You can learn more about macros in the [Tera documents](https://tera.netlify.app/docs/#macros)

### Input.json
"input.json" is a file that is used as an input for generating a report. Its content is similar to what will be in the final version, but the document will be eventually changed according to the data that Byont would like to see in their reports.

### Src folder
"src" folder contains the main executive files:
* "main.rs" is a binary crate that runs the project. It makes use of "read_json.rs" and "generate_report.rs" libraries and executes the code.
* "read_json.rs" is a library crate responsible for reading an input file and converting it into Data struct.
* "generate_report.rs" is a library crate that generates reports using templates from "templates" folder and a variable of Data type.

## Code example
To run the program, after downloading the repository, enter next line in the terminal: `cargo run`
It will create a "full_report.md" file in the "outputs" folder or rewrite the existing one.
If there are any mistakes the terminal will show the corresponding message.