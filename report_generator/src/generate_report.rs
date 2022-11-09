use tera::Tera;
use tera::Context;
use std::fs;
use lazy_static::lazy_static;

use crate::read_json::Data;

lazy_static! {
        pub static ref TEMPLATES: Tera = {
            let mut tera = match Tera::new("templates/*") {
                Ok(t) => t,
                Err(e) => {
                    println!("Parsing error(s): {}", e);
                    ::std::process::exit(1);
                }
            };
            tera.autoescape_on(vec![".html", ".sql"]);
            // tera.register_filter("do_nothing", do_nothing_filter);
            tera
        };
    }

pub fn generate_reports(data: Data) {
    // let names: Vec<_> = TEMPLATES.get_template_names().collect();
    //
    // for i in names.iter() {
    //     println!("{}", i);
    // }

    let mut context = Context::new();

    context.insert("data", &data);

    let doc = TEMPLATES.render("full_report_template.md", &context).unwrap();

    fs::write("outputs/full_report.md", doc)
        .expect("SOMETHING WENT WRONG!");
}