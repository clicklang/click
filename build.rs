//! Embeds the "Using Click" part of the AI reference for `click docs`, so an
//! installed binary documents its own version without the repository.
use std::env;
use std::fs;
use std::path::Path;

fn main() {
    let manifest = env::var("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR");
    let docs = Path::new(&manifest).join("docs");
    let summary_path = docs.join("SUMMARY.md");
    println!("cargo:rerun-if-changed={}", summary_path.display());
    let summary = fs::read_to_string(&summary_path).expect("read docs/SUMMARY.md");
    let using = summary
        .split("# Using Click")
        .nth(1)
        .and_then(|rest| rest.split("# Developing Click").next())
        .expect("docs/SUMMARY.md has a Using Click part");
    let mut pages = String::from("pub(crate) static PAGES: &[(&str, &str)] = &[\n");
    for line in using.lines() {
        let Some(path) = line
            .split("](")
            .nth(1)
            .and_then(|rest| rest.split(')').next())
            .filter(|path| path.ends_with(".md"))
        else {
            continue;
        };
        let file = docs.join(path);
        println!("cargo:rerun-if-changed={}", file.display());
        pages.push_str(&format!(
            "    ({path:?}, include_str!({:?})),\n",
            file.display().to_string()
        ));
    }
    pages.push_str("];\n");
    let out = Path::new(&env::var("OUT_DIR").expect("OUT_DIR")).join("docs_pages.rs");
    fs::write(out, pages).expect("write docs_pages.rs");
}
