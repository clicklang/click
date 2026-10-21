//! `click docs`: the documentation compiled into this binary.

const USAGE: &str = "usage: click docs [<NAME>]\n\nPrints the documentation for a tactic, such as `normalize`, or a topic, such as `tracing`; with no name, lists every name.";

pub(crate) fn entry_with(arguments: impl IntoIterator<Item = String>) -> Result<(), String> {
    let arguments = arguments.into_iter().collect::<Vec<_>>();
    match arguments.as_slice() {
        [] => {
            print!("{}", click::docs::index());
            Ok(())
        }
        [argument] if argument == "-h" || argument == "--help" => {
            println!("{USAGE}");
            Ok(())
        }
        [name] => {
            print!("{}", click::docs::lookup(name)?);
            Ok(())
        }
        _ => Err(format!("expected at most one name\n{USAGE}")),
    }
}
