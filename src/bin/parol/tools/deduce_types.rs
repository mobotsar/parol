use std::convert::TryInto;
use std::path::PathBuf;
use parol::transformation::ast_types::GrammarTypeSystem;
use miette::Result;
use parol::{left_factor, obtain_grammar_config};

/// Calculates the type structure of the generated expanded grammar.
#[derive(clap::Parser)]
#[clap(name = "deduce_types")]
pub struct Args {
    /// The grammar file to use
    #[clap(short = 'f', long = "grammar-file", parse(from_os_str))]
    grammar_file: PathBuf,
}

pub fn main(args: &Args) -> Result<()> {
    let file_name = &args.grammar_file;

    let mut grammar_config = obtain_grammar_config(&file_name, false)?;
    let cfg = left_factor(&grammar_config.cfg);
    // Exchange original grammar with transformed one
    grammar_config.update_cfg(cfg);

    let width = (grammar_config.cfg.pr.len() as f32).log10() as usize + 1;
    let type_system: GrammarTypeSystem = (&grammar_config.cfg).try_into().unwrap();
    for (i, pr) in grammar_config.cfg.pr.iter().enumerate() {
        println!("/* {:w$} */ {}", i, pr, w = width);
    }
    println!();
    println!("Type information:");
    println!("{}", type_system);
    Ok(())
}
