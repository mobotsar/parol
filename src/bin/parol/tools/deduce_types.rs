use std::convert::TryInto;
use parol::transformation::ast_types::GrammarTypeSystem;
use miette::Result;
use parol::{left_factor, obtain_grammar_config};

pub fn sub_command() -> clap::App<'static, 'static> {
    clap::SubCommand::with_name("deduce_types")
        .about("Calculates the type structure of the generated expanded grammar.")
        .arg(
            clap::Arg::with_name("grammar_file")
                .required(true)
                .short("f")
                .long("grammar-file")
                .takes_value(true)
                .help("The grammar file to use")
        )
}

pub fn main(args: &clap::ArgMatches) -> Result<()> {
    let file_name = args
        .value_of("grammar_file")
        .unwrap();

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
