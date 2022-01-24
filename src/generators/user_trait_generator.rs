use crate::generators::{generate_terminal_name, GrammarConfig};
use crate::transformation::ast_types::{ASTType, GrammarTypeSystem};
use crate::{Pr, StrVec, Symbol, Terminal};
use miette::Result;
use std::convert::TryInto;

#[derive(BartDisplay, Debug, Default)]
#[template = "templates/user_trait_caller_function_template.rs"]
struct UserTraitCallerFunctionData {
    fn_name: String,
    prod_num: usize,
    fn_arguments: String,
}

#[derive(BartDisplay, Debug, Default)]
#[template = "templates/user_trait_function_template.rs"]
struct UserTraitFunctionData {
    fn_name: String,
    prod_num: usize,
    fn_arguments: String,
    prod_string: String,
}

#[derive(BartDisplay, Debug, Default)]
#[template = "templates/user_trait_template.rs"]
struct UserTraitData<'a> {
    user_type_name: &'a str,
    production_output_types: StrVec,
    non_terminal_types: StrVec,
    trait_functions: StrVec,
    trait_caller: StrVec,
    user_trait_module_name: &'a str,
}

#[derive(BartDisplay, Debug, Default)]
#[template = "templates/non_terminal_type_struct_template.rs"]
struct NonTerminalTypeStruct {
    comment: String,
    non_terminal: String,
    members: StrVec,
}

#[derive(BartDisplay, Debug, Default)]
#[template = "templates/non_terminal_type_enum_template.rs"]
struct NonTerminalTypeEnum {
    comment: String,
    non_terminal: String,
    members: StrVec,
}

#[derive(BartDisplay, Debug, Default)]
#[template = "templates/non_terminal_type_vec_template.rs"]
struct NonTerminalTypeVec {
    comment: String,
    non_terminal: String,
    members: String,
}

#[derive(BartDisplay, Debug, Default)]
#[template = "templates/non_terminal_type_opt_template.rs"]
struct NonTerminalTypeOpt {
    comment: String,
    non_terminal: String,
    members: String,
}

fn to_camel_case(name: &str) -> String {
    name.chars().fold(String::new(), |mut acc, c| {
        if acc.is_empty() {
            acc.push(c.to_lowercase().next().unwrap())
        } else if c.is_uppercase() {
            acc.push('_');
            acc.push(c.to_lowercase().next().unwrap())
        } else {
            acc.push(c);
        }
        acc
    })
}

pub(crate) fn get_argument_name(
    s: &Symbol,
    arg_index: usize,
    terminals: &[String],
    terminal_names: &[String],
) -> String {
    let get_terminal_index = |tr: &str| terminals.iter().position(|t| *t == tr).unwrap();
    match s {
        Symbol::N(n) => {
            format!("{}_{}", to_camel_case(n), arg_index)
        }
        Symbol::T(Terminal::Trm(t, _)) => {
            let terminal_name = &terminal_names[get_terminal_index(t)];
            format!("{}_{}", to_camel_case(terminal_name), arg_index)
        }
        _ => panic!("Invalid symbol type {}", s),
    }
}

pub(crate) fn generate_argument_names(
    rhs: &[Symbol],
    terminals: &[String],
    terminal_names: &[String],
) -> Vec<String> {
    let get_terminal_index = |tr: &str| terminals.iter().position(|t| *t == tr).unwrap();
    rhs.iter()
        .enumerate()
        .filter(|(_, s)| !s.is_switch() && !s.is_pseudo())
        .map(|(i, a)| match a {
            Symbol::N(n) => {
                format!("{}_{}", to_camel_case(n), i)
            }
            Symbol::T(Terminal::Trm(t, _)) => {
                let terminal_name = &terminal_names[get_terminal_index(t)];
                format!("{}_{}", to_camel_case(terminal_name), i)
            }
            _ => panic!("Invalid symbol type in production!"),
        })
        .collect::<Vec<String>>()
}

fn generate_argument_list(pr: &Pr, terminals: &[&str], terminal_names: &[String]) -> String {
    let get_terminal_index = |tr: &str| terminals.iter().position(|t| *t == tr).unwrap();
    let mut arguments = pr
        .get_r()
        .iter()
        .enumerate()
        .filter(|(_, s)| !s.is_switch() && !s.is_pseudo())
        .map(|(i, a)| match a {
            Symbol::N(n) => {
                format!("_{}_{}: &ParseTreeStackEntry", to_camel_case(n), i)
            }
            Symbol::T(Terminal::Trm(t, _)) => {
                let terminal_name = &terminal_names[get_terminal_index(t)];
                format!(
                    "_{}_{}: &ParseTreeStackEntry",
                    to_camel_case(terminal_name),
                    i
                )
            }
            _ => panic!("Invalid symbol type in production!"),
        })
        .collect::<Vec<String>>();
    arguments.push("_parse_tree: &Tree<ParseTreeType>".to_string());
    arguments.join(", ")
}

fn generate_caller_argument_list(pr: &Pr) -> String {
    let mut arguments = pr
        .get_r()
        .iter()
        .filter(|s| !s.is_switch() && !s.is_pseudo())
        .enumerate()
        .map(|(i, _)| format!("&children[{}]", i))
        .collect::<Vec<String>>();
    arguments.push("parse_tree".to_string());
    arguments.join(", ")
}

// ---------------------------------------------------
// Part of the Public API
// *Changes will affect crate's version according to semver*
// ---------------------------------------------------
///
/// Generates the file with the user actions trait.
///
pub fn generate_user_trait_source(
    user_type_name: &str,
    user_trait_module_name: &str,
    grammar_config: &GrammarConfig,
) -> Result<String> {
    let terminals = grammar_config
        .cfg
        .get_ordered_terminals()
        .iter()
        .map(|(t, _)| *t)
        .collect::<Vec<&str>>();
    let terminal_names = terminals.iter().fold(Vec::new(), |mut acc, e| {
        let n = generate_terminal_name(e, usize::MAX, &grammar_config.cfg);
        acc.push(n);
        acc
    });

    let scanner_state_resolver = |s: &[usize]| {
        s.iter()
            .map(|s| {
                grammar_config.scanner_configurations[*s]
                    .scanner_name
                    .clone()
            })
            .collect::<Vec<String>>()
            .join(", ")
    };

    let type_system: GrammarTypeSystem = (&grammar_config.cfg).try_into()?;

    let production_output_types =
        type_system
            .out_types
            .iter()
            .fold(StrVec::new(0), |mut acc, (s, t)| {
                match t {
                    ASTType::Struct(_n, m) => {
                        let struct_data = NonTerminalTypeStruct {
                            comment: format!("production {}", s),
                            non_terminal: format!("{}{}", grammar_config.cfg.pr[*s].get_n_str(), s),
                            members: m.iter().fold(StrVec::new(4), |mut acc, (n, t)| {
                                acc.push(format!("{}: {},", n, t));
                                acc
                            }),
                        };
                        acc.push(format!("{}", struct_data));
                    }
                    ASTType::Enum(n, m) => {
                        let struct_data = NonTerminalTypeEnum {
                            comment: format!("production {}", s),
                            non_terminal: format!("{}{}", grammar_config.cfg.pr[*s].get_n_str(), s),
                            members: m.iter().enumerate().fold(
                                StrVec::new(4),
                                |mut acc, (i, t)| {
                                    acc.push(format!("{}{}({}),", n, i, t.type_name()));
                                    acc
                                },
                            ),
                        };
                        acc.push(format!("{}", struct_data));
                    }
                    ASTType::Repeat(m) => {
                        let members = m.iter().fold(String::new(), |mut acc, t| {
                            acc.push_str(&format!("{},", t.type_name()));
                            acc
                        });

                        let members = if m.len() == 1 {
                            format!("{}", members)
                        } else {
                            format!("({})", members)
                        };
                        let struct_data = NonTerminalTypeVec {
                            comment: format!("production {}", s),
                            non_terminal: format!("{}{}", grammar_config.cfg.pr[*s].get_n_str(), s),
                            members,
                        };
                        acc.push(format!("{}", struct_data));
                    }
                    ASTType::Option(m) => {
                        let members = m.iter().fold(String::new(), |mut acc, t| {
                            acc.push_str(&format!("{},", t.type_name()));
                            acc
                        });

                        let members = if m.len() == 1 {
                            format!("{}", members)
                        } else {
                            format!("({})", members)
                        };
                        let struct_data = NonTerminalTypeOpt {
                            comment: format!("production {}", s),
                            non_terminal: format!("{}{}", grammar_config.cfg.pr[*s].get_n_str(), s),
                            members,
                        };
                        acc.push(format!("{}", struct_data));
                    }
                    _ => (),
                }
                acc
            });

    let non_terminal_types =
        type_system
            .non_terminal_types
            .iter()
            .fold(StrVec::new(0), |mut acc, (s, t)| {
                match t {
                    ASTType::Struct(_n, m) => {
                        let struct_data = NonTerminalTypeStruct {
                            comment: format!("non-terminal {}", s),
                            non_terminal: s.clone(),
                            members: m.iter().fold(StrVec::new(4), |mut acc, (n, t)| {
                                acc.push(format!("{}: {},", n, t));
                                acc
                            }),
                        };
                        acc.push(format!("{}", struct_data));
                    }
                    ASTType::Enum(n, m) => {
                        let struct_data = NonTerminalTypeEnum {
                            comment: format!("non-terminal {}", s),
                            non_terminal: s.clone(),
                            members: m.iter().enumerate().fold(
                                StrVec::new(4),
                                |mut acc, (i, t)| {
                                    acc.push(format!("{}{}({}),", n, i, t.type_name()));
                                    acc
                                },
                            ),
                        };
                        acc.push(format!("{}", struct_data));
                    }
                    ASTType::Repeat(m) => {
                        let members = m.iter().fold(String::new(), |mut acc, t| {
                            acc.push_str(&format!("{},", t.type_name()));
                            acc
                        });

                        let members = if m.len() == 1 {
                            format!("{}", members)
                        } else {
                            format!("({})", members)
                        };
                        let struct_data = NonTerminalTypeVec {
                            comment: format!("non-terminal {}", s),
                            non_terminal: s.clone(),
                            members,
                        };
                        acc.push(format!("{}", struct_data));
                    }
                    ASTType::Option(m) => {
                        let members = m.iter().fold(String::new(), |mut acc, t| {
                            acc.push_str(&format!("{},", t.type_name()));
                            acc
                        });

                        let members = if m.len() == 1 {
                            format!("{}", members)
                        } else {
                            format!("({})", members)
                        };
                        let struct_data = NonTerminalTypeOpt {
                            comment: format!("non-terminal {}", s),
                            non_terminal: s.clone(),
                            members,
                        };
                        acc.push(format!("{}", struct_data));
                    }
                    _ => (),
                }
                acc
            });

    let trait_functions = grammar_config.cfg.pr.iter().enumerate().fold(
        StrVec::new(0).first_line_no_indent(),
        |mut acc, (i, p)| {
            let fn_name = to_camel_case(p.get_n_str());
            let prod_string = p.format(&scanner_state_resolver);
            let fn_arguments = generate_argument_list(p, &terminals, &terminal_names);
            let user_trait_function_data = UserTraitFunctionData {
                fn_name,
                prod_num: i,
                fn_arguments,
                prod_string,
            };
            acc.push(format!("{}", user_trait_function_data));
            acc
        },
    );

    let trait_caller =
        grammar_config
            .cfg
            .pr
            .iter()
            .enumerate()
            .fold(StrVec::new(12), |mut acc, (i, p)| {
                let fn_name = to_camel_case(p.get_n_str());
                let fn_arguments = generate_caller_argument_list(p);
                let user_trait_function_data = UserTraitCallerFunctionData {
                    fn_name,
                    prod_num: i,
                    fn_arguments,
                };
                acc.push(format!("{}", user_trait_function_data));
                acc
            });

    let user_trait_data = UserTraitData {
        user_type_name,
        production_output_types,
        non_terminal_types,
        trait_functions,
        trait_caller,
        user_trait_module_name,
    };
    //Ok(formatted_or_unchanged(format!("{}", user_trait_data)))
    Ok(format!("{}", user_trait_data))
}
