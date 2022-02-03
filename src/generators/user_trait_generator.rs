use crate::generators::case_helpers::{to_lower_snake_case, to_upper_camel_case};
use crate::generators::{generate_terminal_name, GrammarConfig};
use crate::parser::{ParolGrammarItem, Production};
use crate::transformation::ast_types::{ASTType, GrammarTypeSystem};
use crate::{ParolGrammar, Pr, StrVec, Symbol, Terminal};
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
struct UserTraitFunctionData<'a> {
    fn_name: &'a str,
    prod_num: usize,
    fn_arguments: String,
    prod_string: String,
    // Inner means the expanded version of the grammar.
    // If set to false the actual user grammar is meant.
    inner: bool,
}

#[derive(BartDisplay, Debug, Default)]
#[template = "templates/user_trait_template.rs"]
struct UserTraitData<'a> {
    user_type_name: String,
    auto_generate: bool,
    production_output_types: StrVec,
    non_terminal_types: StrVec,
    ast_type_decl: String,
    trait_functions: StrVec,
    trait_caller: StrVec,
    module_name: &'a str,
    user_trait_functions: StrVec,
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

pub(crate) fn get_argument_name(
    s: &Symbol,
    arg_index: usize,
    terminals: &[String],
    terminal_names: &[String],
) -> String {
    let get_terminal_index = |tr: &str| terminals.iter().position(|t| *t == tr).unwrap();
    match s {
        Symbol::N(n) => {
            format!("{}_{}", to_lower_snake_case(n), arg_index)
        }
        Symbol::T(Terminal::Trm(t, _)) => {
            let terminal_name = &terminal_names[get_terminal_index(t)];
            format!("{}_{}", to_lower_snake_case(terminal_name), arg_index)
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
                format!("{}_{}", to_lower_snake_case(n), i)
            }
            Symbol::T(Terminal::Trm(t, _)) => {
                let terminal_name = &terminal_names[get_terminal_index(t)];
                format!("{}_{}", to_lower_snake_case(terminal_name), i)
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
                format!("_{}_{}: &ParseTreeStackEntry", to_lower_snake_case(n), i)
            }
            Symbol::T(Terminal::Trm(t, _)) => {
                let terminal_name = &terminal_names[get_terminal_index(t)];
                format!(
                    "_{}_{}: &ParseTreeStackEntry",
                    to_lower_snake_case(terminal_name),
                    i
                )
            }
            _ => panic!("Invalid symbol type in production!"),
        })
        .collect::<Vec<String>>();
    arguments.push("_parse_tree: &Tree<ParseTreeType>".to_string());
    arguments.join(", ")
}

fn generate_argument_list_for_user_action(non_terminal: &str) -> String {
    format!("_arg: {}", to_upper_camel_case(non_terminal))
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

fn format_type(
    ast_type: &ASTType,
    non_terminal: &str,
    prod_num: Option<usize>,
    comment: &str,
) -> Option<String> {
    let (comment, non_terminal) = if let Some(prod_num) = prod_num {
        (
            format!("Type derived for {} {}", comment, prod_num),
            to_upper_camel_case(&format!("{}_{}", non_terminal, prod_num)),
        )
    } else {
        (
            format!("Type derived for {} {}", comment, non_terminal),
            to_upper_camel_case(non_terminal),
        )
    };

    match ast_type {
        ASTType::Struct(_n, m) => {
            let struct_data = NonTerminalTypeStruct {
                comment,
                non_terminal,
                members: m.iter().fold(StrVec::new(4), |mut acc, (n, t)| {
                    acc.push(format!("{}: {},", n, t));
                    acc
                }),
            };
            Some(format!("{}", struct_data))
        }
        ASTType::Enum(n, m) => {
            let struct_data = NonTerminalTypeEnum {
                comment,
                non_terminal,
                members: m
                    .iter()
                    .enumerate()
                    .fold(StrVec::new(4), |mut acc, (i, t)| {
                        acc.push(to_upper_camel_case(&format!(
                            "{}_{}({}),",
                            n,
                            i,
                            t.type_name()
                        )));
                        acc
                    }),
            };
            Some(format!("{}", struct_data))
        }
        ASTType::Repeat(m) => {
            let members = m.iter().fold(String::new(), |mut acc, t| {
                acc.push_str(&format!(
                    "{},",
                    match t {
                        ASTType::TypeRef(r) => r.to_string(),
                        _ => t.type_name(),
                    }
                ));
                acc
            });

            let members = if m.len() == 1 {
                members
            } else {
                format!("({})", members)
            };
            let struct_data = NonTerminalTypeVec {
                comment,
                non_terminal,
                members,
            };
            Some(format!("{}", struct_data))
        }
        ASTType::Option(m) => {
            let members = m.iter().fold(String::new(), |mut acc, t| {
                acc.push_str(&format!("{},", t.type_name()));
                acc
            });

            let members = if m.len() == 1 {
                members
            } else {
                format!("({})", members)
            };
            let struct_data = NonTerminalTypeOpt {
                comment,
                non_terminal,
                members,
            };
            Some(format!("{}", struct_data))
        }
        ASTType::Unit => {
            let struct_data = NonTerminalTypeStruct {
                comment,
                non_terminal,
                members: StrVec::new(0),
            };
            Some(format!("{}", struct_data))
        }
        _ => None,
    }
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
    module_name: &str,
    auto_generate: bool,
    parol_grammar: &ParolGrammar,
    grammar_config: &GrammarConfig,
) -> Result<String> {
    let user_type_name = to_upper_camel_case(user_type_name);
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

    let type_system: GrammarTypeSystem = if auto_generate {
        (&grammar_config.cfg).try_into()?
    } else {
        GrammarTypeSystem::default()
    };

    let production_output_types = if auto_generate {
        type_system
            .out_types
            .iter()
            .fold(StrVec::new(0), |mut acc, (s, t)| {
                format_type(
                    t,
                    grammar_config.cfg.pr[*s].get_n_str(),
                    Some(*s),
                    "production",
                )
                .into_iter()
                .for_each(|s| acc.push(s));
                acc
            })
    } else {
        StrVec::new(0)
    };

    let non_terminal_types = if auto_generate {
        type_system
            .non_terminal_types
            .iter()
            .fold(StrVec::new(0), |mut acc, (s, t)| {
                format_type(t, s, None, "non-terminal")
                    .into_iter()
                    .for_each(|s| acc.push(s));
                acc
            })
    } else {
        StrVec::new(0)
    };

    let ast_type_decl = if auto_generate {
        format!(
            "{}",
            NonTerminalTypeEnum {
                comment: "Derived from production output types".to_owned(),
                non_terminal: "ASTType".to_owned(),
                members: type_system.non_terminal_types.iter().fold(
                    StrVec::new(4),
                    |mut acc, (n, _)| {
                        let nt = to_upper_camel_case(n);
                        acc.push(format!("{}({}),", nt, nt));
                        acc
                    }
                ),
            }
        )
    } else {
        String::default()
    };

    let trait_functions = grammar_config.cfg.pr.iter().enumerate().fold(
        StrVec::new(0).first_line_no_indent(),
        |mut acc, (i, p)| {
            let fn_name = to_lower_snake_case(p.get_n_str());
            let prod_string = p.format(&scanner_state_resolver);
            let fn_arguments = generate_argument_list(p, &terminals, &terminal_names);
            let user_trait_function_data = UserTraitFunctionData {
                fn_name: &fn_name,
                prod_num: i,
                fn_arguments,
                prod_string,
                inner: true,
            };
            acc.push(format!("{}", user_trait_function_data));
            acc
        },
    );

    let user_trait_functions = if auto_generate {
        parol_grammar
            .item_stack
            .iter()
            .fold(
                (StrVec::new(0).first_line_no_indent(), 0),
                |(mut acc, mut i), p| {
                    if let ParolGrammarItem::Prod(Production { lhs, rhs: _ }) = p {
                        let fn_name = to_lower_snake_case(&lhs);
                        let prod_string = format!("{}", p.to_par());
                        let fn_arguments = generate_argument_list_for_user_action(&fn_name);
                        let user_trait_function_data = UserTraitFunctionData {
                            fn_name: &fn_name,
                            prod_num: i,
                            fn_arguments,
                            prod_string,
                            inner: false,
                        };
                        acc.push(format!("{}", user_trait_function_data));
                        i += 1;
                    }
                    (acc, i)
                },
            )
            .0
    } else {
        StrVec::default()
    };

    let trait_caller =
        grammar_config
            .cfg
            .pr
            .iter()
            .enumerate()
            .fold(StrVec::new(12), |mut acc, (i, p)| {
                let fn_name = to_lower_snake_case(p.get_n_str());
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
        auto_generate,
        production_output_types,
        non_terminal_types,
        ast_type_decl,
        trait_functions,
        trait_caller,
        module_name,
        user_trait_functions,
    };

    Ok(format!("{}", user_trait_data))
}
