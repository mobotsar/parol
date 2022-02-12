use super::{
    NonTerminalTypeEnum, NonTerminalTypeOpt, NonTerminalTypeStruct, NonTerminalTypeVec,
    UserTraitCallerFunctionData, UserTraitData, UserTraitFunctionData,
};
use crate::generators::naming_helper::NamingHelper as NmHlp;
use crate::generators::GrammarConfig;
use crate::parser::{ParolGrammarItem, Production};
use crate::transformation::ast_types::{ASTType, Action, GrammarTypeSystem};
use crate::{ParolGrammar, Pr, StrVec};
use miette::Result;
use std::collections::HashSet;
use std::convert::TryInto;

/// Generator for user trait code
pub struct UserTraitGenerator<'a> {
    user_type_name: String,
    module_name: &'a str,
    auto_generate: bool,
    parol_grammar: &'a ParolGrammar,
    grammar_config: &'a GrammarConfig,
}

impl<'a> UserTraitGenerator<'a> {
    /// Creates a new item
    pub fn new(
        user_type_name: &'a str,
        module_name: &'a str,
        auto_generate: bool,
        parol_grammar: &'a ParolGrammar,
        grammar_config: &'a GrammarConfig,
    ) -> Self {
        let user_type_name = NmHlp::to_upper_camel_case(user_type_name);
        Self {
            user_type_name,
            module_name,
            auto_generate,
            parol_grammar,
            grammar_config,
        }
    }

    fn generate_inner_action_args(&self, action: &Action) -> String {
        // We reference the parse_tree argument only if a token is in the argument list
        let mut parse_tree_argument_used = false;
        let mut arguments = action
            .args
            .iter()
            .map(|a| {
                if matches!(a.arg_type, ASTType::Token(_)) {
                    parse_tree_argument_used = true;
                }
                format!(
                    "{}{}: &ParseTreeStackEntry",
                    NmHlp::item_unused_indicator(self.auto_generate && a.used),
                    a.name,
                )
            })
            .collect::<Vec<String>>();
        arguments.push(format!(
            "{}parse_tree: &Tree<ParseTreeType>",
            NmHlp::item_unused_indicator(self.auto_generate && parse_tree_argument_used)
        ));
        arguments.join(", ")
    }

    fn generate_user_action_args(non_terminal: &str) -> String {
        format!("_arg: {}", NmHlp::to_upper_camel_case(non_terminal))
    }

    fn generate_token_assignments(_str_vec: &mut StrVec, _action: &Action) {}

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
                NmHlp::to_upper_camel_case(&format!("{}_{}", non_terminal, prod_num)),
            )
        } else {
            (
                format!("Type derived for {} {}", comment, non_terminal),
                NmHlp::to_upper_camel_case(non_terminal),
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
                            acc.push(NmHlp::to_upper_camel_case(&format!(
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
            ASTType::Repeat(r) => {
                let struct_data = NonTerminalTypeVec {
                    comment,
                    non_terminal,
                    type_ref: r.clone(),
                };
                Some(format!("{}", struct_data))
            }
            ASTType::Option(o) => {
                let struct_data = NonTerminalTypeOpt {
                    comment,
                    non_terminal,
                    type_ref: o.clone(),
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
    pub fn generate_user_trait_source(self) -> Result<String> {
        let scanner_state_resolver = |s: &[usize]| {
            s.iter()
                .map(|s| {
                    self.grammar_config.scanner_configurations[*s]
                        .scanner_name
                        .clone()
                })
                .collect::<Vec<String>>()
                .join(", ")
        };

        let type_system: GrammarTypeSystem = if self.auto_generate {
            (&self.grammar_config.cfg).try_into()?
        } else {
            GrammarTypeSystem::default()
        };

        let production_output_types = if self.auto_generate {
            type_system
                .actions
                .iter()
                .fold(StrVec::new(0), |mut acc, a| {
                    Self::format_type(&a.out_type, &a.non_terminal, Some(a.prod_num), "production")
                        .into_iter()
                        .for_each(|s| acc.push(s));
                    acc
                })
        } else {
            StrVec::new(0)
        };

        let non_terminal_types = if self.auto_generate {
            type_system
                .non_terminal_types
                .iter()
                .fold(StrVec::new(0), |mut acc, (s, t)| {
                    Self::format_type(t, s, None, "non-terminal")
                        .into_iter()
                        .for_each(|s| acc.push(s));
                    acc
                })
        } else {
            StrVec::new(0)
        };

        let ast_type_decl = if self.auto_generate {
            format!(
                "{}",
                NonTerminalTypeEnum {
                    comment: "Derived from production output types".to_owned(),
                    non_terminal: "ASTType".to_owned(),
                    members: type_system.non_terminal_types.iter().fold(
                        StrVec::new(4),
                        |mut acc, (n, _)| {
                            let nt = NmHlp::to_upper_camel_case(n);
                            acc.push(format!("{}({}),", nt, nt));
                            acc
                        }
                    ),
                }
            )
        } else {
            String::default()
        };

        let trait_functions =
            type_system
                .actions
                .iter()
                .fold(StrVec::new(0).first_line_no_indent(), |mut acc, a| {
                    let prod_num = a.prod_num;
                    let p = &self.grammar_config.cfg.pr[prod_num];
                    let fn_name = NmHlp::to_lower_snake_case(&a.non_terminal);
                    let prod_string = p.format(&scanner_state_resolver);
                    let fn_arguments = self.generate_inner_action_args(a);
                    let mut code = StrVec::new(8);
                    Self::generate_token_assignments(&mut code, a);
                    let user_trait_function_data = UserTraitFunctionData {
                        fn_name: &fn_name,
                        prod_num,
                        fn_arguments,
                        prod_string,
                        code,
                        inner: true,
                    };
                    acc.push(format!("{}", user_trait_function_data));
                    acc
                });

        let user_trait_functions = if self.auto_generate {
            let mut processed_non_terminals: HashSet<String> = HashSet::new();
            self.parol_grammar
                .item_stack
                .iter()
                .fold(
                    (StrVec::new(0).first_line_no_indent(), 0),
                    |(mut acc, mut i), p| {
                        if let ParolGrammarItem::Prod(Production { lhs, rhs: _ }) = p {
                            if !processed_non_terminals.contains(lhs) {
                                let fn_name =
                                    NmHlp::escape_rust_keyword(NmHlp::to_lower_snake_case(lhs));
                                let prod_string = p.to_par();
                                let fn_arguments = Self::generate_user_action_args(lhs);
                                let code = StrVec::default();
                                let user_trait_function_data = UserTraitFunctionData {
                                    fn_name: &fn_name,
                                    prod_num: i,
                                    fn_arguments,
                                    prod_string,
                                    code,
                                    inner: false,
                                };
                                acc.push(format!("{}", user_trait_function_data));
                                processed_non_terminals.insert(lhs.to_string());
                            }
                            i += 1;
                        }
                        (acc, i)
                    },
                )
                .0
        } else {
            StrVec::default()
        };

        let trait_caller = self.grammar_config.cfg.pr.iter().enumerate().fold(
            StrVec::new(12),
            |mut acc, (i, p)| {
                let fn_name = NmHlp::to_lower_snake_case(p.get_n_str());
                let fn_arguments = Self::generate_caller_argument_list(p);
                let user_trait_function_data = UserTraitCallerFunctionData {
                    fn_name,
                    prod_num: i,
                    fn_arguments,
                };
                acc.push(format!("{}", user_trait_function_data));
                acc
            },
        );

        let user_trait_data = UserTraitData {
            user_type_name: self.user_type_name,
            auto_generate: self.auto_generate,
            production_output_types,
            non_terminal_types,
            ast_type_decl,
            trait_functions,
            trait_caller,
            module_name: self.module_name,
            user_trait_functions,
        };

        Ok(format!("{}", user_trait_data))
    }
}
