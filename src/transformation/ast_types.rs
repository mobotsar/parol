use crate::analysis::lookahead_dfa::ProductionIndex;
use crate::generators::{generate_terminal_name, NamingHelper as NmHlp};
use crate::grammar::{ProductionAttribute, SymbolAttribute};
use crate::{Cfg, Pr, Symbol, Terminal};
use log::trace;
use miette::{miette, Result};
use std::collections::BTreeMap;
use std::convert::TryFrom;
use std::fmt::{Debug, Display, Error, Formatter};

///
/// Type information used for auto-generation
///
#[derive(Debug, Clone, PartialEq)]
pub enum ASTType {
    /// Not specified
    None,
    /// No type ()
    Unit,
    /// Will be generated to a Token structure
    Token(String),
    /// A type name
    TypeRef(String),
    /// A struct, i.e. a collection of types
    Struct(String, Vec<(String, ASTType)>),
    /// Will be generated as enum with given name
    Enum(String, Vec<ASTType>),
    /// Will be generated as Vec<T> where T is the type, similar to TypeRef
    Repeat(String),
    /// Will be generated as Option<Box<T>> where T is the type, similar to TypeRef
    Option(String),
}

impl ASTType {
    pub(crate) fn type_name(&self) -> String {
        match self {
            Self::None => "*TypeError*".to_owned(),
            Self::Unit => "()".to_owned(),
            Self::Token(t) => format!("OwnedToken /* {} */", t),
            Self::TypeRef(r) => format!("Box<{}>", r),
            Self::Struct(n, _) => n.to_string(),
            Self::Enum(n, _) => n.to_string(),
            Self::Repeat(r) => format!("Vec<{}>", r),
            Self::Option(o) => format!("Option<Box<{}>>", o),
        }
    }
}

impl Display for ASTType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::result::Result<(), Error> {
        match self {
            Self::None => write!(f, "-"),
            Self::Unit => write!(f, "()"),
            Self::Token(t) => write!(f, "OwnedToken /* {} */", t),
            Self::TypeRef(r) => write!(f, "Box<{}>", r),
            Self::Struct(n, m) => write!(
                f,
                "struct {} {{ {} }}",
                n,
                m.iter()
                    .map(|(n, t)| format!("{}: {}", n, t))
                    .collect::<Vec<String>>()
                    .join(", ")
            ),
            Self::Enum(n, t) => write!(
                f,
                "enum {} {{ {} }}",
                n,
                t.iter()
                    .enumerate()
                    .map(|(i, t)| format!("{}{}({})", n, i, t))
                    .collect::<Vec<String>>()
                    .join(", ")
            ),
            Self::Repeat(r) => write!(f, "Vec<{}>", r),
            Self::Option(o) => write!(f, "Option<Box<{}>>", o),
        }
    }
}

impl Default for ASTType {
    fn default() -> Self {
        Self::None
    }
}

///
/// An argument of a semantic action
///
#[derive(Debug, Default)]
pub struct Argument {
    /// Argument's name
    pub(crate) name: String,
    /// Argument's type
    pub(crate) arg_type: ASTType,
    /// Argument index or position
    pub(crate) index: Option<usize>,
    /// Indicates if the argument is used
    pub(crate) used: bool,
    /// Semantic information
    pub(crate) sem: SymbolAttribute,
}

impl Argument {
    /// Creates a new item
    pub fn new(name: &str, arg_type: ASTType) -> Self {
        Argument {
            name: NmHlp::to_lower_snake_case(name),
            arg_type,
            ..Default::default()
        }
    }

    /// Set argument index
    pub fn with_index(mut self, index: usize) -> Self {
        self.index = Some(index);
        self
    }

    /// Set argument's used state
    pub fn with_used(mut self, used: bool) -> Self {
        self.used = used;
        self
    }

    /// Set symbol attribute on this argument
    pub fn with_semantic(mut self, sem: SymbolAttribute) -> Self {
        self.sem = sem;
        self
    }
}

impl Display for Argument {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::result::Result<(), Error> {
        let arg_index = if let Some(index) = self.index {
            format!("_{}", index)
        } else {
            String::default()
        };

        write!(
            f,
            "{}{}{}: {}",
            NmHlp::item_unused_indicator(self.used),
            self.name,
            arg_index,
            self.arg_type.type_name()
        )
    }
}

///
/// A semantic action
///
/// For each production there exists an associated semantic action.
/// Any action has a kind of `input` information which can be deduced from the production's
/// right-hand side and resemble the action's argument list.
/// These arguments are feed at prase time by the parser automatically.
/// But in practice not all arguments provided by the parser are actually used because actions have
/// tow possible ways to obtain their input value:
///
/// * First the corresponding values can be obtained from the actions's parameter list
/// * Second the values can be popped from the AST stack
///
/// The first way would actually be used for simple tokens.
/// The second way is applicable if there are already more complex items on the AST stack which
/// is the case for any non-terminals.
///
///
#[derive(Debug, Default)]
pub struct Action {
    /// Associated non-terminal
    pub(crate) non_terminal: String,

    /// Production number
    /// The production index is identical for associated actions and productions, i.e. you can use
    /// this index in Cfg.pr and in GrammarTypeSystem.actions to obtain a matching pair of
    /// production and action.
    pub(crate) prod_num: ProductionIndex,

    /// The function name
    pub(crate) fn_name: String,

    /// The argument list as they are provided by the parser
    pub(crate) args: Vec<Argument>,

    /// The output type, i.e. the return type of the action which corresponds to the constructed
    /// new value pushed on the AST stack.
    /// If there exists an associated semantic action of the user's `input` grammar this type is
    /// used to call it with.
    pub(crate) out_type: ASTType,

    /// Semantic specification
    pub(crate) sem: ProductionAttribute,
}

impl Action {
    /// Create a new item
    pub fn new(non_terminal: &str, prod_num: ProductionIndex) -> Self {
        Action {
            non_terminal: non_terminal.to_string(),
            prod_num,
            ..Default::default()
        }
    }

    /// Set the function name
    pub fn with_name(mut self, fn_name: String) -> Self {
        self.fn_name = fn_name;
        self
    }

    /// Set the function's arguments
    pub fn with_args(mut self, args: Vec<Argument>) -> Self {
        self.args = args;
        self
    }

    /// Set the function's output type
    pub fn with_type(mut self, out_type: ASTType) -> Self {
        self.out_type = out_type;
        self
    }

    /// Set the function's semantic from a ProductionAttribute
    pub fn with_semantic(mut self, sem: &Option<ProductionAttribute>) -> Self {
        self.sem = match sem {
            Some(a) => a.clone(),
            None => ProductionAttribute::None,
        };
        self
    }
}

impl Display for Action {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::result::Result<(), Error> {
        write!(
            f,
            "/* {} */ (({}) -> {})  {{ {} }}",
            self.prod_num,
            self.args
                .iter()
                .map(|a| a.arg_type.type_name())
                .collect::<Vec<String>>()
                .join(", "),
            self.out_type,
            self.sem,
        )
    }
}

///
/// A type system for a given grammar
///
#[derive(Debug, Default)]
pub struct GrammarTypeSystem {
    /// All semantic actions, indices correspond to production indices in Cfg
    pub actions: Vec<Action>,

    /// Calculated type of non-terminals
    pub non_terminal_types: BTreeMap<String, ASTType>,

    /// Helper
    terminals: Vec<String>,
    terminal_names: Vec<String>,
}

impl GrammarTypeSystem {
    /// Create a new item
    /// Initializes the helper data `terminals` and `terminal_names`.
    pub fn new(cfg: &Cfg) -> Self {
        let mut me = Self::default();
        me.terminals = cfg
            .get_ordered_terminals()
            .iter()
            .map(|(t, _)| t.to_string())
            .collect::<Vec<String>>();

        me.terminal_names = me.terminals.iter().fold(Vec::new(), |mut acc, e| {
            let n = generate_terminal_name(e, None, cfg);
            acc.push(n);
            acc
        });
        me
    }

    /// Creates the list of actions from the Cfg.
    fn deduce_actions(&mut self, cfg: &Cfg) -> Result<()> {
        self.actions = Vec::with_capacity(cfg.pr.len());
        for (i, pr) in cfg.pr.iter().enumerate() {
            self.actions.push(
                Action::new(pr.get_n_str(), i)
                    .with_name(NmHlp::to_lower_snake_case(&format!(
                        "{}_{}",
                        pr.get_n_str(),
                        i
                    )))
                    .with_args(self.build_argument_list(pr)?)
                    .with_type(self.deduce_action_type_from_production(pr)?)
                    .with_semantic(&pr.2),
            );
        }
        Ok(())
    }

    fn build_argument_list(&self, prod: &Pr) -> Result<Vec<Argument>> {
        let mut types = prod.get_r().iter().filter(|s| s.is_t() || s.is_n()).fold(
            Ok(Vec::new()),
            |acc, s| {
                acc.and_then(|mut acc| {
                    Self::deduce_type_of_symbol(s).map(|t| {
                        acc.push((t, s.attribute()));
                        acc
                    })
                })
            },
        )?;

        Ok(
            NmHlp::generate_member_names(prod.get_r(), &self.terminals, &self.terminal_names)
                .iter()
                .enumerate()
                .zip(types.drain(..))
                .map(|((i, n), (t, a))| {
                    // Tokens are taken from the parameter list per definition.
                    let used = matches!(t, ASTType::Token(_));
                    Argument::new(n, t)
                        .with_used(used)
                        .with_index(i)
                        .with_semantic(a)
                })
                .collect::<Vec<Argument>>(),
        )
    }

    ///
    /// Returns a vector of action indices matching the given non-terminal n
    ///
    pub fn matching_actions(&self, n: &str) -> Vec<usize> {
        self.actions
            .iter()
            .enumerate()
            .fold(Vec::new(), |mut acc, (i, a)| {
                if a.non_terminal == n {
                    acc.push(i);
                }
                acc
            })
    }

    /// Add non-terminal type
    fn add_non_terminal_type(&mut self, non_terminal: &str, nt_type: ASTType) -> Result<()> {
        self.non_terminal_types
            .insert(non_terminal.to_owned(), nt_type)
            .map_or_else(
                || {
                    trace!("Setting type for non-terminal {}", non_terminal);
                    Ok(())
                },
                |_| {
                    Err(miette!(
                        "Type for non-terminal {} already specified",
                        non_terminal
                    ))
                },
            )
    }

    fn struct_data_of_production(&self, prod: &Pr) -> Result<ASTType> {
        let mut arguments = self.build_argument_list(prod)?;
        Ok(ASTType::Struct(
            NmHlp::to_upper_camel_case(prod.get_n_str()),
            arguments
                .drain(..)
                .map(|arg| (arg.name, arg.arg_type))
                .collect::<Vec<(String, ASTType)>>(),
        ))
    }

    fn deduce_action_type_from_production(&self, prod: &Pr) -> Result<ASTType> {
        match prod.len() {
            0 => Ok(ASTType::Unit),
            1 => match &prod.1[..] {
                [Symbol::Pseudo(SymbolAttribute::OptionalNone(o))] => {
                    Ok(ASTType::Option(o.to_string()))
                }
                _ => Ok(self.struct_data_of_production(prod)?),
            },
            _ => match prod.1[0].attribute() {
                SymbolAttribute::OptionalSome => Ok(ASTType::Option(prod.1[0].get_n().unwrap())),
                SymbolAttribute::Repetition => Ok(ASTType::Repeat(prod.1[0].get_n().unwrap())),
                _ => Ok(self.struct_data_of_production(prod)?),
            },
        }
    }

    fn deduce_type_of_symbol(symbol: &Symbol) -> Result<ASTType> {
        match symbol {
            Symbol::T(Terminal::Trm(t, _)) => Ok(ASTType::Token(t.to_string())),
            Symbol::N(n, a) => {
                let inner_type_name = NmHlp::to_upper_camel_case(n);
                match a {
                    Some(SymbolAttribute::None) => Ok(ASTType::TypeRef(inner_type_name)),
                    Some(SymbolAttribute::OptionalSome) => Ok(ASTType::Option(inner_type_name)),
                    Some(SymbolAttribute::OptionalNone(n)) => Err(miette!(
                        "OptionalNone attribute on non-terminal {} is not supported!",
                        n
                    )),
                    Some(SymbolAttribute::Repetition) => Ok(ASTType::Repeat(inner_type_name)),
                    None => Ok(ASTType::TypeRef(inner_type_name)),
                }
            }
            Symbol::Pseudo(a) => match a {
                SymbolAttribute::OptionalNone(n) => {
                    Ok(ASTType::Option(NmHlp::to_upper_camel_case(n)))
                }
                _ => Err(miette!(
                    "Attribute {} on pseudo symbol  is not supported!",
                    a
                )),
            },
            _ => Ok(ASTType::Unit),
        }
    }

    fn deduce_type_of_non_terminal(&mut self, actions: Vec<usize>) -> Option<ASTType> {
        match actions.len() {
            // Productions can be optimized away, when they have duplicates!
            0 => None,
            // Only one production for this non-terminal: we take the out-type of the single action
            1 => Some(self.actions[actions[0]].out_type.clone()),
            _ => {
                if let Some(option_index) = actions.iter().position(|a| {
                    let a = &self.actions[*a];
                    a.args.len() == 1 && matches!(a.args[0].sem, SymbolAttribute::OptionalSome)
                }) {
                    // Test for option first:
                    //      Does there exist an action with one argument that has
                    //      SymbolAttribute::OptionalSome set?
                    Some(ASTType::Option(NmHlp::to_upper_camel_case(
                        &self.actions[actions[option_index]].non_terminal,
                    )))
                } else if let Some(vec_index) = actions.iter().position(|a| {
                    // Test for collection next:
                    //      Does there exist an action with no arguments and the
                    //      ProductionAttribute::CollectionStart set?
                    let a = &self.actions[*a];
                    a.args.is_empty() && matches!(a.sem, ProductionAttribute::CollectionStart)
                }) {
                    Some(ASTType::Repeat(NmHlp::to_upper_camel_case(
                        &self.actions[actions[vec_index]].non_terminal,
                    )))
                } else {
                    // Otherwise: we generate an enum form the out-types of each action
                    let nt_ref = &self.actions[actions[0]].non_terminal;
                    Some(ASTType::Enum(
                        NmHlp::to_upper_camel_case(nt_ref),
                        actions
                            .iter()
                            .map(|i| self.actions[*i].out_type.clone())
                            .collect::<Vec<ASTType>>(),
                    ))
                }
            }
        }
    }

    fn deduce_type_of_non_terminals(&mut self, cfg: &Cfg) -> Result<()> {
        for nt in cfg.get_non_terminal_set() {
            let actions = self.matching_actions(&nt);
            if let Some(nt_type) = self.deduce_type_of_non_terminal(actions) {
                self.add_non_terminal_type(&nt, nt_type)?;
            }
        }
        Ok(())
    }
}

impl Display for GrammarTypeSystem {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::result::Result<(), Error> {
        for action in &self.actions {
            writeln!(f, "{}", action)?;
        }
        writeln!(f)?;
        for (non_terminal, ast_type) in &self.non_terminal_types {
            writeln!(f, "{}:  {}", non_terminal, ast_type)?;
        }
        Ok(())
    }
}

impl TryFrom<&Cfg> for GrammarTypeSystem {
    type Error = miette::Error;
    fn try_from(cfg: &Cfg) -> Result<Self> {
        let mut me = Self::new(cfg);
        me.deduce_actions(cfg)?;
        me.deduce_type_of_non_terminals(cfg)?;
        Ok(me)
    }
}

#[cfg(test)]
mod tests {
    use super::{ASTType, GrammarTypeSystem};
    use crate::{left_factor, obtain_grammar_config_from_string, Cfg};
    use log::trace;
    use proptest::prelude::*;
    use std::convert::TryInto;
    use std::sync::Once;

    static INIT: Once = Once::new();

    static GRAMMAR1: &str = r#"%start S %% S: "a" {"b-rpt"} "c" {"d-rpt"};"#;
    static GRAMMAR2: &str = r#"%start S %% S: "a" ["b-opt"] "c" ["d-opt"];"#;

    lazy_static! {
        // S: "a" {"b-rpt"} "c" {"d-rpt"};
        // =>
        // /* 0 */ S: "a" Vec<SList> "c" Vec<SList1>;
        // /* 1 */ SList1: "d-rpt" Vec<SList1>; // Vec<T>::Push
        // /* 2 */ SList1: ; // Vec<T>::New
        // /* 3 */ SList: "b-rpt" Vec<SList>; // Vec<T>::Push
        // /* 4 */ SList: ; // Vec<T>::New
        static ref G1: Cfg = left_factor(
            &obtain_grammar_config_from_string(GRAMMAR1, false).unwrap().cfg);
        static ref TYPE_SYSTEM1: GrammarTypeSystem = (&*G1).try_into().unwrap();

        // S: "a" ["b-opt"] "c" ["d-opt"];
        // =>
        // /* 0 */ S: "a" SSuffix2;
        // /* 1 */ SSuffix2: SOpt /* Option::Some */ "c" SSuffix1;
        // /* 2 */ SSuffix2: /* Option<SOpt>::None */ "c" SSuffix;
        // /* 3 */ SSuffix1: SOpt1 /* Option::Some */;
        // /* 4 */ SSuffix1: /* Option<SOpt1>::None */;
        // /* 5 */ SSuffix: SOpt1 /* Option::Some */;
        // /* 6 */ SSuffix: /* Option<SOpt1>::None */;
        // /* 7 */ SOpt1: "d-opt";
        // /* 8 */ SOpt: "b-opt";
        static ref G2: Cfg = left_factor(
            &obtain_grammar_config_from_string(GRAMMAR2, false).unwrap().cfg);
        static ref TYPE_SYSTEM2: GrammarTypeSystem = (&*G2).try_into().unwrap();
    }

    fn setup() {
        INIT.call_once(env_logger::init);
    }

    proptest! {
        #[test]
        fn type_creation_repeat_props(prod_num in 0usize..4) {
            setup();

            assert_eq!(5, TYPE_SYSTEM1.actions.len());
            assert_eq!(3, TYPE_SYSTEM1.non_terminal_types.len());

            assert!(TYPE_SYSTEM1.non_terminal_types.contains_key(G1.pr[prod_num].get_n_str()));
            match &TYPE_SYSTEM1.actions[prod_num].out_type {
                ASTType::Enum(n, m) => {
                    assert_eq!(n, G1.pr[prod_num].get_n_str());
                    assert_eq!(m.len(), (&G1).matching_productions(G1.pr[prod_num].get_n_str()).len())
                }
                _ => ()
            }
        }
    }

    #[test]
    fn type_creation_repeat_1() {
        setup();

        trace!("{}", *TYPE_SYSTEM1);

        assert_eq!(5, TYPE_SYSTEM1.actions.len());
        assert_eq!(3, TYPE_SYSTEM1.non_terminal_types.len());
    }

    proptest! {
        #[test]
        fn type_creation_optional_pros(prod_num in 0usize..8) {
            setup();

            assert!(TYPE_SYSTEM2.non_terminal_types.contains_key(G2.pr[prod_num].get_n_str()));
            match &TYPE_SYSTEM2.actions[prod_num].out_type {
                ASTType::Enum(n, m) => {
                    assert_eq!(n, G2.pr[prod_num].get_n_str());
                    assert_eq!(m.len(), (&G2).matching_productions(G2.pr[prod_num].get_n_str()).len())
                }
                _ => ()
            }
        }
    }

    #[test]
    fn type_creation_optional_1() {
        setup();

        trace!("{}", *TYPE_SYSTEM2);

        assert_eq!(9, TYPE_SYSTEM2.actions.len());
        assert_eq!(6, TYPE_SYSTEM2.non_terminal_types.len());

        // /* 2 */ SSuffix2: /* Option<SOpt>::None */ "c" SSuffix;
        assert_eq!(
            2,
            TYPE_SYSTEM2.actions[2].args.len(),
            "Option::None should not appear in action arguments!"
        );
        assert!(
            matches!(TYPE_SYSTEM2.actions[2].args[0].arg_type, ASTType::Token(_)),
            "Type of argument 0 in action 2 should be Token"
        );
        assert!(
            matches!(&TYPE_SYSTEM2.actions[2].out_type, ASTType::Struct(n, _) if n == "SSuffix2"),
            "Output type of action 2 should be struct SSuffix2 but was {}",
            TYPE_SYSTEM2.actions[2].out_type
        );
    }
}
