use crate::analysis::lookahead_dfa::ProductionIndex;
use crate::grammar::SemanticInfo;
use crate::{Cfg, Pr, Symbol};
use log::trace;
use miette::{miette, Result};
use std::collections::BTreeMap;
use std::convert::TryFrom;
use std::fmt::{Debug, Display, Error, Formatter};

///
/// Type information used for auto-generation
///
#[derive(Debug, Clone)]
pub enum ASTType {
    /// Not specified
    None,
    /// No type ()
    Unit,
    /// Will be generated to a Token structure
    Token(String),
    /// A type name
    TypeRef(String),
    /// A tuple, i.e. a sequence of types
    Tuple(Vec<ASTType>),
    /// Will be generated as enum with given name
    Enum(String, Vec<ASTType>),
    /// Will be generated as Vec<T>
    Repeat(Vec<ASTType>),
    /// Will be generated as Option<T>
    Option(Vec<ASTType>),
}

impl Display for ASTType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::result::Result<(), Error> {
        match self {
            Self::None => write!(f, "-"),
            Self::Unit => write!(f, "()"),
            Self::Token(t) => write!(f, "{}", t),
            Self::TypeRef(r) => write!(f, "{}", r),
            Self::Tuple(t) => write!(
                f,
                "({})",
                t.iter()
                    .map(|t| format!("{}", t))
                    .collect::<Vec<String>>()
                    .join(", ")
            ),
            Self::Enum(n, t) => write!(
                f,
                "enum {} {{{}}}",
                n,
                t.iter()
                    .enumerate()
                    .map(|(i, t)| format!("{}{}: {}", n, i, t))
                    .collect::<Vec<String>>()
                    .join(", ")
            ),
            Self::Repeat(t) => {
                if t.len() <= 1 {
                    write!(
                        f,
                        "Vec<{}>",
                        t.iter()
                            .map(|t| format!("{}", t))
                            .collect::<Vec<String>>()
                            .join(" ")
                    )
                } else {
                    write!(
                        f,
                        "Vec<({})>",
                        t.iter()
                            .map(|t| format!("{}", t))
                            .collect::<Vec<String>>()
                            .join(" ")
                    )
                }
            }
            Self::Option(t) => write!(
                f,
                "Option<{}>",
                t.iter()
                    .map(|t| format!("{}", t))
                    .collect::<Vec<String>>()
                    .join(" ")
            ),
        }
    }
}

///
/// Predefined actions that can be generated automatically
///
#[derive(Debug, Clone)]
pub enum Semantic {
    /// Standard semantic
    None,
    /// Used for productions marked with a SemanticInfo::CollectionStart
    StartCollection,
    /// Add to a collection
    AddToCollection,
    /// An End-Of-Repetition where the collection has to be reversed
    /// The vector contains the names of the items that are collections
    ReverseCollection(Vec<String>),
    /// An Optional::Some case
    OptionalSome,
    /// An Optional::None case
    OptionalNone,
}

impl Display for Semantic {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::result::Result<(), Error> {
        match self {
            Self::None => write!(f, "-"),
            Self::StartCollection => write!(f, "Vec::New"),
            Self::AddToCollection => write!(f, "Vec::Push"),
            Self::ReverseCollection(v) => write!(f, "Vec::Rev({})", v.join(", ")),
            Self::OptionalSome => write!(f, "Option::Some"),
            Self::OptionalNone => write!(f, "Option::None"),
        }
    }
}

///
/// A type system for a given grammar
///
#[derive(Debug, Default)]
pub struct GrammarTypeSystem {
    ///
    /// For each production there exists an `input` type.
    /// This type is the input related side of the semantic action associated with that
    /// productions.
    /// This type(s) correspond(s) to the parameters and is(are) feed at call time in two possible
    /// ways
    /// * First the corresponding values can be obtained from the actions's parameter list
    /// * Second the values can be popped from the AST stack
    ///
    /// The first way would actually be used for simple tokens.
    /// The second way is applicable if there are already more complex items on the AST stack which
    /// is the case for any non-terminals.
    ///
    pub in_types: BTreeMap<ProductionIndex, ASTType>,

    ///
    /// For each used `input` type there exists one `output` types.
    /// These `output` types are usually created as compounds of the `input` types.
    ///
    /// These types correspond to the constructed new values pushed on the AST stack.
    /// If there exists an associated semantic action of the user's `input` grammar this type is
    /// used to call it with.
    ///
    pub out_types: BTreeMap<ProductionIndex, ASTType>,

    /// Calculated type of non-terminals
    pub non_terminal_types: BTreeMap<String, ASTType>,

    /// Information to fill the semantic gap in special cases
    pub semantics: BTreeMap<ProductionIndex, Semantic>,
}

impl GrammarTypeSystem {
    /// Create a new item
    pub fn new() -> Self {
        Self::default()
    }

    /// Add an input type
    fn add_input_type(&mut self, prod_num: ProductionIndex, in_type: ASTType) -> Result<()> {
        self.in_types.insert(prod_num, in_type).map_or_else(
            || {
                trace!("Setting input type for production {}", prod_num);
                Ok(())
            },
            |_| {
                Err(miette!(
                    "Input type for production {} already specified",
                    prod_num
                ))
            },
        )
    }

    /// Add an output type
    fn add_output_type(&mut self, prod_num: ProductionIndex, out_type: ASTType) -> Result<()> {
        self.out_types.insert(prod_num, out_type).map_or_else(
            || {
                trace!("Setting output type for production {}", prod_num);
                Ok(())
            },
            |_| {
                Err(miette!(
                    "Output type for production {} already specified",
                    prod_num
                ))
            },
        )
    }

    /// Add a semantic
    fn add_semantic(&mut self, prod_num: ProductionIndex, sem: Semantic) -> Result<()> {
        self.semantics.insert(prod_num, sem).map_or_else(
            || {
                trace!("Setting semantic for production {}", prod_num);
                Ok(())
            },
            |_| {
                Err(miette!(
                    "Semantic for production {} already specified",
                    prod_num
                ))
            },
        )
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

    fn add_pairwise_types(&mut self, cfg: &Cfg) -> Result<()> {
        cfg.get_non_terminal_set()
            .iter()
            .map(|nt| cfg.matching_productions(nt))
            .filter(|p| p.len() == 2)
            .fold(Ok(()), |mut acc, p| {
                if acc.is_ok() {
                    let p0 = &p[0];
                    let p1 = &p[1];

                    let rhs0 = p0.1.get_r();
                    let rhs1 = p1.1.get_r();
                    match (&rhs0[..], &rhs1[..]) {
                        ([Symbol::Pseudo(SemanticInfo::OptionalNone(n))], _) => {
                            acc = self
                                .add_input_type(
                                    p0.0,
                                    ASTType::Option(vec![ASTType::TypeRef(n.to_string())]),
                                )
                                .and_then(|_| {
                                    self.add_output_type(
                                        p0.0,
                                        ASTType::Option(vec![ASTType::TypeRef(n.to_string())]),
                                    )
                                })
                                .and_then(|_| self.add_semantic(p0.0, Semantic::OptionalNone))
                                .and_then(|_| {
                                    self.add_input_type(
                                        p1.0,
                                        ASTType::Option(vec![ASTType::TypeRef(n.to_string())]),
                                    )
                                })
                                .and_then(|_| {
                                    self.add_output_type(
                                        p1.0,
                                        ASTType::Option(vec![ASTType::TypeRef(n.to_string())]),
                                    )
                                })
                                .and_then(|_| self.add_semantic(p1.0, Semantic::OptionalSome));
                        }
                        (_, [Symbol::Pseudo(SemanticInfo::OptionalNone(n))]) => {
                            acc = self
                                .add_input_type(
                                    p1.0,
                                    ASTType::Option(vec![ASTType::TypeRef(n.to_string())]),
                                )
                                .and_then(|_| {
                                    self.add_output_type(
                                        p1.0,
                                        ASTType::Option(vec![ASTType::TypeRef(n.to_string())]),
                                    )
                                })
                                .and_then(|_| self.add_semantic(p0.0, Semantic::OptionalSome))
                                .and_then(|_| {
                                    self.add_input_type(
                                        p0.0,
                                        ASTType::Option(vec![ASTType::TypeRef(n.to_string())]),
                                    )
                                })
                                .and_then(|_| {
                                    self.add_output_type(
                                        p0.0,
                                        ASTType::Option(vec![ASTType::TypeRef(n.to_string())]),
                                    )
                                })
                                .and_then(|_| self.add_semantic(p1.0, Semantic::OptionalNone));
                        }
                        ([Symbol::Pseudo(SemanticInfo::CollectionStart(n))], _) => {
                            acc = self
                                .add_output_type(p0.0, ASTType::TypeRef(n.to_string()))
                                .and_then(|_| self.add_semantic(p0.0, Semantic::StartCollection))
                                .and_then(|_| {
                                    self.add_output_type(p1.0, ASTType::TypeRef(n.to_string()))
                                })
                                .and_then(|_| self.add_semantic(p1.0, Semantic::AddToCollection));
                        }
                        (_, [Symbol::Pseudo(SemanticInfo::CollectionStart(n))]) => {
                            acc = self
                                .add_output_type(p1.0, ASTType::TypeRef(n.to_string()))
                                .and_then(|_| self.add_semantic(p1.0, Semantic::StartCollection))
                                .and_then(|_| {
                                    self.add_output_type(p0.0, ASTType::TypeRef(n.to_string()))
                                })
                                .and_then(|_| self.add_semantic(p0.0, Semantic::AddToCollection));
                        }
                        _ => (),
                    }
                }
                acc
            })?;
        Ok(())
    }

    fn add_other_types(&mut self, cfg: &Cfg) -> Result<()> {
        cfg.get_non_terminal_set()
            .iter()
            .map(|nt| cfg.matching_productions(nt))
            .fold(Ok(()), |mut acc, p| {
                for (i, pr) in p {
                    if !self.in_types.contains_key(&i) {
                        let in_type = Self::deduce_in_type_of_production(pr);
                        acc = acc.and_then(|_| self.add_input_type(i, in_type));
                    }
                    if !self.out_types.contains_key(&i) {
                        let out_type = Self::deduce_out_type_of_production(pr);
                        acc = acc.and_then(|_| self.add_output_type(i, out_type));
                    }
                }
                acc
            })?;
        Ok(())
    }

    fn deduce_semantics(&mut self, cfg: &Cfg) -> Result<()> {
        cfg.get_non_terminal_set()
            .iter()
            .map(|nt| cfg.matching_productions(nt))
            .fold(Ok(()), |mut acc, p| {
                for (i, pr) in p {
                    if !self.semantics.contains_key(&i) {
                        let sem = self.deduce_semantic_of_production(pr);
                        acc = acc.and_then(|_| self.add_semantic(i, sem));
                    }
                }
                acc
            })?;
        Ok(())
    }

    fn deduce_in_type_of_production(prod: &Pr) -> ASTType {
        match prod.efficient_len() {
            0 => ASTType::Unit,
            1 => Self::deduce_type_of_symbol(&prod.get_r()[0]),
            _ => ASTType::Tuple(prod.get_r().iter().filter(|s| s.is_t() || s.is_n()).fold(
                Vec::new(),
                |mut acc, s| {
                    acc.push(Self::deduce_type_of_symbol(s));
                    acc
                },
            )),
        }
    }

    fn deduce_out_type_of_production(prod: &Pr) -> ASTType {
        match prod.efficient_len() {
            0 => ASTType::Unit,
            1 => ASTType::Tuple(vec![Self::deduce_type_of_symbol(&prod.get_r()[0])]),
            _ => ASTType::Tuple(prod.get_r().iter().filter(|s| s.is_t() || s.is_n()).fold(
                Vec::new(),
                |mut acc, s| {
                    acc.push(Self::deduce_type_of_symbol(s));
                    acc
                },
            )),
        }
    }

    fn deduce_semantic_of_production(&mut self, prod: &Pr) -> Semantic {
        let sem = prod.get_r().iter().fold(Vec::new(), |mut acc, s| {
            if self.is_collection(s) {
                acc.push(s.to_string());
            }
            acc
        });
        if sem.is_empty() {
            Semantic::None
        } else {
            Semantic::ReverseCollection(sem)
        }
    }

    fn deduce_type_of_symbol(symbol: &Symbol) -> ASTType {
        match symbol {
            Symbol::T(t) => ASTType::Token(t.to_string()),
            Symbol::N(n) => ASTType::TypeRef(n.to_string()),
            _ => {
                trace!("Returning Unit for symbol {}", symbol);
                ASTType::Unit
            }
        }
    }

    fn deduce_type_of_non_terminals(&mut self, cfg: &Cfg) -> Result<()> {
        cfg.get_non_terminal_set()
            .iter()
            .map(|nt| (nt, cfg.matching_productions(nt)))
            .fold(Ok(()), |mut acc, (n, prods)| {
                if prods.len() == 1 {
                    acc = acc.and_then(|_| {
                        self.add_non_terminal_type(
                            n,
                            Self::deduce_out_type_of_production(prods[0].1),
                        )
                    });
                } else {
                    let option_type = if prods.len() == 2 {
                        match (
                            self.in_types.get(&prods[0].0),
                            self.in_types.get(&prods[1].0),
                        ) {
                            (Some(ASTType::Option(n)), _) => Some(ASTType::Option(n.clone())),
                            (_, Some(ASTType::Option(n))) => Some(ASTType::Option(n.clone())),
                            _ => None,
                        }
                    } else {
                        None
                    };

                    if let Some(option_type) = option_type {
                        acc = acc.and_then(|_| self.add_non_terminal_type(n, option_type));
                    } else {
                        let repetition_type = if prods.len() == 2 {
                            match (
                                self.semantics.get(&prods[0].0),
                                self.semantics.get(&prods[1].0),
                            ) {
                                (Some(Semantic::StartCollection), _) => {
                                    let mut pr = prods[1].1.clone();
                                    let _ = pr.1.pop();
                                    Some(ASTType::Repeat(
                                        pr.get_r().iter().filter(|s| s.is_t() || s.is_n()).fold(
                                            Vec::new(),
                                            |mut acc, s| {
                                                acc.push(Self::deduce_type_of_symbol(s));
                                                acc
                                            },
                                        ),
                                    ))
                                }
                                (_, Some(Semantic::StartCollection)) => {
                                    let mut pr = prods[0].1.clone();
                                    let _ = pr.1.pop();
                                    Some(ASTType::Repeat(
                                        pr.get_r().iter().filter(|s| s.is_t() || s.is_n()).fold(
                                            Vec::new(),
                                            |mut acc, s| {
                                                acc.push(Self::deduce_type_of_symbol(s));
                                                acc
                                            },
                                        ),
                                    ))
                                }
                                _ => None,
                            }
                        } else {
                            None
                        };

                        if let Some(repetition_type) = repetition_type {
                            acc = acc.and_then(|_| self.add_non_terminal_type(n, repetition_type));
                        } else {
                            acc = acc.and_then(|_| {
                                self.add_non_terminal_type(
                                    n,
                                    ASTType::Enum(
                                        n.to_owned(),
                                        prods
                                            .iter()
                                            .map(|pr| Self::deduce_out_type_of_production(pr.1))
                                            .collect::<Vec<ASTType>>(),
                                    ),
                                )
                            });
                        }
                    }
                }
                acc
            })?;
        Ok(())
    }

    fn is_collection(&mut self, s: &Symbol) -> bool {
        match s {
            Symbol::N(n) => matches!(self.non_terminal_types.get(n), Some(ASTType::Repeat(_))),
            _ => false,
        }
    }
}

impl Display for GrammarTypeSystem {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::result::Result<(), Error> {
        let width = (self.in_types.len() as f32).log10() as usize + 1;
        for (prod_num, in_type) in &self.in_types {
            let out_type = self.out_types.get(prod_num).unwrap_or(&ASTType::None);
            let sem = self.semantics.get(prod_num).unwrap_or(&Semantic::None);
            writeln!(
                f,
                "/* {:w$} */ ({} -> {})  {{ {} }}",
                prod_num,
                in_type,
                out_type,
                sem,
                w = width
            )?;
        }
        writeln!(f)?;
        for (non_terminal, ast_type) in &self.non_terminal_types {
            writeln!(f, "{} ->  {}", non_terminal, ast_type)?;
        }
        Ok(())
    }
}

impl TryFrom<&Cfg> for GrammarTypeSystem {
    type Error = miette::Error;
    fn try_from(cfg: &Cfg) -> Result<Self> {
        let mut me = Self::new();
        me.add_pairwise_types(cfg)?;
        me.add_other_types(cfg)?;
        me.deduce_type_of_non_terminals(cfg)?;
        me.deduce_semantics(cfg)?;
        Ok(me)
    }
}

#[cfg(test)]
mod tests {
    use super::GrammarTypeSystem;
    use crate::grammar::SemanticInfo;
    use crate::{Cfg, Pr, Symbol};
    use std::convert::TryInto;
    use std::sync::Once;

    static INIT: Once = Once::new();

    fn setup() {
        INIT.call_once(env_logger::init);
    }

    fn t(t: &str) -> Symbol {
        Symbol::t(t, vec![0])
    }

    fn n(n: &str) -> Symbol {
        Symbol::n(n)
    }

    fn c(r: &str) -> Symbol {
        Symbol::Pseudo(SemanticInfo::CollectionStart(r.to_owned()))
    }

    fn o(r: &str) -> Symbol {
        Symbol::Pseudo(SemanticInfo::OptionalNone(r.to_owned()))
    }

    #[test]
    fn type_creation_repeat_1() {
        setup();

        // S: "a" {"b-rpt"} "c" {"d-rpt"};

        // /* 0 */ S: "a" SList "c" SList1;
        // /* 1 */ SList1: "d-rpt" SList1;
        // /* 2 */ SList1: /* Vec<SList1>::New */;
        // /* 3 */ SList: "b-rpt" SList;
        // /* 4 */ SList: /* Vec<SList>::New */;

        let g = Cfg::with_start_symbol("S")
            .add_pr(Pr::new("S", vec![t("a"), n("SList"), t("c"), n("SList1")]))
            .add_pr(Pr::new("SList1", vec![t("d-rpt"), n("SList1")]))
            .add_pr(Pr::new("SList1", vec![c("SList1")]))
            .add_pr(Pr::new("SList", vec![t("b-rpt"), n("SList")]))
            .add_pr(Pr::new("SList", vec![c("SList")]));

        let type_system: GrammarTypeSystem = (&g).try_into().unwrap();
        println!("{}", type_system);
    }

    #[test]
    fn type_creation_optional_1() {
        setup();

        // S: "a" ["b-opt"] "c" ["d-opt"];

        // /* 0 */ S: "a" SSuffix2;
        // /* 1 */ SSuffix2: /* Option<SOpt>::None */ "c" SSuffix1;
        // /* 2 */ SSuffix2: SOpt "c" SSuffix;
        // /* 3 */ SSuffix1: SOpt1;
        // /* 4 */ SSuffix1: /* Option<SOpt2>::None */;
        // /* 5 */ SSuffix: SOpt1;
        // /* 6 */ SSuffix: /* Option<SOpt1>::None */;
        // /* 7 */ SOpt1: "d-opt";
        // /* 8 */ SOpt: "b-opt";

        let g = Cfg::with_start_symbol("S")
            .add_pr(Pr::new("S", vec![t("a"), n("SSuffix2")]))
            .add_pr(Pr::new("SSuffix2", vec![o("SOpt"), t("c"), n("SSuffix1")]))
            .add_pr(Pr::new("SSuffix2", vec![n("SOpt"), t("c"), n("SSuffix")]))
            .add_pr(Pr::new("SSuffix1", vec![n("SOpt1")]))
            .add_pr(Pr::new("SSuffix1", vec![o("SOpt2")]))
            .add_pr(Pr::new("SSuffix", vec![n("SOpt1")]))
            .add_pr(Pr::new("SSuffix", vec![o("SOpt1")]))
            .add_pr(Pr::new("SOpt1", vec![t("d-opt")]))
            .add_pr(Pr::new("SOpt", vec![t("b-opt")]));

        let type_system: GrammarTypeSystem = (&g).try_into().unwrap();
        println!("{}", type_system);
    }
}
