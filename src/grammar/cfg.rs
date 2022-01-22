use crate::{Pos, Pr, Symbol, Terminal};
use regex::Regex;
use std::collections::HashSet;
use std::collections::{BTreeMap, BTreeSet};
use std::ops::Index;

lazy_static! {
    pub(crate) static ref RX_NUM_SUFFIX: Regex =
        Regex::new(r"[0-9]+$").expect("error parsing regex");
}

// ---------------------------------------------------
// Part of the Public API
// *Changes will affect crate's version according to semver*
// ---------------------------------------------------
///
/// WrapErr free grammar type
///
#[derive(Debug, Default, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub struct Cfg {
    /// Start symbol of the grammar
    pub st: String,
    /// Set of productions
    pub pr: Vec<Pr>,
}

impl Cfg {
    /// Returns the start symbol of the grammar
    pub fn get_start_symbol(&self) -> &str {
        &self.st
    }

    /// Creates a new item with the given start symbol
    pub fn with_start_symbol(n: &str) -> Self {
        Self {
            st: n.to_owned(),
            ..Default::default()
        }
    }

    /// Adds a production
    pub fn add_pr(mut self, p: Pr) -> Self {
        self.pr.push(p);
        self
    }

    /// Returns the grammar position of the start symbol
    pub fn get_start_symbol_position(&self) -> Option<Pos> {
        self.pr
            .iter()
            .position(|p| p.get_n_str() == self.st)
            .map(|i| (i, 0).into())
    }

    ///
    /// Set of Non-terminals, ordered alphabetically.
    ///
    pub fn get_non_terminal_set(&self) -> BTreeSet<String> {
        let mut set = BTreeSet::new();
        set.insert(self.st.clone());
        self.pr.iter().fold(set, |mut acc, p| {
            acc.insert(p.get_n());
            acc = p.get_r().iter().fold(acc, |mut acc, s| {
                if let Symbol::N(n) = s {
                    acc.insert(n.clone());
                }
                acc
            });
            acc
        })
    }

    ///
    /// Set of Non-terminals, ordered by occurrence
    /// Start symbol comes first
    ///
    pub fn get_non_terminal_ordering(&self) -> Vec<(String, Pos)> {
        let vec = vec![(
            self.st.clone(),
            self.get_start_symbol_position()
                .expect("Start symbol not found in any production"),
        )];
        self.pr.iter().enumerate().fold(vec, |mut acc, (pi, p)| {
            let pos = (pi, 0).into();
            if !acc.contains(&(p.get_n(), pos)) {
                acc.push((p.get_n(), pos));
            }
            acc = p.get_r().iter().enumerate().fold(acc, |mut acc, (si, s)| {
                let pos = (pi, si + 1).into();
                if let Symbol::N(n) = s {
                    let entry = (n.clone(), pos);
                    if !acc.contains(&entry) {
                        acc.push(entry);
                    }
                }
                acc
            });
            acc
        })
    }

    ///
    /// Set of Terminals - ordered by occurrence.
    /// Used for Lexer generation.
    ///
    pub fn get_ordered_terminals(&self) -> Vec<(&str, Vec<usize>)> {
        self.pr.iter().fold(Vec::new(), |mut acc, p| {
            acc = p.get_r().iter().fold(acc, |mut acc, s| {
                if let Symbol::T(Terminal::Trm(t, s)) = s {
                    if let Some(pos) = acc.iter_mut().position(|(trm, _)| trm == t) {
                        for st in s {
                            if !acc[pos].1.contains(st) {
                                acc[pos].1.push(*st);
                            }
                        }
                    } else {
                        acc.push((t, s.to_vec()));
                    }
                }
                acc
            });
            acc
        })
    }

    ///
    /// Terminal positions within the grammar
    /// Used for Nt grammar graphs
    ///
    pub fn get_terminal_positions(&self) -> BTreeMap<Pos, &Symbol> {
        self.pr
            .iter()
            .enumerate()
            .fold(BTreeMap::new(), |mut acc, (pi, p)| {
                acc = p.get_r().iter().enumerate().fold(acc, |mut acc, (si, s)| {
                    if matches!(s, Symbol::T(Terminal::Trm(_, _)))
                        || matches!(s, Symbol::T(Terminal::End))
                    {
                        acc.insert(Pos::new(pi, si + 1), s);
                    }
                    acc
                });
                acc
            })
    }

    ///
    /// Non-terminal positions within the grammar
    /// Used for Nt grammar graphs
    ///
    pub fn get_non_terminal_positions(&self) -> BTreeMap<Pos, String> {
        self.pr
            .iter()
            .enumerate()
            .fold(BTreeMap::new(), |mut acc, (pi, p)| {
                acc.insert(Pos::new(pi, 0), p.get_n());
                acc = p.get_r().iter().enumerate().fold(acc, |mut acc, (si, s)| {
                    if let Symbol::N(n) = s {
                        acc.insert(Pos::new(pi, si + 1), n.clone());
                    }
                    acc
                });
                acc
            })
    }

    ///
    /// Returns a vector of production references with the LHS matching the given non-terminal n
    ///
    pub fn matching_productions(&self, n: &str) -> Vec<(usize, &Pr)> {
        self.pr
            .iter()
            .enumerate()
            .fold(Vec::new(), |mut acc, (i, p)| {
                if p.get_n() == n {
                    acc.push((i, p));
                }
                acc
            })
    }

    ///
    /// Calculates all nullable non-terminals.
    ///
    /// ```
    /// use parol::{Cfg, Pr, Symbol};
    /// use std::collections::BTreeSet;
    /// use std::convert::From;
    ///
    /// let g = Cfg::with_start_symbol("S")
    ///     .add_pr(Pr::new("S", vec![Symbol::n("Y")]))
    ///     .add_pr(Pr::new("Y", vec![Symbol::n("U"), Symbol::n("Z")]))
    ///     .add_pr(Pr::new("Y", vec![Symbol::n("X"), Symbol::t("a", vec![0])]))
    ///     .add_pr(Pr::new("Y", vec![Symbol::t("b", vec![0])]))
    ///     .add_pr(Pr::new("U", vec![Symbol::n("V")]))
    ///     .add_pr(Pr::new("U", vec![]))
    ///     .add_pr(Pr::new("X", vec![Symbol::t("c", vec![0])]))
    ///     .add_pr(Pr::new("V", vec![Symbol::n("V"), Symbol::t("d", vec![0])]))
    ///     .add_pr(Pr::new("V", vec![Symbol::t("d", vec![0])]))
    ///     .add_pr(Pr::new("Z", vec![]))
    ///     .add_pr(Pr::new("Z", vec![Symbol::n("Z"), Symbol::n("X")]));
    /// let productive = g.calculate_nullable_non_terminals();
    /// assert_eq!(
    ///     [
    ///         "S".to_owned(),
    ///         "U".to_owned(),
    ///         "Y".to_owned(),
    ///         "Z".to_owned()
    ///     ].iter().cloned().collect::<BTreeSet<String>>(),
    ///     productive);
    /// ```
    ///
    pub fn calculate_nullable_non_terminals(&self) -> BTreeSet<String> {
        fn initial_nullables(cfg: &Cfg, vars: &[String]) -> HashSet<String> {
            vars.iter()
                .filter(|v| {
                    cfg.matching_productions(v)
                        .iter()
                        .any(|(_, p)| p.is_empty())
                })
                .map(<String as Clone>::clone)
                .collect()
        }

        fn collect_nullables(cfg: &Cfg, nullables: &mut HashSet<String>, vars: &[String]) -> bool {
            fn has_nullable_alt(prods: Vec<&Pr>, nullables: &HashSet<String>) -> bool {
                fn is_already_nullable(s: &Symbol, nullables: &HashSet<String>) -> bool {
                    match s {
                        Symbol::N(n) => nullables.contains(n),
                        _ => false,
                    }
                }

                prods
                    .iter()
                    .any(|p| p.get_r().iter().all(|s| is_already_nullable(s, nullables)))
            }
            let start_len = nullables.len();

            for v in vars {
                let v_prods = cfg
                    .matching_productions(v)
                    .into_iter()
                    .map(|(_, p)| p)
                    .collect();
                if has_nullable_alt(v_prods, nullables) {
                    nullables.insert(v.clone());
                }
            }

            start_len < nullables.len()
        }

        let vars = self
            .get_non_terminal_ordering()
            .into_iter()
            .map(|(n, _)| n)
            .collect::<Vec<String>>();
        let mut nullables = initial_nullables(self, &vars);

        while collect_nullables(self, &mut nullables, &vars) {}

        let mut nullables_vec = BTreeSet::new();
        for n in nullables.drain() {
            nullables_vec.insert(n);
        }
        nullables_vec
    }
}

impl Index<usize> for Cfg {
    type Output = Pr;

    fn index(&self, idx: usize) -> &Self::Output {
        &self.pr[idx]
    }
}

impl Index<&Pos> for Cfg {
    type Output = Symbol;

    fn index(&self, pos: &Pos) -> &Self::Output {
        &self.pr[pos.pr_index()][pos.sy_index()]
    }
}

#[cfg(test)]
mod test {
    use crate::{Cfg, Pr, Symbol};

    #[test]
    fn check_serialization() {
        let g = Cfg::with_start_symbol("S")
            .add_pr(Pr::new("S", vec![Symbol::t("a", vec![0]), Symbol::n("X")]))
            .add_pr(Pr::new("X", vec![Symbol::t("b", vec![0]), Symbol::n("S")]))
            .add_pr(Pr::new(
                "X",
                vec![
                    Symbol::t("a", vec![0]),
                    Symbol::n("Y"),
                    Symbol::t("b", vec![0]),
                    Symbol::n("Y"),
                ],
            ))
            .add_pr(Pr::new(
                "Y",
                vec![Symbol::t("b", vec![0]), Symbol::t("a", vec![0])],
            ))
            .add_pr(Pr::new("Y", vec![Symbol::t("a", vec![0]), Symbol::n("Z")]))
            .add_pr(Pr::new(
                "Z",
                vec![Symbol::t("a", vec![0]), Symbol::n("Z"), Symbol::n("X")],
            ));

        let serialized = serde_json::to_string(&g).unwrap();
        println!("{}", serialized);
        let g1: Cfg = serde_json::from_str(&serialized).unwrap();
        assert_eq!(g, g1);
    }
}
