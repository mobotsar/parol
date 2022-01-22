use crate::{Pr, Symbol};
use std::fmt::{Display, Error, Formatter};

///
/// Symbol strings are special collections of [Symbol]s.
/// They only contain symbol kinds relevant for operations on grammars.
/// Especially in contrast to [Rhs] of [Pr] productions they don't contain scanner state
/// instructions like %sc, %push and %pop.
///
#[derive(Debug, Clone, Default, Hash, Eq, PartialEq)]
pub(crate) struct SymbolString(pub Vec<Symbol>);

impl SymbolString {
    ///
    /// Construction from a given production
    ///
    pub fn from_production(pr: &Pr) -> Self {
        Self(
            pr.get_r()
                .iter()
                .fold(Vec::with_capacity(pr.len()), |mut acc, e| {
                    // Don't include scanner state switches into symbol string
                    if !e.is_switch() {
                        acc.push(e.clone())
                    }
                    acc
                }),
        )
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }
}

impl Display for SymbolString {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        write!(
            f,
            "{}",
            self.0
                .iter()
                .map(|e| format!("{}", e))
                .collect::<Vec<String>>()
                .join(", ")
        )
    }
}
