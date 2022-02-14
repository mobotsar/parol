use std::fmt::{Debug, Display, Error, Formatter};

/// Used to decorate an object's printed format
pub trait Decorate<T>
where
    T: Display,
{
    /// Function used for decorated formatting
    fn decorate(&self, decoratee: &T) -> String;
}

///
/// Attributes applicable to a production or an alternation
///
#[derive(Debug, Clone, Hash, PartialEq, Eq, Serialize, Deserialize)]
pub enum ProductionAttribute {
    /// No valid attribute, default value
    None,
    /// Indicates a start of repetition, i.e. a collections
    CollectionStart,
    /// Add to a collection
    AddToCollection,
}

impl Display for ProductionAttribute {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::result::Result<(), Error> {
        match self {
            Self::None => write!(f, "-"),
            Self::CollectionStart => write!(f, "Vec<T>::New"),
            Self::AddToCollection => write!(f, "Vec<T>::Push"),
        }
    }
}

impl Default for ProductionAttribute {
    fn default() -> Self {
        Self::None
    }
}

impl<T> Decorate<T> for ProductionAttribute
where
    T: Display,
{
    fn decorate(&self, decoratee: &T) -> String {
        match self {
            Self::None => format!("{}", decoratee),
            Self::CollectionStart => format!("{} // Vec<T>::New", decoratee),
            Self::AddToCollection => format!("{} // Vec<T>::Push", decoratee),
        }
    }
}

///
/// Attributes applicable to a grammar symbol
///
#[derive(Debug, Clone, Hash, PartialEq, Eq, Serialize, Deserialize)]
pub enum SymbolAttribute {
    /// No valid attribute, default value
    None,

    /// An Optional::Some case with a type reference (non-terminal name)
    /// Is attached to a non-terminal symbol which shall be typed as option type.
    OptionalSome,

    /// An Optional::None case with a type reference (non-terminal name)
    /// Is attached to a Pseudo symbol.
    OptionalNone(String),

    /// The symbol is actually a collection, i.e. a vector
    /// Is attached to a non-terminal symbol which shall be typed as collection type.
    /// If an argument with this attribute appears in the argument list of a semantic action
    /// this collection should be reversed.
    Repetition,
}

impl Display for SymbolAttribute {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::result::Result<(), Error> {
        match self {
            Self::None => Ok(()),
            Self::OptionalSome => write!(f, "Option<T>::Some"),
            Self::OptionalNone(o) => write!(f, "Option<{}>::None", o),
            Self::Repetition => write!(f, "Vec<T>"),
        }
    }
}

impl Default for SymbolAttribute {
    fn default() -> Self {
        Self::None
    }
}

impl<T> Decorate<T> for SymbolAttribute
where
    T: Display,
{
    fn decorate(&self, decoratee: &T) -> String {
        match self {
            Self::None => format!("{}", decoratee),
            Self::OptionalSome => format!("{} /* Option::Some */", decoratee),
            Self::OptionalNone(o) => format!("{}: Optional<{}>::None", decoratee, o),
            Self::Repetition => format!("{} /* Vec */", decoratee),
        }
    }
}
