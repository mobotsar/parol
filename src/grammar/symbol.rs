use crate::analysis::k_tuple::TerminalMappings;
use crate::parser::parol_grammar::Factor;
use crate::parser::to_grammar_config::try_from_factor;
use parol_runtime::parser::ScannerIndex;
use std::convert::TryFrom;
use std::fmt::{Debug, Display, Error, Formatter};

// ---------------------------------------------------
// Part of the Public API
// *Changes will affect crate's version according to semver*
// ---------------------------------------------------
///
/// A factor only introduced during grammar transformation
/// For auto-generation we need some information of types which normally get lost during
/// grammar transformation. This SemanticInfo is used to convey the information across multiple
/// transformation steps.
///
#[derive(Debug, Clone, Hash, Eq, PartialEq, Serialize, Deserialize)]
pub enum SemanticInfo {
    /// An Start-Of-Repetition with a type reference (production name)
    CollectionStart(String),
    /// An Push-To-Repetition with a type reference (production name)
    // CollectionPush(String),
    /// An Optional::Some case with a type reference (production name)
    // OptionalSome(String),
    /// An Optional::None case with a type reference (production name)
    OptionalNone(String),
}

impl Display for SemanticInfo {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::result::Result<(), Error> {
        match self {
            Self::CollectionStart(r) => write!(f, "Vec<{}>::New", r),
            // Self::CollectionPush(r) => write!(f, "Vec<{}>::Push", r),
            // Self::OptionalSome(o) => write!(f, "Option<{}>::Some", o),
            Self::OptionalNone(o) => write!(f, "Option<{}>::None", o),
        }
    }
}

// ---------------------------------------------------
// Part of the Public API
// *Changes will affect crate's version according to semver*
// ---------------------------------------------------
///
/// A terminal symbol with different specificities
///
#[derive(Debug, Clone, Hash, Eq, PartialEq, Serialize, Deserialize)]
pub enum Terminal {
    ///
    /// A physical terminal symbol with the scanner states it belongs to
    /// Entities that are provided by the lexer.
    ///
    Trm(String, Vec<usize>),

    ///
    /// Epsilon symbol, the empty word
    /// Can be contained in FIRST sets
    /// Cannot be contained in productions of our definition of grammar -
    /// epsilon productions are simply empty.
    ///
    Eps,

    ///
    /// End of input symbol, End of grammar symbol (not belonging to any grammar)
    ///
    End,
}

impl Terminal {
    /// Creates a terminal
    pub fn t(t: &str, s: Vec<usize>) -> Self {
        Self::Trm(t.to_owned(), s)
    }
    /// Checks if self is a terminal
    pub fn is_trm(&self) -> bool {
        matches!(self, Self::Trm(_, _))
    }
    /// Checks if self is an epsilon
    pub fn is_eps(&self) -> bool {
        matches!(self, Self::Eps)
    }
    /// Checks if self is an end of input terminal
    pub fn is_end(&self) -> bool {
        matches!(self, Self::End)
    }

    /// Creates a terminal from a [Symbol]
    pub fn create(s: &Symbol) -> Self {
        match s {
            Symbol::T(Terminal::Trm(t, s)) => Terminal::Trm(t.to_string(), s.to_vec()),
            Symbol::T(Terminal::End) => Terminal::End,
            _ => panic!("Unexpected symbol type: {:?}", s),
        }
    }

    /// Adds a scanner index
    pub fn add_scanner(&mut self, sc: usize) {
        match self {
            Terminal::Trm(_, s) => {
                if !s.contains(&sc) {
                    s.push(sc);
                    s.sort_unstable();
                }
            }
            _ => panic!("Unexpected symbol type: {:?}", self),
        }
    }

    ///
    /// Formats self with the help of a scanner state resolver
    ///
    pub fn format<R>(&self, scanner_state_resolver: R) -> String
    where
        R: Fn(&[usize]) -> String,
    {
        match self {
            Self::Trm(t, s) => {
                if *s == vec![0] {
                    // Don't print state if terminal is only in state INITIAL (0)
                    format!("\"{}\"", t)
                } else {
                    format!("<{}>\"{}\"", scanner_state_resolver(s), t)
                }
            }
            Self::Eps => "\u{03B5}".to_string(), // Lower creek letter Epsilon (ε)
            Self::End => "$".to_string(),
        }
    }
}

impl Display for Terminal {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        match self {
            Self::Trm(t, _) => write!(f, "\"{}\"", t),
            Self::Eps => write!(f, "\u{03B5}"), // Lower creek letter Epsilon (ε)
            Self::End => write!(f, "$"),
        }
    }
}

impl TerminalMappings<Terminal> for Terminal {
    fn eps() -> Terminal {
        Self::Eps
    }

    fn end() -> Terminal {
        Self::End
    }

    fn is_eps(&self) -> bool {
        self.is_eps()
    }

    fn is_end(&self) -> bool {
        self.is_end()
    }
}

// ---------------------------------------------------
// Part of the Public API
// *Changes will affect crate's version according to semver*
// ---------------------------------------------------
///
/// A grammar symbol with different specificities
///
#[derive(Debug, Clone, Hash, Eq, PartialEq, Serialize, Deserialize)]
pub enum Symbol {
    ///
    /// Non-terminal symbol, Meta symbol of the grammar.
    ///
    N(String),

    ///
    /// Terminal symbol of the grammar.
    ///
    T(Terminal),

    ///
    /// Instruction to switch scanner state
    ///
    S(ScannerIndex),

    ///
    /// Instruction to push the index of the current scanner and switch to a scanner configuration
    /// with the given index
    ///
    Push(ScannerIndex),

    ///
    /// Instruction to pop the index of the scanner pushed before and switch to the scanner
    /// configuration with that index
    ///
    Pop,

    ///
    /// Used to preserve type information
    ///
    Pseudo(SemanticInfo),
}

impl Symbol {
    /// Creates a terminal symbol
    pub fn t(t: &str, s: Vec<usize>) -> Self {
        Self::T(Terminal::Trm(t.to_owned(), s))
    }
    /// Creates a non-terminal symbol
    pub fn n(n: &str) -> Self {
        Self::N(n.to_owned())
    }
    /// Creates a end-of-input terminal symbol
    pub fn e() -> Self {
        Self::T(Terminal::End)
    }
    /// Creates a scanner index
    pub fn s(s: usize) -> Self {
        Self::S(s)
    }
    /// Checks if self is a terminal
    pub fn is_t(&self) -> bool {
        matches!(self, Self::T(_))
    }
    /// Checks if self is a non-terminal
    pub fn is_n(&self) -> bool {
        matches!(self, Self::N(_))
    }
    /// Checks if self is a end-of-input terminal
    pub fn is_end(&self) -> bool {
        matches!(self, Self::T(Terminal::End))
    }
    /// Checks if self is a scanner switch instruction
    pub fn is_switch(&self) -> bool {
        matches!(self, Self::S(_)) || matches!(self, Self::Push(_)) || matches!(self, Self::Pop)
    }
    /// Checks if self is a pseudo symbol
    pub fn is_pseudo(&self) -> bool {
        matches!(self, Self::Pseudo(_))
    }
    /// Returns a terminal if available
    pub fn get_t(&self) -> Option<Terminal> {
        if let Self::T(t) = &self {
            Some(t.clone())
        } else {
            None
        }
    }
    /// Returns a terminal reference if available
    pub fn get_t_ref(&self) -> Option<&Terminal> {
        if let Self::T(t) = &self {
            Some(t)
        } else {
            None
        }
    }
    /// Returns a non-terminal if available
    pub fn get_n(&self) -> Option<String> {
        if let Self::N(n) = &self {
            Some(n.clone())
        } else {
            None
        }
    }
    /// Returns a non-terminal reference if available
    pub fn get_n_ref(&self) -> Option<&String> {
        if let Self::N(n) = &self {
            Some(n)
        } else {
            None
        }
    }

    /// Formats self with the help of a scanner state resolver
    pub fn format<R>(&self, scanner_state_resolver: &R) -> String
    where
        R: Fn(&[usize]) -> String,
    {
        match self {
            Self::N(n) => n.to_string(),
            Self::T(t) => t.format(scanner_state_resolver),
            Self::S(s) => {
                if *s == 0 {
                    "%sc()".to_string()
                } else {
                    format!("%sc({})", scanner_state_resolver(&[*s]))
                }
            }
            Self::Push(s) => format!("%push({})", scanner_state_resolver(&[*s])),
            Self::Pop => "%pop()".to_string(),
            Self::Pseudo(p) => format!("/* {} */", p),
        }
    }
}

impl Display for Symbol {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        match self {
            Self::N(n) => write!(f, "{}", n),
            Self::T(t) => write!(f, "{}", t),
            Self::S(s) => write!(f, "S({})", s),
            Self::Push(s) => write!(f, "Push({})", s),
            Self::Pop => write!(f, "Pop"),
            Self::Pseudo(p) => write!(f, "{}", p),
        }
    }
}

impl TryFrom<Factor> for Symbol {
    type Error = miette::Error;
    fn try_from(factor: Factor) -> miette::Result<Self> {
        try_from_factor(factor)
    }
}
