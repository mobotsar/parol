/// Module with functions to convert between different identifier formats
pub mod case_helpers;

/// Module with type GrammarConfig
pub mod grammar_config;
pub use grammar_config::GrammarConfig;

/// Module with type ScannerConfig
pub mod scanner_config;
pub use scanner_config::ScannerConfig;

/// Module with grammar transformations
pub mod grammar_trans;
pub use grammar_trans::check_and_transform_grammar;

/// Module with the language generator
pub mod language_generator;
pub use language_generator::LanguageGenerator;

/// Module with the lexer generator
pub mod lexer_generator;
pub use lexer_generator::{generate_lexer_source, generate_terminal_names};

/// Module with the parser generator
pub mod parser_generator;
pub use parser_generator::generate_parser_source;

/// Module with the user-trait generator
pub mod user_trait_generator;
pub use user_trait_generator::generate_user_trait_source;

/// Module with the code formatting function
pub mod rust_code_formatter;
pub use rust_code_formatter::try_format;

/// Module with the terminal name generator
pub mod terminal_name_generator;
pub use terminal_name_generator::generate_terminal_name;
