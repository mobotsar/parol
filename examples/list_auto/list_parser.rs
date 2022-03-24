// ---------------------------------------------------------
// This file was generated by parol.
// It is not intended for manual editing and changes will be
// lost after next build.
// ---------------------------------------------------------

use id_tree::Tree;
use miette::Result;
use parol_runtime::lexer::{TokenStream, Tokenizer};
use parol_runtime::parser::{
    DFATransition, LLKParser, LookaheadDFA, ParseTreeType, ParseType, Production,
};
use std::cell::RefCell;
use std::path::Path;

use crate::list_grammar::ListGrammar;
use crate::list_grammar_trait::ListGrammarAuto;

use parol_runtime::lexer::tokenizer::{
    ERROR_TOKEN, NEW_LINE_TOKEN, UNMATCHABLE_TOKEN, WHITESPACE_TOKEN,
};

pub const TERMINALS: &[&str; 8] = &[
    /* 0 */ UNMATCHABLE_TOKEN,
    /* 1 */ UNMATCHABLE_TOKEN,
    /* 2 */ UNMATCHABLE_TOKEN,
    /* 3 */ UNMATCHABLE_TOKEN,
    /* 4 */ UNMATCHABLE_TOKEN,
    /* 5 */ r###","###,
    /* 6 */ r###"0|[1-9][0-9]*"###,
    /* 7 */ ERROR_TOKEN,
];

pub const TERMINAL_NAMES: &[&str; 8] = &[
    /* 0 */ "EndOfInput",
    /* 1 */ "Newline",
    /* 2 */ "Whitespace",
    /* 3 */ "LineComment",
    /* 4 */ "BlockComment",
    /* 5 */ "Comma",
    /* 6 */ "Num",
    /* 7 */ "Error",
];

/* SCANNER_0: "INITIAL" */
const SCANNER_0: (&[&str; 5], &[usize; 2]) = (
    &[
        /* 0 */ UNMATCHABLE_TOKEN,
        /* 1 */ NEW_LINE_TOKEN,
        /* 2 */ WHITESPACE_TOKEN,
        /* 3 */ UNMATCHABLE_TOKEN,
        /* 4 */ UNMATCHABLE_TOKEN,
    ],
    &[5 /* Comma */, 6 /* Num */],
);

const MAX_K: usize = 2;

pub const NON_TERMINALS: &[&str; 4] = &[
    /* 0 */ "List",
    /* 1 */ "ListList",
    /* 2 */ "Num",
    /* 3 */ "TrailingComma",
];

pub const LOOKAHEAD_AUTOMATA: &[LookaheadDFA; 4] = &[
    /* 0 - "List" */
    LookaheadDFA {
        states: &[None, Some(0), Some(3)],
        transitions: &[
            DFATransition(0, 0, 2),
            DFATransition(0, 5, 2),
            DFATransition(0, 6, 1),
        ],
        k: 1,
    },
    /* 1 - "ListList" */
    LookaheadDFA {
        states: &[None, None, Some(1), Some(2)],
        transitions: &[
            DFATransition(0, 0, 3),
            DFATransition(0, 5, 1),
            DFATransition(1, 0, 3),
            DFATransition(1, 6, 2),
        ],
        k: 2,
    },
    /* 2 - "Num" */
    LookaheadDFA {
        states: &[Some(4)],
        transitions: &[],
        k: 0,
    },
    /* 3 - "TrailingComma" */
    LookaheadDFA {
        states: &[None, Some(5), Some(6)],
        transitions: &[DFATransition(0, 0, 2), DFATransition(0, 5, 1)],
        k: 1,
    },
];

pub const PRODUCTIONS: &[Production; 7] = &[
    // 0 - List: Num ListList /* Vec */ TrailingComma;
    Production {
        lhs: 0,
        production: &[ParseType::N(3), ParseType::N(1), ParseType::N(2)],
    },
    // 1 - ListList: "," Num ListList;
    Production {
        lhs: 1,
        production: &[ParseType::N(1), ParseType::N(2), ParseType::T(5)],
    },
    // 2 - ListList: ;
    Production {
        lhs: 1,
        production: &[],
    },
    // 3 - List: TrailingComma;
    Production {
        lhs: 0,
        production: &[ParseType::N(3)],
    },
    // 4 - Num: "0|[1-9][0-9]*";
    Production {
        lhs: 2,
        production: &[ParseType::T(6)],
    },
    // 5 - TrailingComma: ",";
    Production {
        lhs: 3,
        production: &[ParseType::T(5)],
    },
    // 6 - TrailingComma: ;
    Production {
        lhs: 3,
        production: &[],
    },
];

lazy_static! {
    static ref TOKENIZERS: Vec<(&'static str, Tokenizer)> = vec![(
        "INITIAL",
        Tokenizer::build(TERMINALS, SCANNER_0.0, SCANNER_0.1).unwrap()
    ),];
}

pub fn parse<'t, T>(
    input: &'t str,
    file_name: T,
    user_actions: &mut ListGrammar,
) -> Result<Tree<ParseTreeType<'t>>>
where
    T: AsRef<Path>,
{
    let mut llk_parser = LLKParser::new(
        0,
        LOOKAHEAD_AUTOMATA,
        PRODUCTIONS,
        TERMINAL_NAMES,
        NON_TERMINALS,
    );
    let token_stream =
        RefCell::new(TokenStream::new(input, file_name, &TOKENIZERS, MAX_K).unwrap());
    // Initialize wrapper
    let mut user_actions = ListGrammarAuto::new(user_actions);
    let result = llk_parser.parse(token_stream, &mut user_actions);
    match result {
        Ok(()) => Ok(llk_parser.parse_tree),
        Err(e) => Err(e),
    }
}
