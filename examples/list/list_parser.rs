// ---------------------------------------------------------
// This file was generated by parol.
// It is not intended for manual editing and changes will be
// lost after next build.
// ---------------------------------------------------------

use parol_runtime::once_cell::sync::Lazy;
#[allow(unused_imports)]
use parol_runtime::parser::{
    LLKParser, LookaheadDFA, ParseTreeType, ParseType, Production, Trans, UserActionsTrait,
};
use parol_runtime::{ParolError, ParseTree, TerminalIndex};
use parol_runtime::{TokenStream, Tokenizer};
use std::cell::RefCell;
use std::path::Path;

use parol_runtime::lexer::tokenizer::{
    ERROR_TOKEN, NEW_LINE_TOKEN, UNMATCHABLE_TOKEN, WHITESPACE_TOKEN,
};

pub const TERMINALS: &[&str; 8] = &[
    /* 0 */ UNMATCHABLE_TOKEN,
    /* 1 */ UNMATCHABLE_TOKEN,
    /* 2 */ UNMATCHABLE_TOKEN,
    /* 3 */ UNMATCHABLE_TOKEN,
    /* 4 */ UNMATCHABLE_TOKEN,
    /* 5 */ r",",
    /* 6 */ r"0|[1-9][0-9]*",
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
const SCANNER_0: (&[&str; 5], &[TerminalIndex; 2]) = (
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

pub const NON_TERMINALS: &[&str; 6] = &[
    /* 0 */ "List",
    /* 1 */ "ListOpt",
    /* 2 */ "ListOpt0",
    /* 3 */ "ListRest",
    /* 4 */ "ListRestOpt",
    /* 5 */ "Num",
];

pub const LOOKAHEAD_AUTOMATA: &[LookaheadDFA; 6] = &[
    /* 0 - "List" */
    LookaheadDFA {
        prod0: 0,
        transitions: &[],
        k: 0,
    },
    /* 1 - "ListOpt" */
    LookaheadDFA {
        prod0: -1,
        transitions: &[Trans(0, 0, 2, 4), Trans(0, 6, 1, 1)],
        k: 1,
    },
    /* 2 - "ListOpt0" */
    LookaheadDFA {
        prod0: -1,
        transitions: &[Trans(0, 0, 2, 3), Trans(0, 5, 1, 2)],
        k: 1,
    },
    /* 3 - "ListRest" */
    LookaheadDFA {
        prod0: 5,
        transitions: &[],
        k: 0,
    },
    /* 4 - "ListRestOpt" */
    LookaheadDFA {
        prod0: -1,
        transitions: &[
            Trans(0, 0, 3, 7),
            Trans(0, 5, 1, -1),
            Trans(1, 0, 3, 7),
            Trans(1, 6, 2, 6),
        ],
        k: 2,
    },
    /* 5 - "Num" */
    LookaheadDFA {
        prod0: 8,
        transitions: &[],
        k: 0,
    },
];

pub const PRODUCTIONS: &[Production; 9] = &[
    // 0 - List: ListOpt /* Option */;
    Production {
        lhs: 0,
        production: &[ParseType::N(1)],
    },
    // 1 - ListOpt: Num ListRest ListOpt0 /* Option */;
    Production {
        lhs: 1,
        production: &[ParseType::N(2), ParseType::N(3), ParseType::N(5)],
    },
    // 2 - ListOpt0: ",";
    Production {
        lhs: 2,
        production: &[ParseType::T(5)],
    },
    // 3 - ListOpt0: ;
    Production {
        lhs: 2,
        production: &[],
    },
    // 4 - ListOpt: ;
    Production {
        lhs: 1,
        production: &[],
    },
    // 5 - ListRest: ListRestOpt /* Option */;
    Production {
        lhs: 3,
        production: &[ParseType::N(4)],
    },
    // 6 - ListRestOpt: "," Num ListRest;
    Production {
        lhs: 4,
        production: &[ParseType::N(3), ParseType::N(5), ParseType::T(5)],
    },
    // 7 - ListRestOpt: ;
    Production {
        lhs: 4,
        production: &[],
    },
    // 8 - Num: "0|[1-9][0-9]*";
    Production {
        lhs: 5,
        production: &[ParseType::T(6)],
    },
];

static TOKENIZERS: Lazy<Vec<(&'static str, Tokenizer)>> = Lazy::new(|| {
    vec![(
        "INITIAL",
        Tokenizer::build(TERMINALS, SCANNER_0.0, SCANNER_0.1).unwrap(),
    )]
});

pub fn parse<'t, T>(
    input: &'t str,
    file_name: T,
    user_actions: &mut dyn UserActionsTrait<'t>,
) -> Result<ParseTree<'t>, ParolError>
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
    llk_parser.parse(token_stream, user_actions)
}
