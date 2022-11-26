// ---------------------------------------------------------
// This file was generated by parol.
// It is not intended for manual editing and changes will be
// lost after next build.
// ---------------------------------------------------------

use parol_runtime::id_tree::Tree;
use parol_runtime::lexer::{TokenStream, Tokenizer};
use parol_runtime::miette::Result;
use parol_runtime::once_cell::sync::Lazy;
#[allow(unused_imports)]
use parol_runtime::parser::{
    DFATransition, LLKParser, LookaheadDFA, ParseTreeType, ParseType, Production,
};
use std::cell::RefCell;
use std::path::Path;

use crate::parol_ls_grammar::ParolLsGrammar;
use crate::parol_ls_grammar_trait::ParolLsGrammarAuto;

use parol_runtime::lexer::tokenizer::{
    ERROR_TOKEN, NEW_LINE_TOKEN, UNMATCHABLE_TOKEN, WHITESPACE_TOKEN,
};

pub const TERMINALS: &[&str; 40] = &[
    /*  0 */ UNMATCHABLE_TOKEN,
    /*  1 */ UNMATCHABLE_TOKEN,
    /*  2 */ UNMATCHABLE_TOKEN,
    /*  3 */ UNMATCHABLE_TOKEN,
    /*  4 */ UNMATCHABLE_TOKEN,
    /*  5 */ r###"%start"###,
    /*  6 */ r###"%title"###,
    /*  7 */ r###"%comment"###,
    /*  8 */ r###"%user_type"###,
    /*  9 */ r###"="###,
    /* 10 */ r###"%line_comment"###,
    /* 11 */ r###"%block_comment"###,
    /* 12 */ r###"%auto_newline_off"###,
    /* 13 */ r###"%auto_ws_off"###,
    /* 14 */ r###"%%"###,
    /* 15 */ r###"::"###,
    /* 16 */ r###":"###,
    /* 17 */ r###";"###,
    /* 18 */ r###"\|"###,
    /* 19 */ r###"<"###,
    /* 20 */ r###">"###,
    /* 21 */ r###"\("###,
    /* 22 */ r###"\)"###,
    /* 23 */ r###"\["###,
    /* 24 */ r###"\]"###,
    /* 25 */ r###"\{"###,
    /* 26 */ r###"\}"###,
    /* 27 */ r###"[a-zA-Z_][a-zA-Z0-9_]*"###,
    /* 28 */ r###"\u{22}(\\.|[^\\])*?\u{22}"###,
    /* 29 */ r###"'(\\'|[^'])*?'"###,
    /* 30 */ r###"%scanner"###,
    /* 31 */ r###","###,
    /* 32 */ r###"%sc"###,
    /* 33 */ r###"%push"###,
    /* 34 */ r###"%pop"###,
    /* 35 */ r###"\^"###,
    /* 36 */ r###"//.*(:?\r\n|\r|\n|$)"###,
    /* 37 */ r###"(?ms)/\u{2a}.*?\u{2a}/"###,
    /* 38 */ r###"/(\\/|[^/]|)*?/"###,
    /* 39 */ ERROR_TOKEN,
];

pub const TERMINAL_NAMES: &[&str; 40] = &[
    /*  0 */ "EndOfInput",
    /*  1 */ "Newline",
    /*  2 */ "Whitespace",
    /*  3 */ "LineComment",
    /*  4 */ "BlockComment",
    /*  5 */ "PercentStart",
    /*  6 */ "PercentTitle",
    /*  7 */ "PercentComment",
    /*  8 */ "PercentUserUnderscoreType",
    /*  9 */ "Equ",
    /* 10 */ "PercentLineUnderscoreComment",
    /* 11 */ "PercentBlockUnderscoreComment",
    /* 12 */ "PercentAutoUnderscoreNewlineUnderscoreOff",
    /* 13 */ "PercentAutoUnderscoreWsUnderscoreOff",
    /* 14 */ "PercentPercent",
    /* 15 */ "DoubleColon",
    /* 16 */ "Colon",
    /* 17 */ "Semicolon",
    /* 18 */ "Or",
    /* 19 */ "LT",
    /* 20 */ "GT",
    /* 21 */ "LParen",
    /* 22 */ "RParen",
    /* 23 */ "LBracket",
    /* 24 */ "RBracket",
    /* 25 */ "LBrace",
    /* 26 */ "RBrace",
    /* 27 */ "Identifier",
    /* 28 */ "String",
    /* 29 */ "LiteralString",
    /* 30 */ "PercentScanner",
    /* 31 */ "Comma",
    /* 32 */ "PercentSc",
    /* 33 */ "PercentPush",
    /* 34 */ "PercentPop",
    /* 35 */ "CutOperator",
    /* 36 */ "LineComment0",
    /* 37 */ "BlockComment0",
    /* 38 */ "Regex",
    /* 39 */ "Error",
];

/* SCANNER_0: "INITIAL" */
const SCANNER_0: (&[&str; 5], &[usize; 34]) = (
    &[
        /*  0 */ UNMATCHABLE_TOKEN,
        /*  1 */ NEW_LINE_TOKEN,
        /*  2 */ WHITESPACE_TOKEN,
        /*  3 */ UNMATCHABLE_TOKEN,
        /*  4 */ UNMATCHABLE_TOKEN,
    ],
    &[
        5,  /* PercentStart */
        6,  /* PercentTitle */
        7,  /* PercentComment */
        8,  /* PercentUserUnderscoreType */
        9,  /* Equ */
        10, /* PercentLineUnderscoreComment */
        11, /* PercentBlockUnderscoreComment */
        12, /* PercentAutoUnderscoreNewlineUnderscoreOff */
        13, /* PercentAutoUnderscoreWsUnderscoreOff */
        14, /* PercentPercent */
        15, /* DoubleColon */
        16, /* Colon */
        17, /* Semicolon */
        18, /* Or */
        19, /* LT */
        20, /* GT */
        21, /* LParen */
        22, /* RParen */
        23, /* LBracket */
        24, /* RBracket */
        25, /* LBrace */
        26, /* RBrace */
        27, /* Identifier */
        28, /* String */
        29, /* LiteralString */
        30, /* PercentScanner */
        31, /* Comma */
        32, /* PercentSc */
        33, /* PercentPush */
        34, /* PercentPop */
        35, /* CutOperator */
        36, /* LineComment0 */
        37, /* BlockComment0 */
        38, /* Regex */
    ],
);

const MAX_K: usize = 1;

pub const NON_TERMINALS: &[&str; 48] = &[
    /*  0 */ "ASTControl",
    /*  1 */ "Alternation",
    /*  2 */ "AlternationList",
    /*  3 */ "Alternations",
    /*  4 */ "AlternationsList",
    /*  5 */ "BlockComment",
    /*  6 */ "Comments",
    /*  7 */ "CommentsList",
    /*  8 */ "CommentsListGroup",
    /*  9 */ "CutOperator",
    /* 10 */ "Declaration",
    /* 11 */ "DoubleColon",
    /* 12 */ "Factor",
    /* 13 */ "GrammarDefinition",
    /* 14 */ "GrammarDefinitionList",
    /* 15 */ "Group",
    /* 16 */ "Identifier",
    /* 17 */ "LineComment",
    /* 18 */ "LiteralString",
    /* 19 */ "NonTerminal",
    /* 20 */ "NonTerminalOpt",
    /* 21 */ "Optional",
    /* 22 */ "ParolLs",
    /* 23 */ "Production",
    /* 24 */ "ProductionLHS",
    /* 25 */ "Prolog",
    /* 26 */ "PrologList",
    /* 27 */ "PrologList0",
    /* 28 */ "Regex",
    /* 29 */ "Repeat",
    /* 30 */ "ScannerDirectives",
    /* 31 */ "ScannerState",
    /* 32 */ "ScannerStateList",
    /* 33 */ "ScannerSwitch",
    /* 34 */ "ScannerSwitchOpt",
    /* 35 */ "SimpleToken",
    /* 36 */ "SimpleTokenOpt",
    /* 37 */ "StartDeclaration",
    /* 38 */ "StateList",
    /* 39 */ "StateListList",
    /* 40 */ "String",
    /* 41 */ "Symbol",
    /* 42 */ "TokenLiteral",
    /* 43 */ "TokenWithStates",
    /* 44 */ "TokenWithStatesOpt",
    /* 45 */ "UserTypeDeclaration",
    /* 46 */ "UserTypeName",
    /* 47 */ "UserTypeNameList",
];

pub const LOOKAHEAD_AUTOMATA: &[LookaheadDFA; 48] = &[
    /* 0 - "ASTControl" */
    LookaheadDFA {
        states: &[None, Some(64), Some(65)],
        transitions: &[DFATransition(0, 16, 2), DFATransition(0, 35, 1)],
        k: 1,
    },
    /* 1 - "Alternation" */
    LookaheadDFA {
        states: &[Some(24)],
        transitions: &[],
        k: 0,
    },
    /* 2 - "AlternationList" */
    LookaheadDFA {
        states: &[None, Some(25), Some(26)],
        transitions: &[
            DFATransition(0, 17, 2),
            DFATransition(0, 18, 2),
            DFATransition(0, 19, 1),
            DFATransition(0, 21, 1),
            DFATransition(0, 22, 2),
            DFATransition(0, 23, 1),
            DFATransition(0, 24, 2),
            DFATransition(0, 25, 1),
            DFATransition(0, 26, 2),
            DFATransition(0, 27, 1),
            DFATransition(0, 28, 1),
            DFATransition(0, 29, 1),
            DFATransition(0, 32, 1),
            DFATransition(0, 33, 1),
            DFATransition(0, 34, 1),
            DFATransition(0, 38, 1),
        ],
        k: 1,
    },
    /* 3 - "Alternations" */
    LookaheadDFA {
        states: &[Some(21)],
        transitions: &[],
        k: 0,
    },
    /* 4 - "AlternationsList" */
    LookaheadDFA {
        states: &[None, Some(22), Some(23)],
        transitions: &[
            DFATransition(0, 17, 2),
            DFATransition(0, 18, 1),
            DFATransition(0, 22, 2),
            DFATransition(0, 24, 2),
            DFATransition(0, 26, 2),
        ],
        k: 1,
    },
    /* 5 - "BlockComment" */
    LookaheadDFA {
        states: &[Some(77)],
        transitions: &[],
        k: 0,
    },
    /* 6 - "Comments" */
    LookaheadDFA {
        states: &[Some(71)],
        transitions: &[],
        k: 0,
    },
    /* 7 - "CommentsList" */
    LookaheadDFA {
        states: &[None, Some(72), Some(75)],
        transitions: &[
            DFATransition(0, 5, 2),
            DFATransition(0, 6, 2),
            DFATransition(0, 7, 2),
            DFATransition(0, 8, 2),
            DFATransition(0, 10, 2),
            DFATransition(0, 11, 2),
            DFATransition(0, 12, 2),
            DFATransition(0, 13, 2),
            DFATransition(0, 14, 2),
            DFATransition(0, 16, 2),
            DFATransition(0, 17, 2),
            DFATransition(0, 18, 2),
            DFATransition(0, 19, 2),
            DFATransition(0, 21, 2),
            DFATransition(0, 22, 2),
            DFATransition(0, 23, 2),
            DFATransition(0, 24, 2),
            DFATransition(0, 25, 2),
            DFATransition(0, 26, 2),
            DFATransition(0, 27, 2),
            DFATransition(0, 28, 2),
            DFATransition(0, 29, 2),
            DFATransition(0, 30, 2),
            DFATransition(0, 32, 2),
            DFATransition(0, 33, 2),
            DFATransition(0, 34, 2),
            DFATransition(0, 36, 1),
            DFATransition(0, 37, 1),
            DFATransition(0, 38, 2),
        ],
        k: 1,
    },
    /* 8 - "CommentsListGroup" */
    LookaheadDFA {
        states: &[None, Some(73), Some(74)],
        transitions: &[DFATransition(0, 36, 1), DFATransition(0, 37, 2)],
        k: 1,
    },
    /* 9 - "CutOperator" */
    LookaheadDFA {
        states: &[Some(66)],
        transitions: &[],
        k: 0,
    },
    /* 10 - "Declaration" */
    LookaheadDFA {
        states: &[None, Some(7), Some(8), Some(9), Some(10)],
        transitions: &[
            DFATransition(0, 6, 1),
            DFATransition(0, 7, 2),
            DFATransition(0, 8, 3),
            DFATransition(0, 10, 4),
            DFATransition(0, 11, 4),
            DFATransition(0, 12, 4),
            DFATransition(0, 13, 4),
        ],
        k: 1,
    },
    /* 11 - "DoubleColon" */
    LookaheadDFA {
        states: &[Some(18)],
        transitions: &[],
        k: 0,
    },
    /* 12 - "Factor" */
    LookaheadDFA {
        states: &[None, Some(27), Some(28), Some(29), Some(30)],
        transitions: &[
            DFATransition(0, 19, 4),
            DFATransition(0, 21, 1),
            DFATransition(0, 23, 3),
            DFATransition(0, 25, 2),
            DFATransition(0, 27, 4),
            DFATransition(0, 28, 4),
            DFATransition(0, 29, 4),
            DFATransition(0, 32, 4),
            DFATransition(0, 33, 4),
            DFATransition(0, 34, 4),
            DFATransition(0, 38, 4),
        ],
        k: 1,
    },
    /* 13 - "GrammarDefinition" */
    LookaheadDFA {
        states: &[Some(15)],
        transitions: &[],
        k: 0,
    },
    /* 14 - "GrammarDefinitionList" */
    LookaheadDFA {
        states: &[None, Some(16), Some(17)],
        transitions: &[
            DFATransition(0, 0, 2),
            DFATransition(0, 27, 1),
            DFATransition(0, 36, 1),
            DFATransition(0, 37, 1),
        ],
        k: 1,
    },
    /* 15 - "Group" */
    LookaheadDFA {
        states: &[Some(44)],
        transitions: &[],
        k: 0,
    },
    /* 16 - "Identifier" */
    LookaheadDFA {
        states: &[Some(50)],
        transitions: &[],
        k: 0,
    },
    /* 17 - "LineComment" */
    LookaheadDFA {
        states: &[Some(76)],
        transitions: &[],
        k: 0,
    },
    /* 18 - "LiteralString" */
    LookaheadDFA {
        states: &[Some(52)],
        transitions: &[],
        k: 0,
    },
    /* 19 - "NonTerminal" */
    LookaheadDFA {
        states: &[Some(47)],
        transitions: &[],
        k: 0,
    },
    /* 20 - "NonTerminalOpt" */
    LookaheadDFA {
        states: &[None, Some(48), Some(49)],
        transitions: &[
            DFATransition(0, 16, 1),
            DFATransition(0, 17, 2),
            DFATransition(0, 18, 2),
            DFATransition(0, 19, 2),
            DFATransition(0, 21, 2),
            DFATransition(0, 22, 2),
            DFATransition(0, 23, 2),
            DFATransition(0, 24, 2),
            DFATransition(0, 25, 2),
            DFATransition(0, 26, 2),
            DFATransition(0, 27, 2),
            DFATransition(0, 28, 2),
            DFATransition(0, 29, 2),
            DFATransition(0, 32, 2),
            DFATransition(0, 33, 2),
            DFATransition(0, 34, 2),
            DFATransition(0, 35, 1),
            DFATransition(0, 36, 2),
            DFATransition(0, 37, 2),
            DFATransition(0, 38, 2),
        ],
        k: 1,
    },
    /* 21 - "Optional" */
    LookaheadDFA {
        states: &[Some(45)],
        transitions: &[],
        k: 0,
    },
    /* 22 - "ParolLs" */
    LookaheadDFA {
        states: &[Some(0)],
        transitions: &[],
        k: 0,
    },
    /* 23 - "Production" */
    LookaheadDFA {
        states: &[Some(20)],
        transitions: &[],
        k: 0,
    },
    /* 24 - "ProductionLHS" */
    LookaheadDFA {
        states: &[Some(19)],
        transitions: &[],
        k: 0,
    },
    /* 25 - "Prolog" */
    LookaheadDFA {
        states: &[Some(1)],
        transitions: &[],
        k: 0,
    },
    /* 26 - "PrologList" */
    LookaheadDFA {
        states: &[None, Some(4), Some(5)],
        transitions: &[
            DFATransition(0, 6, 1),
            DFATransition(0, 7, 1),
            DFATransition(0, 8, 1),
            DFATransition(0, 10, 1),
            DFATransition(0, 11, 1),
            DFATransition(0, 12, 1),
            DFATransition(0, 13, 1),
            DFATransition(0, 14, 2),
            DFATransition(0, 30, 2),
        ],
        k: 1,
    },
    /* 27 - "PrologList0" */
    LookaheadDFA {
        states: &[None, Some(2), Some(3)],
        transitions: &[DFATransition(0, 14, 2), DFATransition(0, 30, 1)],
        k: 1,
    },
    /* 28 - "Regex" */
    LookaheadDFA {
        states: &[Some(78)],
        transitions: &[],
        k: 0,
    },
    /* 29 - "Repeat" */
    LookaheadDFA {
        states: &[Some(46)],
        transitions: &[],
        k: 0,
    },
    /* 30 - "ScannerDirectives" */
    LookaheadDFA {
        states: &[None, Some(11), Some(12), Some(13), Some(14)],
        transitions: &[
            DFATransition(0, 10, 1),
            DFATransition(0, 11, 2),
            DFATransition(0, 12, 3),
            DFATransition(0, 13, 4),
        ],
        k: 1,
    },
    /* 31 - "ScannerState" */
    LookaheadDFA {
        states: &[Some(53)],
        transitions: &[],
        k: 0,
    },
    /* 32 - "ScannerStateList" */
    LookaheadDFA {
        states: &[None, Some(54), Some(55)],
        transitions: &[
            DFATransition(0, 10, 1),
            DFATransition(0, 11, 1),
            DFATransition(0, 12, 1),
            DFATransition(0, 13, 1),
            DFATransition(0, 26, 2),
        ],
        k: 1,
    },
    /* 33 - "ScannerSwitch" */
    LookaheadDFA {
        states: &[None, Some(59), Some(60), Some(61)],
        transitions: &[
            DFATransition(0, 32, 1),
            DFATransition(0, 33, 2),
            DFATransition(0, 34, 3),
        ],
        k: 1,
    },
    /* 34 - "ScannerSwitchOpt" */
    LookaheadDFA {
        states: &[None, Some(62), Some(63)],
        transitions: &[DFATransition(0, 22, 2), DFATransition(0, 27, 1)],
        k: 1,
    },
    /* 35 - "SimpleToken" */
    LookaheadDFA {
        states: &[Some(38)],
        transitions: &[],
        k: 0,
    },
    /* 36 - "SimpleTokenOpt" */
    LookaheadDFA {
        states: &[None, Some(39), Some(40)],
        transitions: &[
            DFATransition(0, 16, 1),
            DFATransition(0, 17, 2),
            DFATransition(0, 18, 2),
            DFATransition(0, 19, 2),
            DFATransition(0, 21, 2),
            DFATransition(0, 22, 2),
            DFATransition(0, 23, 2),
            DFATransition(0, 24, 2),
            DFATransition(0, 25, 2),
            DFATransition(0, 26, 2),
            DFATransition(0, 27, 2),
            DFATransition(0, 28, 2),
            DFATransition(0, 29, 2),
            DFATransition(0, 32, 2),
            DFATransition(0, 33, 2),
            DFATransition(0, 34, 2),
            DFATransition(0, 35, 1),
            DFATransition(0, 36, 2),
            DFATransition(0, 37, 2),
            DFATransition(0, 38, 2),
        ],
        k: 1,
    },
    /* 37 - "StartDeclaration" */
    LookaheadDFA {
        states: &[Some(6)],
        transitions: &[],
        k: 0,
    },
    /* 38 - "StateList" */
    LookaheadDFA {
        states: &[Some(56)],
        transitions: &[],
        k: 0,
    },
    /* 39 - "StateListList" */
    LookaheadDFA {
        states: &[None, Some(57), Some(58)],
        transitions: &[DFATransition(0, 20, 2), DFATransition(0, 31, 1)],
        k: 1,
    },
    /* 40 - "String" */
    LookaheadDFA {
        states: &[Some(51)],
        transitions: &[],
        k: 0,
    },
    /* 41 - "Symbol" */
    LookaheadDFA {
        states: &[None, Some(31), Some(32), Some(33), Some(34)],
        transitions: &[
            DFATransition(0, 19, 3),
            DFATransition(0, 27, 1),
            DFATransition(0, 28, 2),
            DFATransition(0, 29, 2),
            DFATransition(0, 32, 4),
            DFATransition(0, 33, 4),
            DFATransition(0, 34, 4),
            DFATransition(0, 38, 2),
        ],
        k: 1,
    },
    /* 42 - "TokenLiteral" */
    LookaheadDFA {
        states: &[None, Some(35), Some(36), Some(37)],
        transitions: &[
            DFATransition(0, 28, 1),
            DFATransition(0, 29, 2),
            DFATransition(0, 38, 3),
        ],
        k: 1,
    },
    /* 43 - "TokenWithStates" */
    LookaheadDFA {
        states: &[Some(41)],
        transitions: &[],
        k: 0,
    },
    /* 44 - "TokenWithStatesOpt" */
    LookaheadDFA {
        states: &[None, Some(42), Some(43)],
        transitions: &[
            DFATransition(0, 16, 1),
            DFATransition(0, 17, 2),
            DFATransition(0, 18, 2),
            DFATransition(0, 19, 2),
            DFATransition(0, 21, 2),
            DFATransition(0, 22, 2),
            DFATransition(0, 23, 2),
            DFATransition(0, 24, 2),
            DFATransition(0, 25, 2),
            DFATransition(0, 26, 2),
            DFATransition(0, 27, 2),
            DFATransition(0, 28, 2),
            DFATransition(0, 29, 2),
            DFATransition(0, 32, 2),
            DFATransition(0, 33, 2),
            DFATransition(0, 34, 2),
            DFATransition(0, 35, 1),
            DFATransition(0, 36, 2),
            DFATransition(0, 37, 2),
            DFATransition(0, 38, 2),
        ],
        k: 1,
    },
    /* 45 - "UserTypeDeclaration" */
    LookaheadDFA {
        states: &[Some(67)],
        transitions: &[],
        k: 0,
    },
    /* 46 - "UserTypeName" */
    LookaheadDFA {
        states: &[Some(68)],
        transitions: &[],
        k: 0,
    },
    /* 47 - "UserTypeNameList" */
    LookaheadDFA {
        states: &[None, Some(69), Some(70)],
        transitions: &[
            DFATransition(0, 6, 2),
            DFATransition(0, 7, 2),
            DFATransition(0, 8, 2),
            DFATransition(0, 10, 2),
            DFATransition(0, 11, 2),
            DFATransition(0, 12, 2),
            DFATransition(0, 13, 2),
            DFATransition(0, 14, 2),
            DFATransition(0, 15, 1),
            DFATransition(0, 17, 2),
            DFATransition(0, 18, 2),
            DFATransition(0, 19, 2),
            DFATransition(0, 21, 2),
            DFATransition(0, 22, 2),
            DFATransition(0, 23, 2),
            DFATransition(0, 24, 2),
            DFATransition(0, 25, 2),
            DFATransition(0, 26, 2),
            DFATransition(0, 27, 2),
            DFATransition(0, 28, 2),
            DFATransition(0, 29, 2),
            DFATransition(0, 30, 2),
            DFATransition(0, 32, 2),
            DFATransition(0, 33, 2),
            DFATransition(0, 34, 2),
            DFATransition(0, 36, 2),
            DFATransition(0, 37, 2),
            DFATransition(0, 38, 2),
        ],
        k: 1,
    },
];

pub const PRODUCTIONS: &[Production; 79] = &[
    // 0 - ParolLs: Prolog GrammarDefinition;
    Production {
        lhs: 22,
        production: &[ParseType::N(13), ParseType::N(25)],
    },
    // 1 - Prolog: StartDeclaration PrologList /* Vec */ PrologList0 /* Vec */;
    Production {
        lhs: 25,
        production: &[ParseType::N(27), ParseType::N(26), ParseType::N(37)],
    },
    // 2 - PrologList0: ScannerState PrologList0;
    Production {
        lhs: 27,
        production: &[ParseType::N(27), ParseType::N(31)],
    },
    // 3 - PrologList0: ;
    Production {
        lhs: 27,
        production: &[],
    },
    // 4 - PrologList: Declaration PrologList;
    Production {
        lhs: 26,
        production: &[ParseType::N(26), ParseType::N(10)],
    },
    // 5 - PrologList: ;
    Production {
        lhs: 26,
        production: &[],
    },
    // 6 - StartDeclaration: Comments "%start" Identifier Comments;
    Production {
        lhs: 37,
        production: &[
            ParseType::N(6),
            ParseType::N(16),
            ParseType::T(5),
            ParseType::N(6),
        ],
    },
    // 7 - Declaration: "%title" String Comments;
    Production {
        lhs: 10,
        production: &[ParseType::N(6), ParseType::N(40), ParseType::T(6)],
    },
    // 8 - Declaration: "%comment" String Comments;
    Production {
        lhs: 10,
        production: &[ParseType::N(6), ParseType::N(40), ParseType::T(7)],
    },
    // 9 - Declaration: "%user_type" Identifier "=" UserTypeName Comments;
    Production {
        lhs: 10,
        production: &[
            ParseType::N(6),
            ParseType::N(46),
            ParseType::T(9),
            ParseType::N(16),
            ParseType::T(8),
        ],
    },
    // 10 - Declaration: ScannerDirectives;
    Production {
        lhs: 10,
        production: &[ParseType::N(30)],
    },
    // 11 - ScannerDirectives: "%line_comment" TokenLiteral Comments;
    Production {
        lhs: 30,
        production: &[ParseType::N(6), ParseType::N(42), ParseType::T(10)],
    },
    // 12 - ScannerDirectives: "%block_comment" TokenLiteral TokenLiteral Comments;
    Production {
        lhs: 30,
        production: &[
            ParseType::N(6),
            ParseType::N(42),
            ParseType::N(42),
            ParseType::T(11),
        ],
    },
    // 13 - ScannerDirectives: "%auto_newline_off" Comments;
    Production {
        lhs: 30,
        production: &[ParseType::N(6), ParseType::T(12)],
    },
    // 14 - ScannerDirectives: "%auto_ws_off" Comments;
    Production {
        lhs: 30,
        production: &[ParseType::N(6), ParseType::T(13)],
    },
    // 15 - GrammarDefinition: "%%" Production GrammarDefinitionList /* Vec */;
    Production {
        lhs: 13,
        production: &[ParseType::N(14), ParseType::N(23), ParseType::T(14)],
    },
    // 16 - GrammarDefinitionList: Production GrammarDefinitionList;
    Production {
        lhs: 14,
        production: &[ParseType::N(14), ParseType::N(23)],
    },
    // 17 - GrammarDefinitionList: ;
    Production {
        lhs: 14,
        production: &[],
    },
    // 18 - DoubleColon: "::";
    Production {
        lhs: 11,
        production: &[ParseType::T(15)],
    },
    // 19 - ProductionLHS: Comments Identifier Comments ":";
    Production {
        lhs: 24,
        production: &[
            ParseType::T(16),
            ParseType::N(6),
            ParseType::N(16),
            ParseType::N(6),
        ],
    },
    // 20 - Production: ProductionLHS Alternations ";";
    Production {
        lhs: 23,
        production: &[ParseType::T(17), ParseType::N(3), ParseType::N(24)],
    },
    // 21 - Alternations: Alternation AlternationsList /* Vec */;
    Production {
        lhs: 3,
        production: &[ParseType::N(4), ParseType::N(1)],
    },
    // 22 - AlternationsList: "\|" Comments Alternation AlternationsList;
    Production {
        lhs: 4,
        production: &[
            ParseType::N(4),
            ParseType::N(1),
            ParseType::N(6),
            ParseType::T(18),
        ],
    },
    // 23 - AlternationsList: ;
    Production {
        lhs: 4,
        production: &[],
    },
    // 24 - Alternation: AlternationList /* Vec */;
    Production {
        lhs: 1,
        production: &[ParseType::N(2)],
    },
    // 25 - AlternationList: Factor Comments AlternationList;
    Production {
        lhs: 2,
        production: &[ParseType::N(2), ParseType::N(6), ParseType::N(12)],
    },
    // 26 - AlternationList: ;
    Production {
        lhs: 2,
        production: &[],
    },
    // 27 - Factor: Group;
    Production {
        lhs: 12,
        production: &[ParseType::N(15)],
    },
    // 28 - Factor: Repeat;
    Production {
        lhs: 12,
        production: &[ParseType::N(29)],
    },
    // 29 - Factor: Optional;
    Production {
        lhs: 12,
        production: &[ParseType::N(21)],
    },
    // 30 - Factor: Symbol;
    Production {
        lhs: 12,
        production: &[ParseType::N(41)],
    },
    // 31 - Symbol: NonTerminal;
    Production {
        lhs: 41,
        production: &[ParseType::N(19)],
    },
    // 32 - Symbol: SimpleToken;
    Production {
        lhs: 41,
        production: &[ParseType::N(35)],
    },
    // 33 - Symbol: TokenWithStates;
    Production {
        lhs: 41,
        production: &[ParseType::N(43)],
    },
    // 34 - Symbol: ScannerSwitch;
    Production {
        lhs: 41,
        production: &[ParseType::N(33)],
    },
    // 35 - TokenLiteral: String;
    Production {
        lhs: 42,
        production: &[ParseType::N(40)],
    },
    // 36 - TokenLiteral: LiteralString;
    Production {
        lhs: 42,
        production: &[ParseType::N(18)],
    },
    // 37 - TokenLiteral: Regex;
    Production {
        lhs: 42,
        production: &[ParseType::N(28)],
    },
    // 38 - SimpleToken: TokenLiteral SimpleTokenOpt /* Option */;
    Production {
        lhs: 35,
        production: &[ParseType::N(36), ParseType::N(42)],
    },
    // 39 - SimpleTokenOpt: ASTControl;
    Production {
        lhs: 36,
        production: &[ParseType::N(0)],
    },
    // 40 - SimpleTokenOpt: ;
    Production {
        lhs: 36,
        production: &[],
    },
    // 41 - TokenWithStates: "<" StateList ">" TokenLiteral TokenWithStatesOpt /* Option */;
    Production {
        lhs: 43,
        production: &[
            ParseType::N(44),
            ParseType::N(42),
            ParseType::T(20),
            ParseType::N(38),
            ParseType::T(19),
        ],
    },
    // 42 - TokenWithStatesOpt: ASTControl;
    Production {
        lhs: 44,
        production: &[ParseType::N(0)],
    },
    // 43 - TokenWithStatesOpt: ;
    Production {
        lhs: 44,
        production: &[],
    },
    // 44 - Group: "\(" Alternations "\)";
    Production {
        lhs: 15,
        production: &[ParseType::T(22), ParseType::N(3), ParseType::T(21)],
    },
    // 45 - Optional: "\[" Alternations "\]";
    Production {
        lhs: 21,
        production: &[ParseType::T(24), ParseType::N(3), ParseType::T(23)],
    },
    // 46 - Repeat: "\{" Alternations "\}";
    Production {
        lhs: 29,
        production: &[ParseType::T(26), ParseType::N(3), ParseType::T(25)],
    },
    // 47 - NonTerminal: Identifier NonTerminalOpt /* Option */;
    Production {
        lhs: 19,
        production: &[ParseType::N(20), ParseType::N(16)],
    },
    // 48 - NonTerminalOpt: ASTControl;
    Production {
        lhs: 20,
        production: &[ParseType::N(0)],
    },
    // 49 - NonTerminalOpt: ;
    Production {
        lhs: 20,
        production: &[],
    },
    // 50 - Identifier: "[a-zA-Z_][a-zA-Z0-9_]*";
    Production {
        lhs: 16,
        production: &[ParseType::T(27)],
    },
    // 51 - String: "\u{22}(\\.|[^\\])*?\u{22}";
    Production {
        lhs: 40,
        production: &[ParseType::T(28)],
    },
    // 52 - LiteralString: "'(\\'|[^'])*?'";
    Production {
        lhs: 18,
        production: &[ParseType::T(29)],
    },
    // 53 - ScannerState: "%scanner" Identifier "\{" ScannerStateList /* Vec */ "\}";
    Production {
        lhs: 31,
        production: &[
            ParseType::T(26),
            ParseType::N(32),
            ParseType::T(25),
            ParseType::N(16),
            ParseType::T(30),
        ],
    },
    // 54 - ScannerStateList: ScannerDirectives ScannerStateList;
    Production {
        lhs: 32,
        production: &[ParseType::N(32), ParseType::N(30)],
    },
    // 55 - ScannerStateList: ;
    Production {
        lhs: 32,
        production: &[],
    },
    // 56 - StateList: Identifier StateListList /* Vec */;
    Production {
        lhs: 38,
        production: &[ParseType::N(39), ParseType::N(16)],
    },
    // 57 - StateListList: "," Identifier StateListList;
    Production {
        lhs: 39,
        production: &[ParseType::N(39), ParseType::N(16), ParseType::T(31)],
    },
    // 58 - StateListList: ;
    Production {
        lhs: 39,
        production: &[],
    },
    // 59 - ScannerSwitch: "%sc" "\(" ScannerSwitchOpt /* Option */ "\)";
    Production {
        lhs: 33,
        production: &[
            ParseType::T(22),
            ParseType::N(34),
            ParseType::T(21),
            ParseType::T(32),
        ],
    },
    // 60 - ScannerSwitch: "%push" "\(" Identifier "\)";
    Production {
        lhs: 33,
        production: &[
            ParseType::T(22),
            ParseType::N(16),
            ParseType::T(21),
            ParseType::T(33),
        ],
    },
    // 61 - ScannerSwitch: "%pop" "\(" "\)";
    Production {
        lhs: 33,
        production: &[ParseType::T(22), ParseType::T(21), ParseType::T(34)],
    },
    // 62 - ScannerSwitchOpt: Identifier;
    Production {
        lhs: 34,
        production: &[ParseType::N(16)],
    },
    // 63 - ScannerSwitchOpt: ;
    Production {
        lhs: 34,
        production: &[],
    },
    // 64 - ASTControl: CutOperator;
    Production {
        lhs: 0,
        production: &[ParseType::N(9)],
    },
    // 65 - ASTControl: UserTypeDeclaration;
    Production {
        lhs: 0,
        production: &[ParseType::N(45)],
    },
    // 66 - CutOperator: "\^";
    Production {
        lhs: 9,
        production: &[ParseType::T(35)],
    },
    // 67 - UserTypeDeclaration: ":" UserTypeName;
    Production {
        lhs: 45,
        production: &[ParseType::N(46), ParseType::T(16)],
    },
    // 68 - UserTypeName: Identifier UserTypeNameList /* Vec */;
    Production {
        lhs: 46,
        production: &[ParseType::N(47), ParseType::N(16)],
    },
    // 69 - UserTypeNameList: DoubleColon Identifier UserTypeNameList;
    Production {
        lhs: 47,
        production: &[ParseType::N(47), ParseType::N(16), ParseType::N(11)],
    },
    // 70 - UserTypeNameList: ;
    Production {
        lhs: 47,
        production: &[],
    },
    // 71 - Comments: CommentsList /* Vec */;
    Production {
        lhs: 6,
        production: &[ParseType::N(7)],
    },
    // 72 - CommentsList: CommentsListGroup CommentsList;
    Production {
        lhs: 7,
        production: &[ParseType::N(7), ParseType::N(8)],
    },
    // 73 - CommentsListGroup: LineComment;
    Production {
        lhs: 8,
        production: &[ParseType::N(17)],
    },
    // 74 - CommentsListGroup: BlockComment;
    Production {
        lhs: 8,
        production: &[ParseType::N(5)],
    },
    // 75 - CommentsList: ;
    Production {
        lhs: 7,
        production: &[],
    },
    // 76 - LineComment: "//.*(:?\r\n|\r|\n|$)";
    Production {
        lhs: 17,
        production: &[ParseType::T(36)],
    },
    // 77 - BlockComment: "(?ms)/\u{2a}.*?\u{2a}/";
    Production {
        lhs: 5,
        production: &[ParseType::T(37)],
    },
    // 78 - Regex: "/(\\/|[^/]|)*?/";
    Production {
        lhs: 28,
        production: &[ParseType::T(38)],
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
    user_actions: &mut ParolLsGrammar,
) -> Result<Tree<ParseTreeType<'t>>>
where
    T: AsRef<Path>,
{
    let mut llk_parser = LLKParser::new(
        22,
        LOOKAHEAD_AUTOMATA,
        PRODUCTIONS,
        TERMINAL_NAMES,
        NON_TERMINALS,
    );
    let token_stream =
        RefCell::new(TokenStream::new(input, file_name, &TOKENIZERS, MAX_K).unwrap());
    // Initialize wrapper
    let mut user_actions = ParolLsGrammarAuto::new(user_actions);
    let result = llk_parser.parse(token_stream, &mut user_actions);
    match result {
        Ok(()) => Ok(llk_parser.parse_tree),
        Err(e) => Err(e),
    }
}