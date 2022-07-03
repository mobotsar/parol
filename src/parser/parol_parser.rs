// ---------------------------------------------------------
// This file was generated by parol.
// It is not intended for manual editing and changes will be
// lost after next build.
// ---------------------------------------------------------

use id_tree::Tree;
use miette::Result;
use parol_runtime::lexer::{TokenStream, Tokenizer};
#[allow(unused_imports)]
use parol_runtime::parser::{
    DFATransition, LLKParser, LookaheadDFA, ParseTreeType, ParseType, Production,
};
use std::cell::RefCell;
use std::path::Path;

use crate::parser::parol_grammar::ParolGrammar;
use crate::parser::parol_grammar_trait::ParolGrammarAuto;

use parol_runtime::lexer::tokenizer::{
    ERROR_TOKEN, NEW_LINE_TOKEN, UNMATCHABLE_TOKEN, WHITESPACE_TOKEN,
};

pub const TERMINALS: &[&str; 36] = &[
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
    /* 28 */ r###"\u{0022}([^\\]|\\.)*?\u{0022}"###,
    /* 29 */ r###"%scanner"###,
    /* 30 */ r###","###,
    /* 31 */ r###"%sc"###,
    /* 32 */ r###"%push"###,
    /* 33 */ r###"%pop"###,
    /* 34 */ r###"\^"###,
    /* 35 */ ERROR_TOKEN,
];

pub const TERMINAL_NAMES: &[&str; 36] = &[
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
    /* 29 */ "PercentScanner",
    /* 30 */ "Comma",
    /* 31 */ "PercentSc",
    /* 32 */ "PercentPush",
    /* 33 */ "PercentPop",
    /* 34 */ "CutOperator",
    /* 35 */ "Error",
];

/* SCANNER_0: "INITIAL" */
const SCANNER_0: (&[&str; 5], &[usize; 30]) = (
    &[
        /*  0 */ UNMATCHABLE_TOKEN,
        /*  1 */ NEW_LINE_TOKEN,
        /*  2 */ WHITESPACE_TOKEN,
        /*  3 */ r###"(//.*(\r\n|\r|\n|$))"###,
        /*  4 */ r###"((?ms)/\*.*?\*/)"###,
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
        29, /* PercentScanner */
        30, /* Comma */
        31, /* PercentSc */
        32, /* PercentPush */
        33, /* PercentPop */
        34, /* CutOperator */
    ],
);

const MAX_K: usize = 1;

pub const NON_TERMINALS: &[&str; 39] = &[
    /*  0 */ "ASTControl",
    /*  1 */ "Alternation",
    /*  2 */ "AlternationList",
    /*  3 */ "Alternations",
    /*  4 */ "AlternationsList",
    /*  5 */ "CutOperator",
    /*  6 */ "Declaration",
    /*  7 */ "DoubleColon",
    /*  8 */ "Factor",
    /*  9 */ "GrammarDefinition",
    /* 10 */ "GrammarDefinitionList",
    /* 11 */ "Group",
    /* 12 */ "Identifier",
    /* 13 */ "NonTerminal",
    /* 14 */ "NonTerminalOpt",
    /* 15 */ "Optional",
    /* 16 */ "Parol",
    /* 17 */ "Production",
    /* 18 */ "Prolog",
    /* 19 */ "PrologList",
    /* 20 */ "PrologList0",
    /* 21 */ "Repeat",
    /* 22 */ "ScannerDirectives",
    /* 23 */ "ScannerState",
    /* 24 */ "ScannerStateList",
    /* 25 */ "ScannerSwitch",
    /* 26 */ "ScannerSwitchOpt",
    /* 27 */ "SimpleToken",
    /* 28 */ "SimpleTokenOpt",
    /* 29 */ "StartDeclaration",
    /* 30 */ "StateList",
    /* 31 */ "StateListList",
    /* 32 */ "String",
    /* 33 */ "Symbol",
    /* 34 */ "TokenWithStates",
    /* 35 */ "TokenWithStatesOpt",
    /* 36 */ "UserTypeDeclaration",
    /* 37 */ "UserTypeName",
    /* 38 */ "UserTypeNameList",
];

pub const LOOKAHEAD_AUTOMATA: &[LookaheadDFA; 39] = &[
    /* 0 - "ASTControl" */
    LookaheadDFA {
        states: &[None, Some(59), Some(60)],
        transitions: &[DFATransition(0, 16, 2), DFATransition(0, 34, 1)],
        k: 1,
    },
    /* 1 - "Alternation" */
    LookaheadDFA {
        states: &[Some(23)],
        transitions: &[],
        k: 0,
    },
    /* 2 - "AlternationList" */
    LookaheadDFA {
        states: &[None, Some(24), Some(25)],
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
            DFATransition(0, 31, 1),
            DFATransition(0, 32, 1),
            DFATransition(0, 33, 1),
        ],
        k: 1,
    },
    /* 3 - "Alternations" */
    LookaheadDFA {
        states: &[Some(20)],
        transitions: &[],
        k: 0,
    },
    /* 4 - "AlternationsList" */
    LookaheadDFA {
        states: &[None, Some(21), Some(22)],
        transitions: &[
            DFATransition(0, 17, 2),
            DFATransition(0, 18, 1),
            DFATransition(0, 22, 2),
            DFATransition(0, 24, 2),
            DFATransition(0, 26, 2),
        ],
        k: 1,
    },
    /* 5 - "CutOperator" */
    LookaheadDFA {
        states: &[Some(61)],
        transitions: &[],
        k: 0,
    },
    /* 6 - "Declaration" */
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
    /* 7 - "DoubleColon" */
    LookaheadDFA {
        states: &[Some(18)],
        transitions: &[],
        k: 0,
    },
    /* 8 - "Factor" */
    LookaheadDFA {
        states: &[None, Some(26), Some(27), Some(28), Some(29)],
        transitions: &[
            DFATransition(0, 19, 4),
            DFATransition(0, 21, 1),
            DFATransition(0, 23, 3),
            DFATransition(0, 25, 2),
            DFATransition(0, 27, 4),
            DFATransition(0, 28, 4),
            DFATransition(0, 31, 4),
            DFATransition(0, 32, 4),
            DFATransition(0, 33, 4),
        ],
        k: 1,
    },
    /* 9 - "GrammarDefinition" */
    LookaheadDFA {
        states: &[Some(15)],
        transitions: &[],
        k: 0,
    },
    /* 10 - "GrammarDefinitionList" */
    LookaheadDFA {
        states: &[None, Some(16), Some(17)],
        transitions: &[DFATransition(0, 0, 2), DFATransition(0, 27, 1)],
        k: 1,
    },
    /* 11 - "Group" */
    LookaheadDFA {
        states: &[Some(40)],
        transitions: &[],
        k: 0,
    },
    /* 12 - "Identifier" */
    LookaheadDFA {
        states: &[Some(46)],
        transitions: &[],
        k: 0,
    },
    /* 13 - "NonTerminal" */
    LookaheadDFA {
        states: &[Some(43)],
        transitions: &[],
        k: 0,
    },
    /* 14 - "NonTerminalOpt" */
    LookaheadDFA {
        states: &[None, Some(44), Some(45)],
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
            DFATransition(0, 31, 2),
            DFATransition(0, 32, 2),
            DFATransition(0, 33, 2),
            DFATransition(0, 34, 1),
        ],
        k: 1,
    },
    /* 15 - "Optional" */
    LookaheadDFA {
        states: &[Some(41)],
        transitions: &[],
        k: 0,
    },
    /* 16 - "Parol" */
    LookaheadDFA {
        states: &[Some(0)],
        transitions: &[],
        k: 0,
    },
    /* 17 - "Production" */
    LookaheadDFA {
        states: &[Some(19)],
        transitions: &[],
        k: 0,
    },
    /* 18 - "Prolog" */
    LookaheadDFA {
        states: &[Some(1)],
        transitions: &[],
        k: 0,
    },
    /* 19 - "PrologList" */
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
            DFATransition(0, 29, 2),
        ],
        k: 1,
    },
    /* 20 - "PrologList0" */
    LookaheadDFA {
        states: &[None, Some(2), Some(3)],
        transitions: &[DFATransition(0, 14, 2), DFATransition(0, 29, 1)],
        k: 1,
    },
    /* 21 - "Repeat" */
    LookaheadDFA {
        states: &[Some(42)],
        transitions: &[],
        k: 0,
    },
    /* 22 - "ScannerDirectives" */
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
    /* 23 - "ScannerState" */
    LookaheadDFA {
        states: &[Some(48)],
        transitions: &[],
        k: 0,
    },
    /* 24 - "ScannerStateList" */
    LookaheadDFA {
        states: &[None, Some(49), Some(50)],
        transitions: &[
            DFATransition(0, 10, 1),
            DFATransition(0, 11, 1),
            DFATransition(0, 12, 1),
            DFATransition(0, 13, 1),
            DFATransition(0, 26, 2),
        ],
        k: 1,
    },
    /* 25 - "ScannerSwitch" */
    LookaheadDFA {
        states: &[None, Some(54), Some(55), Some(56)],
        transitions: &[
            DFATransition(0, 31, 1),
            DFATransition(0, 32, 2),
            DFATransition(0, 33, 3),
        ],
        k: 1,
    },
    /* 26 - "ScannerSwitchOpt" */
    LookaheadDFA {
        states: &[None, Some(57), Some(58)],
        transitions: &[DFATransition(0, 22, 2), DFATransition(0, 27, 1)],
        k: 1,
    },
    /* 27 - "SimpleToken" */
    LookaheadDFA {
        states: &[Some(34)],
        transitions: &[],
        k: 0,
    },
    /* 28 - "SimpleTokenOpt" */
    LookaheadDFA {
        states: &[None, Some(35), Some(36)],
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
            DFATransition(0, 31, 2),
            DFATransition(0, 32, 2),
            DFATransition(0, 33, 2),
            DFATransition(0, 34, 1),
        ],
        k: 1,
    },
    /* 29 - "StartDeclaration" */
    LookaheadDFA {
        states: &[Some(6)],
        transitions: &[],
        k: 0,
    },
    /* 30 - "StateList" */
    LookaheadDFA {
        states: &[Some(51)],
        transitions: &[],
        k: 0,
    },
    /* 31 - "StateListList" */
    LookaheadDFA {
        states: &[None, Some(52), Some(53)],
        transitions: &[DFATransition(0, 20, 2), DFATransition(0, 30, 1)],
        k: 1,
    },
    /* 32 - "String" */
    LookaheadDFA {
        states: &[Some(47)],
        transitions: &[],
        k: 0,
    },
    /* 33 - "Symbol" */
    LookaheadDFA {
        states: &[None, Some(30), Some(31), Some(32), Some(33)],
        transitions: &[
            DFATransition(0, 19, 3),
            DFATransition(0, 27, 1),
            DFATransition(0, 28, 2),
            DFATransition(0, 31, 4),
            DFATransition(0, 32, 4),
            DFATransition(0, 33, 4),
        ],
        k: 1,
    },
    /* 34 - "TokenWithStates" */
    LookaheadDFA {
        states: &[Some(37)],
        transitions: &[],
        k: 0,
    },
    /* 35 - "TokenWithStatesOpt" */
    LookaheadDFA {
        states: &[None, Some(38), Some(39)],
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
            DFATransition(0, 31, 2),
            DFATransition(0, 32, 2),
            DFATransition(0, 33, 2),
            DFATransition(0, 34, 1),
        ],
        k: 1,
    },
    /* 36 - "UserTypeDeclaration" */
    LookaheadDFA {
        states: &[Some(62)],
        transitions: &[],
        k: 0,
    },
    /* 37 - "UserTypeName" */
    LookaheadDFA {
        states: &[Some(63)],
        transitions: &[],
        k: 0,
    },
    /* 38 - "UserTypeNameList" */
    LookaheadDFA {
        states: &[None, Some(64), Some(65)],
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
            DFATransition(0, 31, 2),
            DFATransition(0, 32, 2),
            DFATransition(0, 33, 2),
        ],
        k: 1,
    },
];

pub const PRODUCTIONS: &[Production; 66] = &[
    // 0 - Parol: Prolog GrammarDefinition;
    Production {
        lhs: 16,
        production: &[ParseType::N(9), ParseType::N(18)],
    },
    // 1 - Prolog: StartDeclaration PrologList /* Vec */ PrologList0 /* Vec */;
    Production {
        lhs: 18,
        production: &[ParseType::N(20), ParseType::N(19), ParseType::N(29)],
    },
    // 2 - PrologList0: ScannerState PrologList0;
    Production {
        lhs: 20,
        production: &[ParseType::N(20), ParseType::N(23)],
    },
    // 3 - PrologList0: ;
    Production {
        lhs: 20,
        production: &[],
    },
    // 4 - PrologList: Declaration PrologList;
    Production {
        lhs: 19,
        production: &[ParseType::N(19), ParseType::N(6)],
    },
    // 5 - PrologList: ;
    Production {
        lhs: 19,
        production: &[],
    },
    // 6 - StartDeclaration: "%start"^ /* Clipped */ Identifier;
    Production {
        lhs: 29,
        production: &[ParseType::N(12), ParseType::T(5)],
    },
    // 7 - Declaration: "%title"^ /* Clipped */ String;
    Production {
        lhs: 6,
        production: &[ParseType::N(32), ParseType::T(6)],
    },
    // 8 - Declaration: "%comment"^ /* Clipped */ String;
    Production {
        lhs: 6,
        production: &[ParseType::N(32), ParseType::T(7)],
    },
    // 9 - Declaration: "%user_type"^ /* Clipped */ Identifier "="^ /* Clipped */ UserTypeName;
    Production {
        lhs: 6,
        production: &[
            ParseType::N(37),
            ParseType::T(9),
            ParseType::N(12),
            ParseType::T(8),
        ],
    },
    // 10 - Declaration: ScannerDirectives;
    Production {
        lhs: 6,
        production: &[ParseType::N(22)],
    },
    // 11 - ScannerDirectives: "%line_comment"^ /* Clipped */ String;
    Production {
        lhs: 22,
        production: &[ParseType::N(32), ParseType::T(10)],
    },
    // 12 - ScannerDirectives: "%block_comment"^ /* Clipped */ String String;
    Production {
        lhs: 22,
        production: &[ParseType::N(32), ParseType::N(32), ParseType::T(11)],
    },
    // 13 - ScannerDirectives: "%auto_newline_off"^ /* Clipped */;
    Production {
        lhs: 22,
        production: &[ParseType::T(12)],
    },
    // 14 - ScannerDirectives: "%auto_ws_off"^ /* Clipped */;
    Production {
        lhs: 22,
        production: &[ParseType::T(13)],
    },
    // 15 - GrammarDefinition: "%%"^ /* Clipped */ Production GrammarDefinitionList /* Vec */;
    Production {
        lhs: 9,
        production: &[ParseType::N(10), ParseType::N(17), ParseType::T(14)],
    },
    // 16 - GrammarDefinitionList: Production GrammarDefinitionList;
    Production {
        lhs: 10,
        production: &[ParseType::N(10), ParseType::N(17)],
    },
    // 17 - GrammarDefinitionList: ;
    Production {
        lhs: 10,
        production: &[],
    },
    // 18 - DoubleColon: "::";
    Production {
        lhs: 7,
        production: &[ParseType::T(15)],
    },
    // 19 - Production: Identifier ":"^ /* Clipped */ Alternations ";"^ /* Clipped */;
    Production {
        lhs: 17,
        production: &[
            ParseType::T(17),
            ParseType::N(3),
            ParseType::T(16),
            ParseType::N(12),
        ],
    },
    // 20 - Alternations: Alternation AlternationsList /* Vec */;
    Production {
        lhs: 3,
        production: &[ParseType::N(4), ParseType::N(1)],
    },
    // 21 - AlternationsList: "\|"^ /* Clipped */ Alternation AlternationsList;
    Production {
        lhs: 4,
        production: &[ParseType::N(4), ParseType::N(1), ParseType::T(18)],
    },
    // 22 - AlternationsList: ;
    Production {
        lhs: 4,
        production: &[],
    },
    // 23 - Alternation: AlternationList /* Vec */;
    Production {
        lhs: 1,
        production: &[ParseType::N(2)],
    },
    // 24 - AlternationList: Factor AlternationList;
    Production {
        lhs: 2,
        production: &[ParseType::N(2), ParseType::N(8)],
    },
    // 25 - AlternationList: ;
    Production {
        lhs: 2,
        production: &[],
    },
    // 26 - Factor: Group;
    Production {
        lhs: 8,
        production: &[ParseType::N(11)],
    },
    // 27 - Factor: Repeat;
    Production {
        lhs: 8,
        production: &[ParseType::N(21)],
    },
    // 28 - Factor: Optional;
    Production {
        lhs: 8,
        production: &[ParseType::N(15)],
    },
    // 29 - Factor: Symbol;
    Production {
        lhs: 8,
        production: &[ParseType::N(33)],
    },
    // 30 - Symbol: NonTerminal;
    Production {
        lhs: 33,
        production: &[ParseType::N(13)],
    },
    // 31 - Symbol: SimpleToken;
    Production {
        lhs: 33,
        production: &[ParseType::N(27)],
    },
    // 32 - Symbol: TokenWithStates;
    Production {
        lhs: 33,
        production: &[ParseType::N(34)],
    },
    // 33 - Symbol: ScannerSwitch;
    Production {
        lhs: 33,
        production: &[ParseType::N(25)],
    },
    // 34 - SimpleToken: String SimpleTokenOpt /* Option */;
    Production {
        lhs: 27,
        production: &[ParseType::N(28), ParseType::N(32)],
    },
    // 35 - SimpleTokenOpt: ASTControl;
    Production {
        lhs: 28,
        production: &[ParseType::N(0)],
    },
    // 36 - SimpleTokenOpt: ;
    Production {
        lhs: 28,
        production: &[],
    },
    // 37 - TokenWithStates: "<"^ /* Clipped */ StateList ">"^ /* Clipped */ String TokenWithStatesOpt /* Option */;
    Production {
        lhs: 34,
        production: &[
            ParseType::N(35),
            ParseType::N(32),
            ParseType::T(20),
            ParseType::N(30),
            ParseType::T(19),
        ],
    },
    // 38 - TokenWithStatesOpt: ASTControl;
    Production {
        lhs: 35,
        production: &[ParseType::N(0)],
    },
    // 39 - TokenWithStatesOpt: ;
    Production {
        lhs: 35,
        production: &[],
    },
    // 40 - Group: "\("^ /* Clipped */ Alternations "\)"^ /* Clipped */;
    Production {
        lhs: 11,
        production: &[ParseType::T(22), ParseType::N(3), ParseType::T(21)],
    },
    // 41 - Optional: "\["^ /* Clipped */ Alternations "\]"^ /* Clipped */;
    Production {
        lhs: 15,
        production: &[ParseType::T(24), ParseType::N(3), ParseType::T(23)],
    },
    // 42 - Repeat: "\{"^ /* Clipped */ Alternations "\}"^ /* Clipped */;
    Production {
        lhs: 21,
        production: &[ParseType::T(26), ParseType::N(3), ParseType::T(25)],
    },
    // 43 - NonTerminal: Identifier NonTerminalOpt /* Option */;
    Production {
        lhs: 13,
        production: &[ParseType::N(14), ParseType::N(12)],
    },
    // 44 - NonTerminalOpt: ASTControl;
    Production {
        lhs: 14,
        production: &[ParseType::N(0)],
    },
    // 45 - NonTerminalOpt: ;
    Production {
        lhs: 14,
        production: &[],
    },
    // 46 - Identifier: "[a-zA-Z_][a-zA-Z0-9_]*";
    Production {
        lhs: 12,
        production: &[ParseType::T(27)],
    },
    // 47 - String: "\u{0022}([^\\]|\\.)*?\u{0022}";
    Production {
        lhs: 32,
        production: &[ParseType::T(28)],
    },
    // 48 - ScannerState: "%scanner"^ /* Clipped */ Identifier "\{"^ /* Clipped */ ScannerStateList /* Vec */ "\}"^ /* Clipped */;
    Production {
        lhs: 23,
        production: &[
            ParseType::T(26),
            ParseType::N(24),
            ParseType::T(25),
            ParseType::N(12),
            ParseType::T(29),
        ],
    },
    // 49 - ScannerStateList: ScannerDirectives ScannerStateList;
    Production {
        lhs: 24,
        production: &[ParseType::N(24), ParseType::N(22)],
    },
    // 50 - ScannerStateList: ;
    Production {
        lhs: 24,
        production: &[],
    },
    // 51 - StateList: Identifier StateListList /* Vec */;
    Production {
        lhs: 30,
        production: &[ParseType::N(31), ParseType::N(12)],
    },
    // 52 - StateListList: ","^ /* Clipped */ Identifier StateListList;
    Production {
        lhs: 31,
        production: &[ParseType::N(31), ParseType::N(12), ParseType::T(30)],
    },
    // 53 - StateListList: ;
    Production {
        lhs: 31,
        production: &[],
    },
    // 54 - ScannerSwitch: "%sc"^ /* Clipped */ "\("^ /* Clipped */ ScannerSwitchOpt /* Option */ "\)"^ /* Clipped */;
    Production {
        lhs: 25,
        production: &[
            ParseType::T(22),
            ParseType::N(26),
            ParseType::T(21),
            ParseType::T(31),
        ],
    },
    // 55 - ScannerSwitch: "%push"^ /* Clipped */ "\("^ /* Clipped */ Identifier "\)"^ /* Clipped */;
    Production {
        lhs: 25,
        production: &[
            ParseType::T(22),
            ParseType::N(12),
            ParseType::T(21),
            ParseType::T(32),
        ],
    },
    // 56 - ScannerSwitch: "%pop"^ /* Clipped */ "\("^ /* Clipped */ "\)"^ /* Clipped */;
    Production {
        lhs: 25,
        production: &[ParseType::T(22), ParseType::T(21), ParseType::T(33)],
    },
    // 57 - ScannerSwitchOpt: Identifier;
    Production {
        lhs: 26,
        production: &[ParseType::N(12)],
    },
    // 58 - ScannerSwitchOpt: ;
    Production {
        lhs: 26,
        production: &[],
    },
    // 59 - ASTControl: CutOperator;
    Production {
        lhs: 0,
        production: &[ParseType::N(5)],
    },
    // 60 - ASTControl: UserTypeDeclaration;
    Production {
        lhs: 0,
        production: &[ParseType::N(36)],
    },
    // 61 - CutOperator: "\^"^ /* Clipped */;
    Production {
        lhs: 5,
        production: &[ParseType::T(34)],
    },
    // 62 - UserTypeDeclaration: ":"^ /* Clipped */ UserTypeName;
    Production {
        lhs: 36,
        production: &[ParseType::N(37), ParseType::T(16)],
    },
    // 63 - UserTypeName: Identifier UserTypeNameList /* Vec */;
    Production {
        lhs: 37,
        production: &[ParseType::N(38), ParseType::N(12)],
    },
    // 64 - UserTypeNameList: DoubleColon^ /* Clipped */ Identifier UserTypeNameList;
    Production {
        lhs: 38,
        production: &[ParseType::N(38), ParseType::N(12), ParseType::N(7)],
    },
    // 65 - UserTypeNameList: ;
    Production {
        lhs: 38,
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
    user_actions: &mut ParolGrammar<'t>,
) -> Result<Tree<ParseTreeType<'t>>>
where
    T: AsRef<Path>,
{
    let mut llk_parser = LLKParser::new(
        16,
        LOOKAHEAD_AUTOMATA,
        PRODUCTIONS,
        TERMINAL_NAMES,
        NON_TERMINALS,
    );
    let token_stream =
        RefCell::new(TokenStream::new(input, file_name, &TOKENIZERS, MAX_K).unwrap());
    // Initialize wrapper
    let mut user_actions = ParolGrammarAuto::new(user_actions);
    let result = llk_parser.parse(token_stream, &mut user_actions);
    match result {
        Ok(()) => Ok(llk_parser.parse_tree),
        Err(e) => Err(e),
    }
}
