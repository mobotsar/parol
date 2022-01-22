// ---------------------------------------------------------
// This file was generated by parol.
// It is not intended for manual editing and changes will be
// lost after next build.
// ---------------------------------------------------------

use crate::parser::parol_grammar::ParolGrammar;
use id_tree::Tree;
use miette::{miette, Result};
use parol_runtime::parser::{ParseTreeStackEntry, ParseTreeType, UserActionsTrait};

///
/// The `ParolGrammarTrait` trait is automatically generated for the
/// given grammar.
/// All functions have default implementations.
///
pub trait ParolGrammarTrait {
    ///
    /// Implement this method if you need the provided information
    ///
    fn init(&mut self, _file_name: &std::path::Path) {}

    /// Semantic action for production 0:
    ///
    /// Parol: Prolog GrammarDefinition;
    ///
    fn parol_0(
        &mut self,
        _prolog_0: &ParseTreeStackEntry,
        _grammar_definition_1: &ParseTreeStackEntry,
        _parse_tree: &Tree<ParseTreeType>,
    ) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 1:
    ///
    /// Prolog: StartDeclaration Declarations ScannerStates;
    ///
    fn prolog_1(
        &mut self,
        _start_declaration_0: &ParseTreeStackEntry,
        _declarations_1: &ParseTreeStackEntry,
        _scanner_states_2: &ParseTreeStackEntry,
        _parse_tree: &Tree<ParseTreeType>,
    ) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 2:
    ///
    /// StartDeclaration: "%start" Identifier;
    ///
    fn start_declaration_2(
        &mut self,
        _percent_start_0: &ParseTreeStackEntry,
        _identifier_1: &ParseTreeStackEntry,
        _parse_tree: &Tree<ParseTreeType>,
    ) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 3:
    ///
    /// Declarations: Declaration Declarations;
    ///
    fn declarations_3(
        &mut self,
        _declaration_0: &ParseTreeStackEntry,
        _declarations_1: &ParseTreeStackEntry,
        _parse_tree: &Tree<ParseTreeType>,
    ) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 4:
    ///
    /// Declarations: ;
    ///
    fn declarations_4(&mut self, _parse_tree: &Tree<ParseTreeType>) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 5:
    ///
    /// Declaration: "%title" String;
    ///
    fn declaration_5(
        &mut self,
        _percent_title_0: &ParseTreeStackEntry,
        _string_1: &ParseTreeStackEntry,
        _parse_tree: &Tree<ParseTreeType>,
    ) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 6:
    ///
    /// Declaration: "%comment" String;
    ///
    fn declaration_6(
        &mut self,
        _percent_comment_0: &ParseTreeStackEntry,
        _string_1: &ParseTreeStackEntry,
        _parse_tree: &Tree<ParseTreeType>,
    ) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 7:
    ///
    /// Declaration: ScannerDirectives;
    ///
    fn declaration_7(
        &mut self,
        _scanner_directives_0: &ParseTreeStackEntry,
        _parse_tree: &Tree<ParseTreeType>,
    ) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 8:
    ///
    /// ScannerDirectives: "%line_comment" String;
    ///
    fn scanner_directives_8(
        &mut self,
        _percent_line_underscore_comment_0: &ParseTreeStackEntry,
        _string_1: &ParseTreeStackEntry,
        _parse_tree: &Tree<ParseTreeType>,
    ) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 9:
    ///
    /// ScannerDirectives: "%block_comment" String String;
    ///
    fn scanner_directives_9(
        &mut self,
        _percent_block_underscore_comment_0: &ParseTreeStackEntry,
        _string_1: &ParseTreeStackEntry,
        _string_2: &ParseTreeStackEntry,
        _parse_tree: &Tree<ParseTreeType>,
    ) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 10:
    ///
    /// ScannerDirectives: "%auto_newline_off";
    ///
    fn scanner_directives_10(
        &mut self,
        _percent_auto_underscore_newline_underscore_off_0: &ParseTreeStackEntry,
        _parse_tree: &Tree<ParseTreeType>,
    ) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 11:
    ///
    /// ScannerDirectives: "%auto_ws_off";
    ///
    fn scanner_directives_11(
        &mut self,
        _percent_auto_underscore_ws_underscore_off_0: &ParseTreeStackEntry,
        _parse_tree: &Tree<ParseTreeType>,
    ) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 12:
    ///
    /// ScannerStates: ScannerState ScannerStates;
    ///
    fn scanner_states_12(
        &mut self,
        _scanner_state_0: &ParseTreeStackEntry,
        _scanner_states_1: &ParseTreeStackEntry,
        _parse_tree: &Tree<ParseTreeType>,
    ) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 13:
    ///
    /// ScannerStates: ;
    ///
    fn scanner_states_13(&mut self, _parse_tree: &Tree<ParseTreeType>) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 14:
    ///
    /// GrammarDefinition: "%%" Production GrammarDefinitionList;
    ///
    fn grammar_definition_14(
        &mut self,
        _percent_percent_0: &ParseTreeStackEntry,
        _production_1: &ParseTreeStackEntry,
        _grammar_definition_list_2: &ParseTreeStackEntry,
        _parse_tree: &Tree<ParseTreeType>,
    ) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 15:
    ///
    /// GrammarDefinitionList: Production GrammarDefinitionList;
    ///
    fn grammar_definition_list_15(
        &mut self,
        _production_0: &ParseTreeStackEntry,
        _grammar_definition_list_1: &ParseTreeStackEntry,
        _parse_tree: &Tree<ParseTreeType>,
    ) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 16:
    ///
    /// GrammarDefinitionList: /* Vec<GrammarDefinitionList>::New */;
    ///
    fn grammar_definition_list_16(&mut self, _parse_tree: &Tree<ParseTreeType>) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 17:
    ///
    /// Production: Identifier ":" Alternations ";";
    ///
    fn production_17(
        &mut self,
        _identifier_0: &ParseTreeStackEntry,
        _colon_1: &ParseTreeStackEntry,
        _alternations_2: &ParseTreeStackEntry,
        _semicolon_3: &ParseTreeStackEntry,
        _parse_tree: &Tree<ParseTreeType>,
    ) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 18:
    ///
    /// Alternations: Alternation AlternationsList;
    ///
    fn alternations_18(
        &mut self,
        _alternation_0: &ParseTreeStackEntry,
        _alternations_list_1: &ParseTreeStackEntry,
        _parse_tree: &Tree<ParseTreeType>,
    ) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 19:
    ///
    /// AlternationsList: "\|" Alternation AlternationsList;
    ///
    fn alternations_list_19(
        &mut self,
        _or_0: &ParseTreeStackEntry,
        _alternation_1: &ParseTreeStackEntry,
        _alternations_list_2: &ParseTreeStackEntry,
        _parse_tree: &Tree<ParseTreeType>,
    ) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 20:
    ///
    /// AlternationsList: /* Vec<AlternationsList>::New */;
    ///
    fn alternations_list_20(&mut self, _parse_tree: &Tree<ParseTreeType>) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 21:
    ///
    /// Alternation: AlternationList;
    ///
    fn alternation_21(
        &mut self,
        _alternation_list_0: &ParseTreeStackEntry,
        _parse_tree: &Tree<ParseTreeType>,
    ) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 22:
    ///
    /// AlternationList: Factor AlternationList;
    ///
    fn alternation_list_22(
        &mut self,
        _factor_0: &ParseTreeStackEntry,
        _alternation_list_1: &ParseTreeStackEntry,
        _parse_tree: &Tree<ParseTreeType>,
    ) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 23:
    ///
    /// AlternationList: /* Vec<AlternationList>::New */;
    ///
    fn alternation_list_23(&mut self, _parse_tree: &Tree<ParseTreeType>) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 24:
    ///
    /// Factor: Group;
    ///
    fn factor_24(
        &mut self,
        _group_0: &ParseTreeStackEntry,
        _parse_tree: &Tree<ParseTreeType>,
    ) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 25:
    ///
    /// Factor: Repeat;
    ///
    fn factor_25(
        &mut self,
        _repeat_0: &ParseTreeStackEntry,
        _parse_tree: &Tree<ParseTreeType>,
    ) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 26:
    ///
    /// Factor: Optional;
    ///
    fn factor_26(
        &mut self,
        _optional_0: &ParseTreeStackEntry,
        _parse_tree: &Tree<ParseTreeType>,
    ) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 27:
    ///
    /// Factor: Symbol;
    ///
    fn factor_27(
        &mut self,
        _symbol_0: &ParseTreeStackEntry,
        _parse_tree: &Tree<ParseTreeType>,
    ) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 28:
    ///
    /// Symbol: Identifier;
    ///
    fn symbol_28(
        &mut self,
        _identifier_0: &ParseTreeStackEntry,
        _parse_tree: &Tree<ParseTreeType>,
    ) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 29:
    ///
    /// Symbol: SimpleToken;
    ///
    fn symbol_29(
        &mut self,
        _simple_token_0: &ParseTreeStackEntry,
        _parse_tree: &Tree<ParseTreeType>,
    ) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 30:
    ///
    /// Symbol: TokenWithStates;
    ///
    fn symbol_30(
        &mut self,
        _token_with_states_0: &ParseTreeStackEntry,
        _parse_tree: &Tree<ParseTreeType>,
    ) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 31:
    ///
    /// Symbol: ScannerSwitch;
    ///
    fn symbol_31(
        &mut self,
        _scanner_switch_0: &ParseTreeStackEntry,
        _parse_tree: &Tree<ParseTreeType>,
    ) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 32:
    ///
    /// SimpleToken: String;
    ///
    fn simple_token_32(
        &mut self,
        _string_0: &ParseTreeStackEntry,
        _parse_tree: &Tree<ParseTreeType>,
    ) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 33:
    ///
    /// TokenWithStates: "<" StateList ">" String;
    ///
    fn token_with_states_33(
        &mut self,
        _l_t_0: &ParseTreeStackEntry,
        _state_list_1: &ParseTreeStackEntry,
        _g_t_2: &ParseTreeStackEntry,
        _string_3: &ParseTreeStackEntry,
        _parse_tree: &Tree<ParseTreeType>,
    ) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 34:
    ///
    /// Group: "\(" Alternations "\)";
    ///
    fn group_34(
        &mut self,
        _l_paren_0: &ParseTreeStackEntry,
        _alternations_1: &ParseTreeStackEntry,
        _r_paren_2: &ParseTreeStackEntry,
        _parse_tree: &Tree<ParseTreeType>,
    ) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 35:
    ///
    /// Optional: "\[" Alternations "\]";
    ///
    fn optional_35(
        &mut self,
        _l_bracket_0: &ParseTreeStackEntry,
        _alternations_1: &ParseTreeStackEntry,
        _r_bracket_2: &ParseTreeStackEntry,
        _parse_tree: &Tree<ParseTreeType>,
    ) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 36:
    ///
    /// Repeat: "\{" Alternations "\}";
    ///
    fn repeat_36(
        &mut self,
        _l_brace_0: &ParseTreeStackEntry,
        _alternations_1: &ParseTreeStackEntry,
        _r_brace_2: &ParseTreeStackEntry,
        _parse_tree: &Tree<ParseTreeType>,
    ) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 37:
    ///
    /// Identifier: "[a-zA-Z_][a-zA-Z0-9_]*";
    ///
    fn identifier_37(
        &mut self,
        _identifier_0: &ParseTreeStackEntry,
        _parse_tree: &Tree<ParseTreeType>,
    ) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 38:
    ///
    /// String: "\u{0022}([^\\]|\\.)*?\u{0022}";
    ///
    fn string_38(
        &mut self,
        _string_0: &ParseTreeStackEntry,
        _parse_tree: &Tree<ParseTreeType>,
    ) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 39:
    ///
    /// ScannerState: "%scanner" Identifier "\{" ScannerStateList "\}";
    ///
    fn scanner_state_39(
        &mut self,
        _percent_scanner_0: &ParseTreeStackEntry,
        _identifier_1: &ParseTreeStackEntry,
        _l_brace_2: &ParseTreeStackEntry,
        _scanner_state_list_3: &ParseTreeStackEntry,
        _r_brace_4: &ParseTreeStackEntry,
        _parse_tree: &Tree<ParseTreeType>,
    ) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 40:
    ///
    /// ScannerStateList: ScannerDirectives ScannerStateList;
    ///
    fn scanner_state_list_40(
        &mut self,
        _scanner_directives_0: &ParseTreeStackEntry,
        _scanner_state_list_1: &ParseTreeStackEntry,
        _parse_tree: &Tree<ParseTreeType>,
    ) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 41:
    ///
    /// ScannerStateList: /* Vec<ScannerStateList>::New */;
    ///
    fn scanner_state_list_41(&mut self, _parse_tree: &Tree<ParseTreeType>) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 42:
    ///
    /// StateList: Identifier StateListRest;
    ///
    fn state_list_42(
        &mut self,
        _identifier_0: &ParseTreeStackEntry,
        _state_list_rest_1: &ParseTreeStackEntry,
        _parse_tree: &Tree<ParseTreeType>,
    ) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 43:
    ///
    /// StateListRest: "," Identifier StateListRest;
    ///
    fn state_list_rest_43(
        &mut self,
        _comma_0: &ParseTreeStackEntry,
        _identifier_1: &ParseTreeStackEntry,
        _state_list_rest_2: &ParseTreeStackEntry,
        _parse_tree: &Tree<ParseTreeType>,
    ) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 44:
    ///
    /// StateListRest: ;
    ///
    fn state_list_rest_44(&mut self, _parse_tree: &Tree<ParseTreeType>) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 45:
    ///
    /// ScannerSwitch: "%sc" "\(" ScannerNameOpt "\)";
    ///
    fn scanner_switch_45(
        &mut self,
        _percent_sc_0: &ParseTreeStackEntry,
        _l_paren_1: &ParseTreeStackEntry,
        _scanner_name_opt_2: &ParseTreeStackEntry,
        _r_paren_3: &ParseTreeStackEntry,
        _parse_tree: &Tree<ParseTreeType>,
    ) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 46:
    ///
    /// ScannerSwitch: "%push" "\(" Identifier "\)";
    ///
    fn scanner_switch_46(
        &mut self,
        _percent_push_0: &ParseTreeStackEntry,
        _l_paren_1: &ParseTreeStackEntry,
        _identifier_2: &ParseTreeStackEntry,
        _r_paren_3: &ParseTreeStackEntry,
        _parse_tree: &Tree<ParseTreeType>,
    ) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 47:
    ///
    /// ScannerSwitch: "%pop" "\(" "\)";
    ///
    fn scanner_switch_47(
        &mut self,
        _percent_pop_0: &ParseTreeStackEntry,
        _l_paren_1: &ParseTreeStackEntry,
        _r_paren_2: &ParseTreeStackEntry,
        _parse_tree: &Tree<ParseTreeType>,
    ) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 48:
    ///
    /// ScannerNameOpt: Identifier;
    ///
    fn scanner_name_opt_48(
        &mut self,
        _identifier_0: &ParseTreeStackEntry,
        _parse_tree: &Tree<ParseTreeType>,
    ) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 49:
    ///
    /// ScannerNameOpt: ;
    ///
    fn scanner_name_opt_49(&mut self, _parse_tree: &Tree<ParseTreeType>) -> Result<()> {
        Ok(())
    }
}

impl UserActionsTrait for ParolGrammar {
    ///
    /// Initialize the user with additional information.
    /// This function is called by the parser before parsing starts.
    /// Is is used to transport necessary data from parser to user.
    ///
    fn init(&mut self, file_name: &std::path::Path) {
        ParolGrammarTrait::init(self, file_name);
    }

    ///
    /// This function is implemented automatically for the user's item ParolGrammar.
    ///
    fn call_semantic_action_for_production_number(
        &mut self,
        prod_num: usize,
        children: &[ParseTreeStackEntry],
        parse_tree: &Tree<ParseTreeType>,
    ) -> Result<()> {
        match prod_num {
            0 => self.parol_0(&children[0], &children[1], parse_tree),

            1 => self.prolog_1(&children[0], &children[1], &children[2], parse_tree),

            2 => self.start_declaration_2(&children[0], &children[1], parse_tree),

            3 => self.declarations_3(&children[0], &children[1], parse_tree),

            4 => self.declarations_4(parse_tree),

            5 => self.declaration_5(&children[0], &children[1], parse_tree),

            6 => self.declaration_6(&children[0], &children[1], parse_tree),

            7 => self.declaration_7(&children[0], parse_tree),

            8 => self.scanner_directives_8(&children[0], &children[1], parse_tree),

            9 => self.scanner_directives_9(&children[0], &children[1], &children[2], parse_tree),

            10 => self.scanner_directives_10(&children[0], parse_tree),

            11 => self.scanner_directives_11(&children[0], parse_tree),

            12 => self.scanner_states_12(&children[0], &children[1], parse_tree),

            13 => self.scanner_states_13(parse_tree),

            14 => self.grammar_definition_14(&children[0], &children[1], &children[2], parse_tree),

            15 => self.grammar_definition_list_15(&children[0], &children[1], parse_tree),

            16 => self.grammar_definition_list_16(parse_tree),

            17 => self.production_17(
                &children[0],
                &children[1],
                &children[2],
                &children[3],
                parse_tree,
            ),

            18 => self.alternations_18(&children[0], &children[1], parse_tree),

            19 => self.alternations_list_19(&children[0], &children[1], &children[2], parse_tree),

            20 => self.alternations_list_20(parse_tree),

            21 => self.alternation_21(&children[0], parse_tree),

            22 => self.alternation_list_22(&children[0], &children[1], parse_tree),

            23 => self.alternation_list_23(parse_tree),

            24 => self.factor_24(&children[0], parse_tree),

            25 => self.factor_25(&children[0], parse_tree),

            26 => self.factor_26(&children[0], parse_tree),

            27 => self.factor_27(&children[0], parse_tree),

            28 => self.symbol_28(&children[0], parse_tree),

            29 => self.symbol_29(&children[0], parse_tree),

            30 => self.symbol_30(&children[0], parse_tree),

            31 => self.symbol_31(&children[0], parse_tree),

            32 => self.simple_token_32(&children[0], parse_tree),

            33 => self.token_with_states_33(
                &children[0],
                &children[1],
                &children[2],
                &children[3],
                parse_tree,
            ),

            34 => self.group_34(&children[0], &children[1], &children[2], parse_tree),

            35 => self.optional_35(&children[0], &children[1], &children[2], parse_tree),

            36 => self.repeat_36(&children[0], &children[1], &children[2], parse_tree),

            37 => self.identifier_37(&children[0], parse_tree),

            38 => self.string_38(&children[0], parse_tree),

            39 => self.scanner_state_39(
                &children[0],
                &children[1],
                &children[2],
                &children[3],
                &children[4],
                parse_tree,
            ),

            40 => self.scanner_state_list_40(&children[0], &children[1], parse_tree),

            41 => self.scanner_state_list_41(parse_tree),

            42 => self.state_list_42(&children[0], &children[1], parse_tree),

            43 => self.state_list_rest_43(&children[0], &children[1], &children[2], parse_tree),

            44 => self.state_list_rest_44(parse_tree),

            45 => self.scanner_switch_45(
                &children[0],
                &children[1],
                &children[2],
                &children[3],
                parse_tree,
            ),

            46 => self.scanner_switch_46(
                &children[0],
                &children[1],
                &children[2],
                &children[3],
                parse_tree,
            ),

            47 => self.scanner_switch_47(&children[0], &children[1], &children[2], parse_tree),

            48 => self.scanner_name_opt_48(&children[0], parse_tree),

            49 => self.scanner_name_opt_49(parse_tree),

            _ => Err(miette!("Unhandled production number: {}", prod_num)),
        }
    }
}
