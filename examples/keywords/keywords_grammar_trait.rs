// ---------------------------------------------------------
// This file was generated by parol.
// It is not intended for manual editing and changes will be
// lost after next build.
// ---------------------------------------------------------

use id_tree::Tree;

use miette::{miette, Result};
use parol_runtime::parser::{ParseTreeStackEntry, ParseTreeType, UserActionsTrait};

use crate::keywords_grammar::KeywordsGrammar;
use std::path::Path;

///
/// The `KeywordsGrammarTrait` trait is automatically generated for the
/// given grammar.
/// All functions have default implementations.
///
pub trait KeywordsGrammarTrait {
    ///
    /// Implement this method if you need the provided information
    ///
    fn init(&mut self, _file_name: &Path) {}

    /// Semantic action for production 0:
    ///
    /// Grammar: GrammarList /* Vec */;
    ///
    fn grammar_0(
        &mut self,
        _grammar_list_0: &ParseTreeStackEntry,
        _parse_tree: &Tree<ParseTreeType>,
    ) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 1:
    ///
    /// GrammarList: Items GrammarList; // Vec<T>::Push
    ///
    fn grammar_list_1(
        &mut self,
        _items_0: &ParseTreeStackEntry,
        _grammar_list_1: &ParseTreeStackEntry,
        _parse_tree: &Tree<ParseTreeType>,
    ) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 2:
    ///
    /// GrammarList: ; // Vec<T>::New
    ///
    fn grammar_list_2(&mut self, _parse_tree: &Tree<ParseTreeType>) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 3:
    ///
    /// Items: Declaration;
    ///
    fn items_3(
        &mut self,
        _declaration_0: &ParseTreeStackEntry,
        _parse_tree: &Tree<ParseTreeType>,
    ) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 4:
    ///
    /// Items: Block;
    ///
    fn items_4(
        &mut self,
        _block_0: &ParseTreeStackEntry,
        _parse_tree: &Tree<ParseTreeType>,
    ) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 5:
    ///
    /// Declaration: Var Identifier ";";
    ///
    fn declaration_5(
        &mut self,
        _var_0: &ParseTreeStackEntry,
        _identifier_1: &ParseTreeStackEntry,
        _semicolon_2: &ParseTreeStackEntry,
        _parse_tree: &Tree<ParseTreeType>,
    ) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 6:
    ///
    /// Block: Begin BlockList /* Vec */ End;
    ///
    fn block_6(
        &mut self,
        _begin_0: &ParseTreeStackEntry,
        _block_list_1: &ParseTreeStackEntry,
        _end_2: &ParseTreeStackEntry,
        _parse_tree: &Tree<ParseTreeType>,
    ) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 7:
    ///
    /// BlockList: Items BlockList; // Vec<T>::Push
    ///
    fn block_list_7(
        &mut self,
        _items_0: &ParseTreeStackEntry,
        _block_list_1: &ParseTreeStackEntry,
        _parse_tree: &Tree<ParseTreeType>,
    ) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 8:
    ///
    /// BlockList: ; // Vec<T>::New
    ///
    fn block_list_8(&mut self, _parse_tree: &Tree<ParseTreeType>) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 9:
    ///
    /// Begin: "(?i)\bBegin\b";
    ///
    fn begin_9(
        &mut self,
        _begin_0: &ParseTreeStackEntry,
        _parse_tree: &Tree<ParseTreeType>,
    ) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 10:
    ///
    /// End: "(?i)\bEnd\b";
    ///
    fn end_10(
        &mut self,
        _end_0: &ParseTreeStackEntry,
        _parse_tree: &Tree<ParseTreeType>,
    ) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 11:
    ///
    /// Var: "(?i)\bVar\b";
    ///
    fn var_11(
        &mut self,
        _var_0: &ParseTreeStackEntry,
        _parse_tree: &Tree<ParseTreeType>,
    ) -> Result<()> {
        Ok(())
    }

    /// Semantic action for production 12:
    ///
    /// Identifier: "[a-zA-Z_][a-zA-Z0-9_]*";
    ///
    fn identifier_12(
        &mut self,
        _identifier_0: &ParseTreeStackEntry,
        _parse_tree: &Tree<ParseTreeType>,
    ) -> Result<()> {
        Ok(())
    }
}

impl UserActionsTrait<'_> for KeywordsGrammar {
    ///
    /// Initialize the user with additional information.
    /// This function is called by the parser before parsing starts.
    /// Is is used to transport necessary data from parser to user.
    ///
    fn init(&mut self, _file_name: &Path) {}

    ///
    /// This function is implemented automatically for the user's item KeywordsGrammar.
    ///
    fn call_semantic_action_for_production_number(
        &mut self,
        prod_num: usize,
        children: &[ParseTreeStackEntry],
        parse_tree: &Tree<ParseTreeType>,
    ) -> Result<()> {
        match prod_num {
            0 => self.grammar_0(&children[0], parse_tree),
            1 => self.grammar_list_1(&children[0], &children[1], parse_tree),
            2 => self.grammar_list_2(parse_tree),
            3 => self.items_3(&children[0], parse_tree),
            4 => self.items_4(&children[0], parse_tree),
            5 => self.declaration_5(&children[0], &children[1], &children[2], parse_tree),
            6 => self.block_6(&children[0], &children[1], &children[2], parse_tree),
            7 => self.block_list_7(&children[0], &children[1], parse_tree),
            8 => self.block_list_8(parse_tree),
            9 => self.begin_9(&children[0], parse_tree),
            10 => self.end_10(&children[0], parse_tree),
            11 => self.var_11(&children[0], parse_tree),
            12 => self.identifier_12(&children[0], parse_tree),
            _ => Err(miette!("Unhandled production number: {}", prod_num)),
        }
    }
}
