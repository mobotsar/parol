// ---------------------------------------------------------
// This file was generated by parol.
// It is not intended for manual editing and changes will be
// lost after next build.
// ---------------------------------------------------------

#[allow(unused_imports)]
use crate::list_grammar::ListGrammar;
use id_tree::Tree;
use log::trace;
use miette::{miette, IntoDiagnostic, Result};
use parol_runtime::lexer::Token;
use parol_runtime::parser::{ParseTreeStackEntry, ParseTreeType, UserActionsTrait};
use std::path::{Path, PathBuf};

/// Semantic actions trait generated for the user grammar
/// All functions have default implementations.
pub trait ListGrammarTrait<'t> {
    fn init(&mut self, _file_name: &Path) {}

    /// Semantic action for user production 0:
    ///
    /// List: [Num {<0>"," Num}] TrailingComma;
    ///
    fn list(&mut self, _arg: &List<'t>) -> Result<()> {
        Ok(())
    }

    /// Semantic action for user production 1:
    ///
    /// Num: <0>"0|[1-9][0-9]*";
    ///
    fn num(&mut self, _arg: &Num<'t>) -> Result<()> {
        Ok(())
    }

    /// Semantic action for user production 2:
    ///
    /// TrailingComma: [<0>","];
    ///
    fn trailing_comma(&mut self, _arg: &TrailingComma<'t>) -> Result<()> {
        Ok(())
    }
}

// -------------------------------------------------------------------------------------------------
//
// Output Types of productions deduced from the structure of the transformed grammar
//

///
/// Type derived for production 0
///
/// List: Num ListList /* Vec */ TrailingComma;
///
#[allow(dead_code)]
#[derive(Builder, Debug, Clone)]
pub struct List0<'t> {
    pub num_0: Box<Num<'t>>,
    pub list_list_1: Vec<ListList<'t>>,
    pub trailing_comma_2: Box<TrailingComma<'t>>,
}

///
/// Type derived for production 3
///
/// List: TrailingComma;
///
#[allow(dead_code)]
#[derive(Builder, Debug, Clone)]
pub struct List3<'t> {
    pub trailing_comma_0: Box<TrailingComma<'t>>,
}

///
/// Type derived for production 5
///
/// TrailingComma: ",";
///
#[allow(dead_code)]
#[derive(Builder, Debug, Clone)]
pub struct TrailingComma5<'t> {
    pub comma_0: Token<'t>, /* , */
}

///
/// Type derived for production 6
///
/// TrailingComma: ;
///
#[allow(dead_code)]
#[derive(Builder, Debug, Clone)]
pub struct TrailingComma6 {}

// -------------------------------------------------------------------------------------------------
//
// Types of non-terminals deduced from the structure of the transformed grammar
//

///
/// Type derived for non-terminal List
///
#[allow(dead_code)]
#[derive(Debug, Clone)]
pub enum List<'t> {
    List0(List0<'t>),
    List3(List3<'t>),
}

///
/// Type derived for non-terminal ListList
///
#[allow(dead_code)]
#[derive(Builder, Debug, Clone)]
pub struct ListList<'t> {
    pub comma_0: Token<'t>, /* , */
    pub num_1: Box<Num<'t>>,
}

///
/// Type derived for non-terminal Num
///
#[allow(dead_code)]
#[derive(Builder, Debug, Clone)]
pub struct Num<'t> {
    pub num_0: Token<'t>, /* 0|[1-9][0-9]* */
}

///
/// Type derived for non-terminal TrailingComma
///
#[allow(dead_code)]
#[derive(Debug, Clone)]
pub enum TrailingComma<'t> {
    TrailingComma5(TrailingComma5<'t>),
    TrailingComma6(TrailingComma6),
}

// -------------------------------------------------------------------------------------------------

///
/// Deduced ASTType of expanded grammar
///
#[allow(dead_code)]
#[derive(Debug, Clone)]
pub enum ASTType<'t> {
    List(List<'t>),
    ListList(Vec<ListList<'t>>),
    Num(Num<'t>),
    TrailingComma(TrailingComma<'t>),
}

/// Auto-implemented adapter grammar
///
/// The lifetime parameter `'t` refers to the lifetime of the scanned text.
/// The lifetime parameter `'u` refers to the lifetime of user grammar object.
///
#[allow(dead_code)]
pub struct ListGrammarAuto<'t, 'u>
where
    't: 'u,
{
    // Mutable reference of the actual user grammar to be able to call the semantic actions on it
    user_grammar: &'u mut dyn ListGrammarTrait<'t>,
    // Stack to construct the AST on it
    item_stack: Vec<ASTType<'t>>,
    // Path of the input file. Used for diagnostics.
    file_name: PathBuf,
}

///
/// The `ListGrammarAuto` impl is automatically generated for the
/// given grammar.
///
impl<'t, 'u> ListGrammarAuto<'t, 'u> {
    pub fn new(user_grammar: &'u mut dyn ListGrammarTrait<'t>) -> Self {
        Self {
            user_grammar,
            item_stack: Vec::new(),
            file_name: PathBuf::default(),
        }
    }

    fn push(&mut self, item: ASTType<'t>, context: &str) {
        trace!("push    {}: {:?}", context, item);
        self.item_stack.push(item)
    }

    fn pop(&mut self, context: &str) -> Option<ASTType<'t>> {
        if !self.item_stack.is_empty() {
            let item = self.item_stack.pop();
            if let Some(ref item) = item {
                trace!("pop     {}: {:?}", context, item);
            }
            item
        } else {
            None
        }
    }

    #[allow(dead_code)]
    // Use this function for debugging purposes:
    // trace!("{}", self.trace_item_stack(context));
    fn trace_item_stack(&self, context: &str) -> std::string::String {
        format!(
            "Item stack at {}:\n{}",
            context,
            self.item_stack
                .iter()
                .rev()
                .map(|s| format!("  {:?}", s))
                .collect::<Vec<std::string::String>>()
                .join("\n")
        )
    }

    /// Semantic action for production 0:
    ///
    /// List: Num ListList /* Vec */ TrailingComma;
    ///
    fn list_0(
        &mut self,
        _num_0: &ParseTreeStackEntry<'t>,
        _list_list_1: &ParseTreeStackEntry<'t>,
        _trailing_comma_2: &ParseTreeStackEntry<'t>,
        _parse_tree: &Tree<ParseTreeType<'t>>,
    ) -> Result<()> {
        let context = "list_0";
        trace!("{}", self.trace_item_stack(context));
        let trailing_comma_2 =
            if let Some(ASTType::TrailingComma(trailing_comma_2)) = self.pop(context) {
                trailing_comma_2
            } else {
                return Err(miette!("{}: Expecting ASTType::TrailingComma", context));
            };
        let list_list_1 = if let Some(ASTType::ListList(mut list_list_1)) = self.pop(context) {
            list_list_1.reverse();
            list_list_1
        } else {
            return Err(miette!("{}: Expecting ASTType::ListList", context));
        };
        let num_0 = if let Some(ASTType::Num(num_0)) = self.pop(context) {
            num_0
        } else {
            return Err(miette!("{}: Expecting ASTType::Num", context));
        };
        let list_0_built = List0Builder::default()
            .num_0(Box::new(num_0))
            .list_list_1(list_list_1)
            .trailing_comma_2(Box::new(trailing_comma_2))
            .build()
            .into_diagnostic()?;
        let list_0_built = List::List0(list_0_built);
        // Calling user action here
        self.user_grammar.list(&list_0_built)?;
        self.push(ASTType::List(list_0_built), context);
        Ok(())
    }

    /// Semantic action for production 1:
    ///
    /// ListList: "," Num ListList; // Vec<T>::Push
    ///
    fn list_list_1(
        &mut self,
        comma_0: &ParseTreeStackEntry<'t>,
        _num_1: &ParseTreeStackEntry<'t>,
        _list_list_2: &ParseTreeStackEntry<'t>,
        parse_tree: &Tree<ParseTreeType<'t>>,
    ) -> Result<()> {
        let context = "list_list_1";
        trace!("{}", self.trace_item_stack(context));
        let comma_0 = *comma_0.token(parse_tree)?;
        let mut list_list_2 = if let Some(ASTType::ListList(list_list_2)) = self.pop(context) {
            list_list_2
        } else {
            return Err(miette!("{}: Expecting ASTType::ListList", context));
        };
        let num_1 = if let Some(ASTType::Num(num_1)) = self.pop(context) {
            num_1
        } else {
            return Err(miette!("{}: Expecting ASTType::Num", context));
        };
        let list_list_1_built = ListListBuilder::default()
            .num_1(Box::new(num_1))
            .comma_0(comma_0)
            .build()
            .into_diagnostic()?;
        // Add an element to the vector
        list_list_2.push(list_list_1_built);
        self.push(ASTType::ListList(list_list_2), context);
        Ok(())
    }

    /// Semantic action for production 2:
    ///
    /// ListList: ; // Vec<T>::New
    ///
    fn list_list_2(&mut self, _parse_tree: &Tree<ParseTreeType<'t>>) -> Result<()> {
        let context = "list_list_2";
        trace!("{}", self.trace_item_stack(context));
        let list_list_2_built = Vec::new();
        self.push(ASTType::ListList(list_list_2_built), context);
        Ok(())
    }

    /// Semantic action for production 3:
    ///
    /// List: TrailingComma;
    ///
    fn list_3(
        &mut self,
        _trailing_comma_0: &ParseTreeStackEntry<'t>,
        _parse_tree: &Tree<ParseTreeType<'t>>,
    ) -> Result<()> {
        let context = "list_3";
        trace!("{}", self.trace_item_stack(context));
        let trailing_comma_0 =
            if let Some(ASTType::TrailingComma(trailing_comma_0)) = self.pop(context) {
                trailing_comma_0
            } else {
                return Err(miette!("{}: Expecting ASTType::TrailingComma", context));
            };
        let list_3_built = List3Builder::default()
            .trailing_comma_0(Box::new(trailing_comma_0))
            .build()
            .into_diagnostic()?;
        let list_3_built = List::List3(list_3_built);
        // Calling user action here
        self.user_grammar.list(&list_3_built)?;
        self.push(ASTType::List(list_3_built), context);
        Ok(())
    }

    /// Semantic action for production 4:
    ///
    /// Num: "0|[1-9][0-9]*";
    ///
    fn num_4(
        &mut self,
        num_0: &ParseTreeStackEntry<'t>,
        parse_tree: &Tree<ParseTreeType<'t>>,
    ) -> Result<()> {
        let context = "num_4";
        trace!("{}", self.trace_item_stack(context));
        let num_0 = *num_0.token(parse_tree)?;
        let num_4_built = NumBuilder::default()
            .num_0(num_0)
            .build()
            .into_diagnostic()?;
        // Calling user action here
        self.user_grammar.num(&num_4_built)?;
        self.push(ASTType::Num(num_4_built), context);
        Ok(())
    }

    /// Semantic action for production 5:
    ///
    /// TrailingComma: ",";
    ///
    fn trailing_comma_5(
        &mut self,
        comma_0: &ParseTreeStackEntry<'t>,
        parse_tree: &Tree<ParseTreeType<'t>>,
    ) -> Result<()> {
        let context = "trailing_comma_5";
        trace!("{}", self.trace_item_stack(context));
        let comma_0 = *comma_0.token(parse_tree)?;
        let trailing_comma_5_built = TrailingComma5Builder::default()
            .comma_0(comma_0)
            .build()
            .into_diagnostic()?;
        let trailing_comma_5_built = TrailingComma::TrailingComma5(trailing_comma_5_built);
        // Calling user action here
        self.user_grammar.trailing_comma(&trailing_comma_5_built)?;
        self.push(ASTType::TrailingComma(trailing_comma_5_built), context);
        Ok(())
    }

    /// Semantic action for production 6:
    ///
    /// TrailingComma: ;
    ///
    fn trailing_comma_6(&mut self, _parse_tree: &Tree<ParseTreeType<'t>>) -> Result<()> {
        let context = "trailing_comma_6";
        trace!("{}", self.trace_item_stack(context));
        let trailing_comma_6_built = TrailingComma6Builder::default().build().into_diagnostic()?;
        let trailing_comma_6_built = TrailingComma::TrailingComma6(trailing_comma_6_built);
        // Calling user action here
        self.user_grammar.trailing_comma(&trailing_comma_6_built)?;
        self.push(ASTType::TrailingComma(trailing_comma_6_built), context);
        Ok(())
    }
}

impl<'t> UserActionsTrait<'t> for ListGrammarAuto<'t, '_> {
    ///
    /// Initialize the user with additional information.
    /// This function is called by the parser before parsing starts.
    /// Is is used to transport necessary data from parser to user.
    ///
    fn init(&mut self, file_name: &Path) {
        self.file_name = file_name.to_owned();
        self.user_grammar.init(file_name);
    }

    ///
    /// This function is implemented automatically for the user's item ListGrammar.
    ///
    fn call_semantic_action_for_production_number(
        &mut self,
        prod_num: usize,
        children: &[ParseTreeStackEntry<'t>],
        parse_tree: &Tree<ParseTreeType<'t>>,
    ) -> Result<()> {
        match prod_num {
            0 => self.list_0(&children[0], &children[1], &children[2], parse_tree),
            1 => self.list_list_1(&children[0], &children[1], &children[2], parse_tree),
            2 => self.list_list_2(parse_tree),
            3 => self.list_3(&children[0], parse_tree),
            4 => self.num_4(&children[0], parse_tree),
            5 => self.trailing_comma_5(&children[0], parse_tree),
            6 => self.trailing_comma_6(parse_tree),
            _ => Err(miette!("Unhandled production number: {}", prod_num)),
        }
    }
}
