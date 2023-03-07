// ---------------------------------------------------------
// This file was generated by parol.
// It is not intended for manual editing and changes will be
// lost after next build.
// ---------------------------------------------------------

// Disable clippy warnings that can result in the way how parol generates code.
#![allow(clippy::enum_variant_names)]
#![allow(clippy::large_enum_variant)]
#![allow(clippy::upper_case_acronyms)]

use parol_runtime::derive_builder::Builder;
use parol_runtime::log::trace;
#[allow(unused_imports)]
use parol_runtime::parol_macros::{pop_and_reverse_item, pop_item};
use parol_runtime::parser::{ParseTreeType, UserActionsTrait};
use parol_runtime::{ParserError, Result};
use std::marker::PhantomData;

/// Semantic actions trait generated for the user grammar
/// All functions have default implementations.
pub trait ListGrammarTrait {
    /// Semantic action for non-terminal 'List'
    fn list(&mut self, _arg: &List) -> Result<()> {
        Ok(())
    }

    /// Semantic action for non-terminal 'Items'
    fn items(&mut self, _arg: &Items) -> Result<()> {
        Ok(())
    }

    /// Semantic action for non-terminal 'Num'
    fn num(&mut self, _arg: &Num) -> Result<()> {
        Ok(())
    }

    /// Semantic action for non-terminal 'TrailingComma'
    fn trailing_comma(&mut self, _arg: &TrailingComma) -> Result<()> {
        Ok(())
    }
}

// -------------------------------------------------------------------------------------------------
//
// Output Types of productions deduced from the structure of the transformed grammar
//

// -------------------------------------------------------------------------------------------------
//
// Types of non-terminals deduced from the structure of the transformed grammar
//

///
/// Type derived for non-terminal Items
///
#[allow(dead_code)]
#[derive(Builder, Debug, Clone)]
#[builder(crate = "parol_runtime::derive_builder")]
pub struct Items {
    pub num: Box<Num>,
    pub items_list: Vec<ItemsList>,
}

///
/// Type derived for non-terminal ItemsList
///
#[allow(dead_code)]
#[derive(Builder, Debug, Clone)]
#[builder(crate = "parol_runtime::derive_builder")]
pub struct ItemsList {
    pub num: Box<Num>,
}

///
/// Type derived for non-terminal List
///
#[allow(dead_code)]
#[derive(Builder, Debug, Clone)]
#[builder(crate = "parol_runtime::derive_builder")]
pub struct List {
    pub list_opt: Option<Box<ListOpt>>,
}

///
/// Type derived for non-terminal ListOpt
///
#[allow(dead_code)]
#[derive(Builder, Debug, Clone)]
#[builder(crate = "parol_runtime::derive_builder")]
pub struct ListOpt {
    pub items: crate::list_grammar::Numbers,
}

///
/// Type derived for non-terminal Num
///
#[allow(dead_code)]
#[derive(Builder, Debug, Clone)]
#[builder(crate = "parol_runtime::derive_builder")]
pub struct Num {
    pub num: crate::list_grammar::Number, /* 0|[1-9][0-9]* */
}

///
/// Type derived for non-terminal TrailingComma
///
#[allow(dead_code)]
#[derive(Builder, Debug, Clone)]
#[builder(crate = "parol_runtime::derive_builder")]
pub struct TrailingComma {
    pub trailing_comma_opt: Option<Box<TrailingCommaOpt>>,
}

///
/// Type derived for non-terminal TrailingCommaOpt
///
#[allow(dead_code)]
#[derive(Builder, Debug, Clone)]
#[builder(crate = "parol_runtime::derive_builder")]
pub struct TrailingCommaOpt {}

// -------------------------------------------------------------------------------------------------

///
/// Deduced ASTType of expanded grammar
///
#[allow(dead_code)]
#[derive(Debug, Clone)]
pub enum ASTType {
    Items(Items),
    ItemsList(Vec<ItemsList>),
    List(List),
    ListOpt(Option<Box<ListOpt>>),
    Num(Num),
    TrailingComma(TrailingComma),
    TrailingCommaOpt(Option<Box<TrailingCommaOpt>>),
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
    user_grammar: &'u mut dyn ListGrammarTrait,
    // Stack to construct the AST on it
    item_stack: Vec<ASTType>,
    // Just to hold the lifetime generated by parol
    phantom: PhantomData<&'t str>,
}

///
/// The `ListGrammarAuto` impl is automatically generated for the
/// given grammar.
///
impl<'t, 'u> ListGrammarAuto<'t, 'u> {
    pub fn new(user_grammar: &'u mut dyn ListGrammarTrait) -> Self {
        Self {
            user_grammar,
            item_stack: Vec::new(),
            phantom: PhantomData::default(),
        }
    }

    #[allow(dead_code)]
    fn push(&mut self, item: ASTType, context: &str) {
        trace!("push    {}: {:?}", context, item);
        self.item_stack.push(item)
    }

    #[allow(dead_code)]
    fn pop(&mut self, context: &str) -> Option<ASTType> {
        let item = self.item_stack.pop();
        if let Some(ref item) = item {
            trace!("pop     {}: {:?}", context, item);
        }
        item
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
    /// List: ListOpt /* Option */ TrailingComma^ /* Clipped */;
    ///
    #[parol_runtime::function_name::named]
    fn list(
        &mut self,
        _list_opt: &ParseTreeType<'t>,
        _trailing_comma: &ParseTreeType<'t>,
    ) -> Result<()> {
        let context = function_name!();
        trace!("{}", self.trace_item_stack(context));
        // Ignore clipped member 'trailing_comma'
        self.pop(context);
        let list_opt = pop_item!(self, list_opt, ListOpt, context);
        let list_built = List {
            list_opt,
            // Ignore clipped member 'trailing_comma'
        };
        // Calling user action here
        self.user_grammar.list(&list_built)?;
        self.push(ASTType::List(list_built), context);
        Ok(())
    }

    /// Semantic action for production 1:
    ///
    /// ListOpt /* Option<T>::Some */: Items : Numbers;
    ///
    #[parol_runtime::function_name::named]
    fn list_opt_0(&mut self, _items: &ParseTreeType<'t>) -> Result<()> {
        let context = function_name!();
        trace!("{}", self.trace_item_stack(context));
        let items = pop_item!(self, items, Items, context);
        let list_opt_0_built = ListOpt {
            items: (&items)
                .try_into()
                .map_err(parol_runtime::ParolError::UserError)?,
        };
        self.push(ASTType::ListOpt(Some(Box::new(list_opt_0_built))), context);
        Ok(())
    }

    /// Semantic action for production 2:
    ///
    /// ListOpt /* Option<T>::None */: ;
    ///
    #[parol_runtime::function_name::named]
    fn list_opt_1(&mut self) -> Result<()> {
        let context = function_name!();
        trace!("{}", self.trace_item_stack(context));
        self.push(ASTType::ListOpt(None), context);
        Ok(())
    }

    /// Semantic action for production 3:
    ///
    /// Items: Num ItemsList /* Vec */;
    ///
    #[parol_runtime::function_name::named]
    fn items(&mut self, _num: &ParseTreeType<'t>, _items_list: &ParseTreeType<'t>) -> Result<()> {
        let context = function_name!();
        trace!("{}", self.trace_item_stack(context));
        let items_list = pop_and_reverse_item!(self, items_list, ItemsList, context);
        let num = pop_item!(self, num, Num, context);
        let items_built = Items {
            num: Box::new(num),
            items_list,
        };
        // Calling user action here
        self.user_grammar.items(&items_built)?;
        self.push(ASTType::Items(items_built), context);
        Ok(())
    }

    /// Semantic action for production 4:
    ///
    /// ItemsList /* Vec<T>::Push */: ","^ /* Clipped */ Num ItemsList;
    ///
    #[parol_runtime::function_name::named]
    fn items_list_0(
        &mut self,
        _comma: &ParseTreeType<'t>,
        _num: &ParseTreeType<'t>,
        _items_list: &ParseTreeType<'t>,
    ) -> Result<()> {
        let context = function_name!();
        trace!("{}", self.trace_item_stack(context));
        let mut items_list = pop_item!(self, items_list, ItemsList, context);
        let num = pop_item!(self, num, Num, context);
        let items_list_0_built = ItemsList {
            num: Box::new(num),
            // Ignore clipped member 'comma'
        };
        // Add an element to the vector
        items_list.push(items_list_0_built);
        self.push(ASTType::ItemsList(items_list), context);
        Ok(())
    }

    /// Semantic action for production 5:
    ///
    /// ItemsList /* Vec<T>::New */: ;
    ///
    #[parol_runtime::function_name::named]
    fn items_list_1(&mut self) -> Result<()> {
        let context = function_name!();
        trace!("{}", self.trace_item_stack(context));
        let items_list_1_built = Vec::new();
        self.push(ASTType::ItemsList(items_list_1_built), context);
        Ok(())
    }

    /// Semantic action for production 6:
    ///
    /// Num: "0|[1-9][0-9]*" : Number;
    ///
    #[parol_runtime::function_name::named]
    fn num(&mut self, num: &ParseTreeType<'t>) -> Result<()> {
        let context = function_name!();
        trace!("{}", self.trace_item_stack(context));
        let num = num
            .token()?
            .try_into()
            .map_err(parol_runtime::ParolError::UserError)?;
        let num_built = Num { num };
        // Calling user action here
        self.user_grammar.num(&num_built)?;
        self.push(ASTType::Num(num_built), context);
        Ok(())
    }

    /// Semantic action for production 7:
    ///
    /// TrailingComma: TrailingCommaOpt /* Option */;
    ///
    #[parol_runtime::function_name::named]
    fn trailing_comma(&mut self, _trailing_comma_opt: &ParseTreeType<'t>) -> Result<()> {
        let context = function_name!();
        trace!("{}", self.trace_item_stack(context));
        let trailing_comma_opt = pop_item!(self, trailing_comma_opt, TrailingCommaOpt, context);
        let trailing_comma_built = TrailingComma { trailing_comma_opt };
        // Calling user action here
        self.user_grammar.trailing_comma(&trailing_comma_built)?;
        self.push(ASTType::TrailingComma(trailing_comma_built), context);
        Ok(())
    }

    /// Semantic action for production 8:
    ///
    /// TrailingCommaOpt /* Option<T>::Some */: ","^ /* Clipped */;
    ///
    #[parol_runtime::function_name::named]
    fn trailing_comma_opt_0(&mut self, _comma: &ParseTreeType<'t>) -> Result<()> {
        let context = function_name!();
        trace!("{}", self.trace_item_stack(context));
        let trailing_comma_opt_0_built = TrailingCommaOpt {
        // Ignore clipped member 'comma'
        };
        self.push(
            ASTType::TrailingCommaOpt(Some(Box::new(trailing_comma_opt_0_built))),
            context,
        );
        Ok(())
    }

    /// Semantic action for production 9:
    ///
    /// TrailingCommaOpt /* Option<T>::None */: ;
    ///
    #[parol_runtime::function_name::named]
    fn trailing_comma_opt_1(&mut self) -> Result<()> {
        let context = function_name!();
        trace!("{}", self.trace_item_stack(context));
        self.push(ASTType::TrailingCommaOpt(None), context);
        Ok(())
    }
}

impl<'t> UserActionsTrait<'t> for ListGrammarAuto<'t, '_> {
    ///
    /// This function is implemented automatically for the user's item ListGrammar.
    ///
    fn call_semantic_action_for_production_number(
        &mut self,
        prod_num: usize,
        children: &[ParseTreeType<'t>],
    ) -> Result<()> {
        match prod_num {
            0 => self.list(&children[0], &children[1]),
            1 => self.list_opt_0(&children[0]),
            2 => self.list_opt_1(),
            3 => self.items(&children[0], &children[1]),
            4 => self.items_list_0(&children[0], &children[1], &children[2]),
            5 => self.items_list_1(),
            6 => self.num(&children[0]),
            7 => self.trailing_comma(&children[0]),
            8 => self.trailing_comma_opt_0(&children[0]),
            9 => self.trailing_comma_opt_1(),
            _ => Err(ParserError::InternalError(format!(
                "Unhandled production number: {}",
                prod_num
            ))
            .into()),
        }
    }
}
