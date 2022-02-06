use crate::StrVec;

#[derive(BartDisplay, Debug, Default)]
#[template = "templates/user_trait_caller_function_template.rs"]
pub(crate) struct UserTraitCallerFunctionData {
    pub fn_name: String,
    pub prod_num: usize,
    pub fn_arguments: String,
}

#[derive(BartDisplay, Debug, Default)]
#[template = "templates/user_trait_function_template.rs"]
pub(crate) struct UserTraitFunctionData<'a> {
    pub fn_name: &'a str,
    pub prod_num: usize,
    pub fn_arguments: String,
    pub prod_string: String,
    pub code: StrVec,
    // Inner means the expanded version of the grammar.
    // If set to false the actual user grammar is meant.
    pub inner: bool,
}

#[derive(BartDisplay, Debug, Default)]
#[template = "templates/user_trait_template.rs"]
pub(crate) struct UserTraitData<'a> {
    pub user_type_name: String,
    pub auto_generate: bool,
    pub production_output_types: StrVec,
    pub non_terminal_types: StrVec,
    pub ast_type_decl: String,
    pub trait_functions: StrVec,
    pub trait_caller: StrVec,
    pub module_name: &'a str,
    pub user_trait_functions: StrVec,
}

#[derive(BartDisplay, Debug, Default)]
#[template = "templates/non_terminal_type_struct_template.rs"]
pub(crate) struct NonTerminalTypeStruct {
    pub comment: String,
    pub non_terminal: String,
    pub members: StrVec,
}

#[derive(BartDisplay, Debug, Default)]
#[template = "templates/non_terminal_type_enum_template.rs"]
pub(crate) struct NonTerminalTypeEnum {
    pub comment: String,
    pub non_terminal: String,
    pub members: StrVec,
}

#[derive(BartDisplay, Debug, Default)]
#[template = "templates/non_terminal_type_vec_template.rs"]
pub(crate) struct NonTerminalTypeVec {
    pub comment: String,
    pub non_terminal: String,
    pub members: String,
}

#[derive(BartDisplay, Debug, Default)]
#[template = "templates/non_terminal_type_opt_template.rs"]
pub(crate) struct NonTerminalTypeOpt {
    pub comment: String,
    pub non_terminal: String,
    pub members: String,
}
