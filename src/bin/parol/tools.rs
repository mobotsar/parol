//! A registry for all the extra tools that can be used with parol.

pub type SubCommandFunc = fn() -> clap::App<'static, 'static>;
pub type ToolFunc = fn(&clap::ArgMatches) -> miette::Result<()>;

pub fn get_tool_sub_command(name: &str) -> Option<SubCommandFunc> {
    TOOLS
        .iter()
        .find(|(actual_name, _, _)| *actual_name == name)
        .map(|tool| tool.1)
}

pub fn get_tool_main(name: &str) -> Option<ToolFunc> {
    TOOLS
        .iter()
        .find(|(actual_name, _, _)| *actual_name == name)
        .map(|tool| tool.2)
}

pub fn names() -> impl Iterator<Item = &'static str> {
    TOOLS.iter().map(|(name, _, _)| *name)
}

/*
 * For each specified tool name this
 *
 * 1. Declares `mod $tool`
 * 2. Registers it in the table of tools
 */
macro_rules! declare_tools {
    ($($tool:ident),*) => {
        $(mod $tool;)*
        pub static TOOLS: &[(&str, SubCommandFunc, ToolFunc)] = &[
            $((stringify!($tool), self::$tool::sub_command, self::$tool::main)),*
        ];
    }
}

declare_tools!(
    calculate_k,
    calculate_k_tuples,
    decidable,
    deduce_types,
    first,
    follow,
    format,
    generate,
    left_factor,
    left_recursions,
    productivity,
    serialize
);
