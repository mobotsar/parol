    /// Semantic action for {{^inner?}}user {{/inner}}production {{prod_num}}:
    /// 
    /// {{{prod_string}}}
    /// 
    fn {{fn_name}}{{#inner?}}_{{prod_num}}{{/inner}}(&mut self, {{{fn_arguments}}}) -> Result<()> {
        {{code}}Ok(())
    }
