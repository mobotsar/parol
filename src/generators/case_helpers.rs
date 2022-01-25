///
/// Produces a lower snake camel case version of the given name.
///
/// ```
/// use parol::generators::case_helpers::to_lower_snake_case;
/// assert_eq!("prolog_0", to_lower_snake_case("Prolog0"));
/// assert_eq!("_prolog_0_", to_lower_snake_case("_prolog_0_"));
/// assert_eq!("_prolog_0_1_3", to_lower_snake_case("_prolog_0_1__3"));
/// assert_eq!("_", to_lower_snake_case("_____"));
/// ```
pub fn to_lower_snake_case(name: &str) -> String {
    name.chars().fold(String::new(), |mut acc, c| {
        if acc.is_empty() {
            acc.push(c.to_lowercase().next().unwrap())
        } else if c == '_' {
            if !acc.ends_with('_') {
                acc.push('_');
            }
        } else if c.is_ascii_uppercase() || c.is_ascii_digit() {
            if !acc.ends_with('_') {
                acc.push('_');
            }
            acc.push(c.to_lowercase().next().unwrap())
        } else {
            acc.push(c);
        }
        acc
    })
}

///
/// Produces an upper camel case version of the given name.
/// Separated numbers are kept separated.
///
/// ```
/// use parol::generators::case_helpers::to_upper_camel_case;
/// assert_eq!("Prolog0", to_upper_camel_case("_prolog_0"));
/// assert_eq!("Prolog0", to_upper_camel_case("_prolog_0_"));
/// assert_eq!("Prolog0", to_upper_camel_case("_prolog_0__"));
/// assert_eq!("Prolog0_1", to_upper_camel_case("_prolog_0__1"));
/// assert_eq!("Prolog0_1_10_20", to_upper_camel_case("_prolog_0__1_10___20__"));
/// assert_eq!("Prolog0A", to_upper_camel_case("_prolog_0__a"));
/// assert_eq!("PrologAA", to_upper_camel_case("_prolog_a_a"));
/// assert_eq!("PrologItem", to_upper_camel_case("prolog_item"));
/// assert_eq!("AA", to_upper_camel_case("_a_a_"));
/// ```
pub fn to_upper_camel_case(name: &str) -> String {
    let mut up = true;
    let mut last_char = '.';
    name.chars().fold(String::new(), |mut acc, c| {
        if c == '_' {
            up = true;
        } else {
            if up {
                if last_char.is_ascii_digit() && c.is_ascii_digit() {
                    acc.push('_');
                }
                last_char = c.to_uppercase().next().unwrap();
                acc.push(last_char);
                up = false;
            } else {
                last_char = c.to_lowercase().next().unwrap();
                acc.push(last_char);
            }
        }
        acc
    })
}
