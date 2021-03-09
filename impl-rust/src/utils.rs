use regex::Regex;

pub fn mk_fresh_name(s: &str, exclude: &std::collections::HashSet<String>) -> String {
    lazy_static! {
        static ref RE: Regex = Regex::new("^(?P<base>.*)!\\d+$").unwrap();
    }
    let base = RE.replace_all(s, "$base");
    if exclude.contains(&base.to_string()) {
        let mut i = 0;
        while exclude.contains(&format!("{base}!{num}", base = base, num = i)) {
            i += 1;
        }
        format!("{base}!{num}", base = base, num = i)
    } else {
        base.to_string()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;

    #[test]
    fn test_mk_fresh_name() {
        assert_eq!("test", mk_fresh_name("test", &HashSet::new()));
        assert_eq!(
            "x!0",
            mk_fresh_name("x!1", &["x".to_string()].iter().cloned().collect())
        );
        assert_eq!(
            "x!0",
            mk_fresh_name("x", &["x".to_string()].iter().cloned().collect())
        );
        assert_eq!(
            "x!1",
            mk_fresh_name(
                "x",
                &["x".to_string(), "x!0".to_string()]
                    .iter()
                    .cloned()
                    .collect()
            )
        );
    }
}
