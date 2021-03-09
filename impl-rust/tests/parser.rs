extern crate lib;
extern crate nom;
use lib::lambda::term::Term;

#[test]
fn test() {
    let cases = vec![
        ("xyz", Term::Var("xyz".to_string())),
        ("(xyz)", Term::Var("xyz".to_string())),
        (
            "f x ",
            Term::App(
                Box::new(Term::Var("f".to_string())),
                Box::new(Term::Var("x".to_string())),
            ),
        ),
        (
            "fun x->f x",
            Term::Lambda(
                "x".to_string(),
                Box::new(Term::App(
                    Box::new(Term::Var("f".to_string())),
                    Box::new(Term::Var("x".to_string())),
                )),
            ),
        ),
    ];
    for (s, t) in cases.into_iter() {
        assert_eq!(
            nom::combinator::all_consuming(lib::lambda::parser::term)(s),
            Ok(("", t))
        );
    }
}
