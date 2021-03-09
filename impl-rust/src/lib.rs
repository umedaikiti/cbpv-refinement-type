#[macro_use]
extern crate lazy_static;
extern crate regex;
pub mod context;
pub mod lambda;
pub mod logic;
pub mod refinement;
pub mod smtlib;
pub mod underlying;
pub mod utils;

#[cfg(test)]
mod tests {
    #[test]
    fn test_unify() {
        use super::underlying::r#type::*;
        use super::underlying::unification::*;
        assert!((Constraints {
            value: vec![(
                Value::Var("x".to_string()),
                Value::Sum(Box::new(Value::Var("x".to_string())), Box::new(Value::Int)),
            )],
            computation: vec![],
        })
        .unify()
        .is_err());
    }
    #[test]
    fn test_display_underlying_type() {
        use super::underlying::r#type::*;
        let tests_computation = [
            (
                Computation::Function(
                    Box::new(Value::U(Box::new(Computation::Function(
                        Box::new(Value::Int),
                        Box::new(Computation::F(Box::new(Value::Int))),
                    )))),
                    Box::new(Computation::Function(
                        Box::new(Value::Int),
                        Box::new(Computation::F(Box::new(Value::Int))),
                    )),
                ),
                "U (int -> F int) -> int -> F int",
            ),
            (
                Computation::F(Box::new(Value::U(Box::new(Computation::F(Box::new(
                    Value::Int,
                )))))),
                "F U F int",
            ),
            (
                Computation::Function(
                    Box::new(Value::Pair(
                        Box::new(Value::Int),
                        Box::new(Value::Sum(Box::new(Value::Int), Box::new(Value::Int))),
                    )),
                    Box::new(Computation::F(Box::new(Value::Int))),
                ),
                "(int * (int + int)) -> F int",
            ),
        ];
        for (t, s) in tests_computation.iter() {
            assert_eq!(t.to_string(), s.to_string());
        }
    }
}
