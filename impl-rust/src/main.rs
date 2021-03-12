//#[macro_use]
extern crate lib;
extern crate nom;
use lib::context::Context;
use lib::lambda;
use lib::refinement::infer;
use lib::underlying;
use std::collections::HashSet;

fn main() {
    let mut parser = nom::combinator::all_consuming(lambda::parser::term);
    let parse_tests = [
        "xyz",
        "(xyz)",
        "f x ",
        "fun x->f x",
        "fun f x -> f x",
        "(fun f x -> f x) f y",
        "(fun x y -> (x, y)) () x",
        "inl () x",
        "inl inl ()",
        "case inl () in inl x -> x | inr y -> y",
        "match (x, y) with (x, y) -> x",
        "fail",
        "123",
        "fun x x -> x",
    ];
    for s in parse_tests.iter() {
        println!("input: {}", s);
        let (_, t) = parser(s).unwrap();
        println!("{:?}", t);
    }
    let inference_tests = [
        "case leq 1 2 in inl x -> () | inr x -> fail",
        "fun x -> case leq x (add x 1) in inl y -> x | inr y -> add x 1",
        "fun x -> add x 1",
        "let rec f x = add x 1 in f",
        "let rec f x = case leq 0 x in inl z -> add x (f (add x (-1))) | inr z -> 0 in case leq 0 (f ?) in inl y -> () | inr y -> fail",
    ];
    for s in inference_tests.iter() {
        println!("input");
        println!("{}", s);
        let (_, t) = parser(s).unwrap();
        println!("parse result");
        println!("{:#?}", t);
        let (_, term) = underlying::translate::cbv_of_lambda(&Context::new(), &t);
        println!("cbv");
        println!("{:#?}", term);
        let term = term.simplify(&HashSet::new());
        println!("simplified term");
        println!("{:#?}", term);
        let (m, ty) = term.infer(&mut Context::new()).unwrap();
        let term = term.subst_type(&m);
        println!("simple type inference");
        println!("{:?} : {}", term, ty.subst(&m));
        if m.fv_cod().is_empty() {
            let mut used_pvar = Context::new();
            let (c, t) = infer::computation(&mut Context::new(), &term, &mut used_pvar);
            println!("raw constraints");
            for c in c.iter() {
                println!("{:?}", c);
            }
            let (used_pvar, c) = lib::logic::simplify(used_pvar, c);
            println!("simplified constraints");
            println!("{:?}", used_pvar);
            for c in c.iter() {
                println!("{:?}", c);
            }
            let smtlib = lib::logic::to_smtlib(&used_pvar, &c).unwrap();
            println!("refinement type");
            println!("{}", t);
            println!("SMT-LIB");
            println!("{}", smtlib);
        }
    }
    for s in inference_tests.iter() {
        println!("input: {}", s);
        let (_, t) = parser(s).unwrap();
        let (_, term) = underlying::translate::cbn_of_lambda(&Context::new(), &t);
        println!("{:?}", term);
        let term = term.simplify(&HashSet::new());
        println!("{:?}", term);
        let (m, ty) = term.infer(&mut Context::new()).unwrap();
        let term = term.subst_type(&m);
        println!("{:?} : {}", term, ty.subst(&m));
        if m.fv_cod().is_empty() {
            let mut used_pvar = Context::new();
            let (c, t) = infer::computation(&mut Context::new(), &term, &mut used_pvar);
            let (used_pvar, c) = lib::logic::simplify(used_pvar, c);
            let smtlib = lib::logic::to_smtlib(&used_pvar, &c).unwrap();
            println!("{}", t);
            println!("{}", smtlib);
        }
    }
}
