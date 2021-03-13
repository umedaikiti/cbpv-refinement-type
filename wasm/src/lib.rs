extern crate lib;
extern crate nom;
extern crate wasm_bindgen;
use lib::context::Context;
use lib::lambda;
use lib::refinement::infer_debug;
use lib::underlying;
use serde::{Deserialize, Serialize};
use std::collections::HashSet;
use std::fmt::Write;

use wasm_bindgen::prelude::*;

#[wasm_bindgen]
extern "C" {
    pub fn alert(s: &str);
    #[wasm_bindgen(js_namespace = console)]
    fn log(s: &str);
}

#[wasm_bindgen]
pub fn greet(name: &str) {
    alert(&format!("Hello, {}!", name));
}

#[wasm_bindgen]
pub fn parser(s: &str) -> String {
    match nom::combinator::all_consuming(lambda::parser::term)(s) {
        Ok((_, t)) => format!("{:?}", t),
        Err(e) => format!("parse error: {}", e.to_string()),
    }
}

#[derive(Serialize, Deserialize)]
enum AST {
    Term {
        name: String,
        children: Vec<AST>,
        r#type: String,
    },
    Binder {
        name: String,
        child: Box<AST>,
        r#type: String,
    },
}

fn value_to_ast(v: &infer_debug::Value) -> AST {
    match &v.term {
        infer_debug::ValueTerm::Var(x) => AST::Term {
            name: format!("Var({})", x),
            children: Vec::new(),
            r#type: v.ty.to_string(),
        },
        infer_debug::ValueTerm::Unit => AST::Term {
            name: "Unit".to_string(),
            children: Vec::new(),
            r#type: v.ty.to_string(),
        },
        infer_debug::ValueTerm::Int(i) => AST::Term {
            name: format!("Int({})", i),
            children: Vec::new(),
            r#type: v.ty.to_string(),
        },
        infer_debug::ValueTerm::Inl(w, _) => AST::Term {
            name: "Inl".to_string(),
            children: vec![value_to_ast(w)],
            r#type: v.ty.to_string(),
        },
        infer_debug::ValueTerm::Inr(w, _) => AST::Term {
            name: "Inr".to_string(),
            children: vec![value_to_ast(w)],
            r#type: v.ty.to_string(),
        },
        infer_debug::ValueTerm::Pair(w1, w2) => AST::Term {
            name: "Pair".to_string(),
            children: vec![value_to_ast(w1), value_to_ast(w2)],
            r#type: v.ty.to_string(),
        },
        infer_debug::ValueTerm::Thunk(m) => AST::Term {
            name: "Thunk".to_string(),
            children: vec![computation_to_ast(m)],
            r#type: v.ty.to_string(),
        },
    }
}
fn computation_to_ast(m: &infer_debug::Computation) -> AST {
    match &m.term {
        infer_debug::ComputationTerm::Return(v) => AST::Term {
            name: "Return".to_string(),
            children: vec![value_to_ast(v)],
            r#type: m.ty.to_string(),
        },
        infer_debug::ComputationTerm::SeqComp(n1, (x, a), n2) => AST::Term {
            name: "SeqComp".to_string(),
            children: vec![
                computation_to_ast(n1),
                AST::Binder {
                    name: x.clone(),
                    child: Box::new(computation_to_ast(n2)),
                    r#type: a.to_string(),
                },
            ],
            r#type: m.ty.to_string(),
        },
        infer_debug::ComputationTerm::App(n, v) => AST::Term {
            name: "App".to_string(),
            children: vec![computation_to_ast(n), value_to_ast(v)],
            r#type: m.ty.to_string(),
        },
        infer_debug::ComputationTerm::Lambda((x, a), n) => AST::Term {
            name: "Lambda".to_string(),
            children: vec![AST::Binder {
                name: x.clone(),
                child: Box::new(computation_to_ast(n)),
                r#type: a.to_string(),
            }],
            r#type: m.ty.to_string(),
        },
        infer_debug::ComputationTerm::PatternMatch(v, (x, a), (y, b), n) => AST::Term {
            name: "PatternMatch".to_string(),
            children: vec![
                value_to_ast(v),
                AST::Binder {
                    name: x.clone(),
                    child: Box::new(AST::Binder {
                        name: y.clone(),
                        child: Box::new(computation_to_ast(n)),
                        r#type: b.to_string(),
                    }),
                    r#type: a.to_string(),
                },
            ],
            r#type: m.ty.to_string(),
        },
        infer_debug::ComputationTerm::Case(v, (x, a), n1, (y, b), n2) => AST::Term {
            name: "Case".to_string(),
            children: vec![
                value_to_ast(v),
                AST::Binder {
                    name: x.clone(),
                    child: Box::new(computation_to_ast(n1)),
                    r#type: a.to_string(),
                },
                AST::Binder {
                    name: y.clone(),
                    child: Box::new(computation_to_ast(n2)),
                    r#type: b.to_string(),
                },
            ],
            r#type: m.ty.to_string(),
        },
        infer_debug::ComputationTerm::Explode(v, _) => AST::Term {
            name: "Explode".to_string(),
            children: vec![value_to_ast(v)],
            r#type: m.ty.to_string(),
        },
        infer_debug::ComputationTerm::Fix(x, n, c) => AST::Term {
            name: "Fix".to_string(),
            children: vec![AST::Binder {
                name: x.clone(),
                child: Box::new(computation_to_ast(n)),
                r#type: lib::refinement::r#type::Value::U(Box::new(c.clone())).to_string(),
            }],
            r#type: m.ty.to_string(),
        },
        infer_debug::ComputationTerm::Force(v) => AST::Term {
            name: "Force".to_string(),
            children: vec![value_to_ast(v)],
            r#type: m.ty.to_string(),
        },
        infer_debug::ComputationTerm::Fail => AST::Term {
            name: "Fail".to_string(),
            children: Vec::new(),
            r#type: m.ty.to_string(),
        },
        infer_debug::ComputationTerm::Add => AST::Term {
            name: "Add".to_string(),
            children: Vec::new(),
            r#type: m.ty.to_string(),
        },
        infer_debug::ComputationTerm::Leq => AST::Term {
            name: "Leq".to_string(),
            children: Vec::new(),
            r#type: m.ty.to_string(),
        },
        infer_debug::ComputationTerm::NDInt => AST::Term {
            name: "NDInt".to_string(),
            children: Vec::new(),
            r#type: m.ty.to_string(),
        },
    }
}

#[derive(Serialize, Deserialize)]
struct Data {
    ast: Option<AST>,
    smtlib: Option<String>,
}

enum Strategy {
    CBV,
    CBN,
}

fn to_smtlib(s: &str, log: &mut String, ev: Strategy) -> Result<(AST, String), String> {
    lib::logic::Formula::reset_pname_counter();
    let write_error_handler = |e| Err(format!("log error: {}", e));
    let (_, t) = nom::combinator::all_consuming(lambda::parser::term)(s)
        .or_else(|e| Err(format!("{}", e)))?;
    writeln!(log, "parse result").or_else(write_error_handler)?;
    writeln!(log, "{:#?}", t).or_else(write_error_handler)?;
    let (_, term) = match ev {
        Strategy::CBV => {
            writeln!(log, "cbv translation").or_else(write_error_handler)?;
            underlying::translate::cbv_of_lambda(&Context::new(), &t)
        }
        Strategy::CBN => {
            writeln!(log, "cbn translation").or_else(write_error_handler)?;
            underlying::translate::cbn_of_lambda(&Context::new(), &t)
        }
    };
    writeln!(log, "{:#?}", term).or_else(write_error_handler)?;
    let term = term.simplify(&HashSet::new());
    writeln!(log, "simplified term").or_else(write_error_handler)?;
    writeln!(log, "{:#?}", term).or_else(write_error_handler)?;
    let (m, ty) = term.infer(&mut Context::new())?;
    let term = term.subst_type(&m);
    writeln!(log, "HM type inference").or_else(write_error_handler)?;
    writeln!(log, "{:?} : {}", term, ty.subst(&m)).or_else(write_error_handler)?;
    if term.free_type_vars().is_empty() {
        let mut used_pvar = Context::new();
        let (c, t) = infer_debug::computation(&mut Context::new(), &term, &mut used_pvar);
        writeln!(log, "raw constraints").or_else(write_error_handler)?;
        for c in c.iter() {
            writeln!(log, "{:?}", c).or_else(write_error_handler)?;
        }
        let (used_pvar, c) = lib::logic::simplify(used_pvar, c);
        writeln!(log, "simplified constraints").or_else(write_error_handler)?;
        writeln!(log, "{:?}", used_pvar).or_else(write_error_handler)?;
        for c in c.iter() {
            writeln!(log, "{:?}", c).or_else(write_error_handler)?;
        }
        let smtlib = lib::logic::to_smtlib(&used_pvar, &c).ok_or("cannot encode to SMT LIB")?;
        Ok((computation_to_ast(&t), smtlib.to_string()))
    } else {
        Err("HM type inference: not fully resolved".to_string())
    }
}

#[wasm_bindgen]
pub fn to_smtlib_cbv(s: &str) -> JsValue {
    let mut l = String::new();
    let result = to_smtlib(s, &mut l, Strategy::CBV);
    log(&l);
    let data = match result {
        Ok((ast, smtlib)) => Data {
            ast: Some(ast),
            smtlib: Some(smtlib),
        },
        Err(e) => {
            alert(&e);
            Data {
                ast: None,
                smtlib: None,
            }
        }
    };
    JsValue::from_serde(&data).unwrap()
}

#[wasm_bindgen]
pub fn to_smtlib_cbn(s: &str) -> JsValue {
    let mut l = String::new();
    let result = to_smtlib(s, &mut l, Strategy::CBN);
    log(&l);
    let data = match result {
        Ok((ast, smtlib)) => Data {
            ast: Some(ast),
            smtlib: Some(smtlib),
        },
        Err(e) => {
            alert(&e);
            Data {
                ast: None,
                smtlib: None,
            }
        }
    };
    JsValue::from_serde(&data).unwrap()
}
