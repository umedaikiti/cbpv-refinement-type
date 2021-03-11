extern crate lib;
extern crate nom;
extern crate wasm_bindgen;
use lib::context::Context;
use lib::lambda;
use lib::refinement::infer;
use lib::underlying;
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

enum Strategy {
    CBV,
    CBN,
}

fn to_smtlib(s: &str, log: &mut String, ev: Strategy) -> Result<String, String> {
    lib::logic::Formula::reset_pname_counter();
    let write_error_handler = |e| Err(format!("log error: {}", e));
    let (_, t) = nom::combinator::all_consuming(lambda::parser::term)(s)
        .or_else(|e| Err(format!("parse error: {}", e)))?;
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
    if m.fv_cod().is_empty() {
        let mut used_pvar = Context::new();
        let (c, t) = infer::computation(&mut Context::new(), &term, &mut used_pvar);
        writeln!(log, "refinement type").or_else(write_error_handler)?;
        writeln!(log, "{}", t).or_else(write_error_handler)?;
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
        Ok(smtlib.to_string())
    } else {
        Err("HM type inference: not fully resolved".to_string())
    }
}

#[wasm_bindgen]
pub fn to_smtlib_cbv(s: &str) -> Option<String> {
    let mut l = String::new();
    let result = to_smtlib(s, &mut l, Strategy::CBV);
    log(&l);
    match result {
        Ok(smtlib) => Some(smtlib),
        Err(e) => {
            log(&e);
            None
        }
    }
}

#[wasm_bindgen]
pub fn to_smtlib_cbn(s: &str) -> Option<String> {
    let mut l = String::new();
    let result = to_smtlib(s, &mut l, Strategy::CBN);
    log(&l);
    match result {
        Ok(smtlib) => Some(smtlib),
        Err(e) => {
            log(&e);
            None
        }
    }
}
