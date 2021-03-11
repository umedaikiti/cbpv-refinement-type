use super::super::context::Context;
use super::super::lambda;
use super::super::utils;
use super::r#type;
use super::term::{Computation, Value};
use lambda::r#type::Type;
use lambda::term::Term;
use std::collections::{HashMap, HashSet};

struct RenameContext {
    vars: HashSet<String>,
    map: HashMap<String, String>,
}

impl RenameContext {
    fn new() -> Self {
        RenameContext {
            vars: HashSet::new(),
            map: HashMap::new(),
        }
    }
    fn init(ctx: &Context<Type>) -> Self {
        let mut rctx = RenameContext::new();
        for (x, _) in ctx.0.iter() {
            let x_new = utils::mk_fresh_name(x, &rctx.vars);
            rctx.vars.insert(x_new.clone());
            rctx.map.insert(x.clone(), x_new);
        }
        rctx
    }
    #[must_use]
    fn add(&mut self, x: &str) -> String {
        let x_new = utils::mk_fresh_name(x, &self.vars);
        self.vars.insert(x_new.clone());
        x_new
    }
    fn remove(&mut self, x: &String) {
        self.vars.remove(x);
    }
    #[must_use]
    fn register_rename(&mut self, from: &String, to: &String) -> Option<String> {
        self.map.insert(from.clone(), to.clone())
    }
    fn restore_rename(&mut self, from: &String, to: Option<String>) {
        match to {
            Some(to) => {
                self.map.insert(from.clone(), to);
            }
            None => {
                self.map.remove(from);
            }
        }
    }
    fn rename(&self, x: &String) -> String {
        match self.map.get(x) {
            Some(y) => y.clone(),
            None => x.clone(),
        }
    }
}

pub fn cbv_of_lambda(ctx: &Context<Type>, term: &Term) -> (Context<r#type::Value>, Computation) {
    let mut rctx = RenameContext::init(ctx);
    let ctx: Vec<(String, r#type::Value)> = ctx
        .0
        .iter()
        .map(|(x, a)| (x.to_string(), a.cbv_of_lambda()))
        .collect();
    (ctx.into(), cbv_of_lambda_sub(term, &mut rctx))
}

pub fn cbn_of_lambda(ctx: &Context<Type>, term: &Term) -> (Context<r#type::Value>, Computation) {
    let mut rctx = RenameContext::init(ctx);
    let ctx: Vec<(String, r#type::Value)> = ctx
        .0
        .iter()
        .map(|(x, a)| (x.to_string(), r#type::Value::U(Box::new(a.cbn_of_lambda()))))
        .collect();
    (ctx.into(), cbn_of_lambda_sub(term, &mut rctx))
}

impl Type {
    fn cbv_of_lambda(&self) -> r#type::Value {
        match self {
            Type::Unit => r#type::Value::Unit,
            _ => unimplemented!(),
        }
    }
    fn cbn_of_lambda(&self) -> r#type::Computation {
        match self {
            Type::Unit => r#type::Computation::F(Box::new(r#type::Value::Unit)),
            _ => unimplemented!(),
        }
    }
}

fn cbv_of_lambda_sub(term: &Term, rctx: &mut RenameContext) -> Computation {
    match term {
        Term::Var(x) => Computation::Return(Box::new(Value::Var(rctx.rename(x)))),
        Term::Int(i) => Computation::Return(Box::new(Value::Int(*i))),
        Term::Lambda(x, m) => {
            let x_new = rctx.add(x);
            let save_x = rctx.register_rename(x, &x_new);
            let cbv_m = cbv_of_lambda_sub(m, rctx);
            rctx.restore_rename(x, save_x);
            rctx.remove(&x_new);
            Computation::Return(Box::new(Value::Thunk(Box::new(Computation::Lambda(
                (x_new, r#type::Value::Var(r#type::Value::mk_fresh_name())),
                Box::new(cbv_m),
            )))))
        }
        Term::App(m, n) => {
            let cbv_m = cbv_of_lambda_sub(m, rctx);
            let f = rctx.add("f");
            let cbv_n = cbv_of_lambda_sub(n, rctx);
            let x = rctx.add("x");
            rctx.remove(&x);
            rctx.remove(&f);
            Computation::SeqComp(
                Box::new(cbv_m),
                (
                    f.clone(),
                    r#type::Value::Var(r#type::Value::mk_fresh_name()),
                ),
                Box::new(Computation::SeqComp(
                    Box::new(cbv_n),
                    (
                        x.clone(),
                        r#type::Value::Var(r#type::Value::mk_fresh_name()),
                    ),
                    Box::new(Computation::App(
                        Box::new(Computation::Force(Box::new(Value::Var(f)))),
                        Box::new(Value::Var(x)),
                    )),
                )),
            )
        }
        Term::Unit => Computation::Return(Box::new(Value::Unit)),
        Term::Pair(v, w) => {
            let cbv_v = cbv_of_lambda_sub(v, rctx);
            let x = rctx.add("x");
            let cbv_w = cbv_of_lambda_sub(w, rctx);
            let y = rctx.add("y");
            rctx.remove(&y);
            rctx.remove(&x);
            Computation::SeqComp(
                Box::new(cbv_v),
                (
                    x.clone(),
                    r#type::Value::Var(r#type::Value::mk_fresh_name()),
                ),
                Box::new(Computation::SeqComp(
                    Box::new(cbv_w),
                    (
                        y.clone(),
                        r#type::Value::Var(r#type::Value::mk_fresh_name()),
                    ),
                    Box::new(Computation::Return(Box::new(Value::Pair(
                        Box::new(Value::Var(x)),
                        Box::new(Value::Var(y)),
                    )))),
                )),
            )
        }
        Term::Inr(v) => {
            let cbv_v = cbv_of_lambda_sub(v, rctx);
            let x = rctx.add("x");
            rctx.remove(&x);
            Computation::SeqComp(
                Box::new(cbv_v),
                (
                    x.clone(),
                    r#type::Value::Var(r#type::Value::mk_fresh_name()),
                ),
                Box::new(Computation::Return(Box::new(Value::Inr(
                    Box::new(Value::Var(x)),
                    r#type::Value::Var(r#type::Value::mk_fresh_name()),
                )))),
            )
        }
        Term::Inl(v) => {
            let cbv_v = cbv_of_lambda_sub(v, rctx);
            let x = rctx.add("x");
            rctx.remove(&x);
            Computation::SeqComp(
                Box::new(cbv_v),
                (
                    x.clone(),
                    r#type::Value::Var(r#type::Value::mk_fresh_name()),
                ),
                Box::new(Computation::Return(Box::new(Value::Inl(
                    Box::new(Value::Var(x)),
                    r#type::Value::Var(r#type::Value::mk_fresh_name()),
                )))),
            )
        }
        Term::Case(v, x, m, y, n) => {
            let cbv_v = cbv_of_lambda_sub(v, rctx);
            let z = rctx.add("z");
            let x_new = rctx.add(x);
            let save_x = rctx.register_rename(x, &x_new);
            let cbv_m = cbv_of_lambda_sub(m, rctx);
            rctx.restore_rename(x, save_x);
            rctx.remove(&x_new);
            let y_new = rctx.add(y);
            let save_y = rctx.register_rename(y, &y_new);
            let cbv_n = cbv_of_lambda_sub(n, rctx);
            rctx.restore_rename(y, save_y);
            rctx.remove(&y_new);
            rctx.remove(&z);
            Computation::SeqComp(
                Box::new(cbv_v),
                (
                    z.clone(),
                    r#type::Value::Var(r#type::Value::mk_fresh_name()),
                ),
                Box::new(Computation::Case(
                    Box::new(Value::Var(z)),
                    (x_new, r#type::Value::Var(r#type::Value::mk_fresh_name())),
                    Box::new(cbv_m),
                    (y_new, r#type::Value::Var(r#type::Value::mk_fresh_name())),
                    Box::new(cbv_n),
                )),
            )
        }
        Term::PatternMatch(v, x, y, m) => {
            let cbv_v = cbv_of_lambda_sub(v, rctx);
            let z = rctx.add("z");
            let x_new = rctx.add(x);
            let save_x = rctx.register_rename(x, &x_new);
            let y_new = rctx.add(y);
            let save_y = rctx.register_rename(y, &y_new);
            let cbv_m = cbv_of_lambda_sub(m, rctx);
            rctx.restore_rename(y, save_y);
            rctx.remove(&y_new);
            rctx.restore_rename(x, save_x);
            rctx.remove(&x_new);
            rctx.remove(&z);
            Computation::SeqComp(
                Box::new(cbv_v),
                (
                    z.clone(),
                    r#type::Value::Var(r#type::Value::mk_fresh_name()),
                ),
                Box::new(Computation::PatternMatch(
                    Box::new(Value::Var(z)),
                    (x_new, r#type::Value::Var(r#type::Value::mk_fresh_name())),
                    (y_new, r#type::Value::Var(r#type::Value::mk_fresh_name())),
                    Box::new(cbv_m),
                )),
            )
        }
        Term::Explode(v) => {
            let cbv_v = cbv_of_lambda_sub(v, rctx);
            let z = rctx.add("z");
            rctx.remove(&z);
            Computation::SeqComp(
                Box::new(cbv_v),
                (z.clone(), r#type::Value::Empty),
                Box::new(Computation::Explode(
                    Box::new(Value::Var(z)),
                    r#type::Computation::Var(r#type::Computation::mk_fresh_name()),
                )),
            )
        }
        Term::Fix(x, m) => {
            let x_new = rctx.add(x);
            let save_x = rctx.register_rename(x, &x_new);
            let cbv_m = cbv_of_lambda_sub(m, rctx);
            rctx.restore_rename(x, save_x);
            rctx.remove(&x_new);
            let fix_tmp = rctx.add("fix_tmp");
            rctx.remove(&fix_tmp);
            Computation::Return(Box::new(Value::Thunk(Box::new(Computation::Fix(
                x_new,
                Box::new(Computation::SeqComp(
                    Box::new(cbv_m),
                    (
                        fix_tmp.clone(),
                        r#type::Value::Var(r#type::Value::mk_fresh_name()),
                    ),
                    Box::new(Computation::Force(Box::new(Value::Var(fix_tmp)))),
                )),
                r#type::Computation::Var(r#type::Computation::mk_fresh_name()),
            )))))
        }
        Term::Fail => Computation::Return(Box::new(Value::Thunk(Box::new(Computation::Fail)))),
        Term::Add => {
            let x = rctx.add("x");
            let y = rctx.add("y");
            rctx.remove(&y);
            rctx.remove(&x);
            let term = Computation::Add;
            let term = Computation::App(Box::new(term), Box::new(Value::Var(x.clone())));
            let term = Computation::App(Box::new(term), Box::new(Value::Var(y.clone())));
            let term = Computation::Return(Box::new(Value::Thunk(Box::new(Computation::Lambda(
                (y, r#type::Value::Int),
                Box::new(term),
            )))));
            let term = Computation::Return(Box::new(Value::Thunk(Box::new(Computation::Lambda(
                (x, r#type::Value::Int),
                Box::new(term),
            )))));
            term
        }
        Term::Leq => {
            let x = rctx.add("x");
            let y = rctx.add("y");
            rctx.remove(&y);
            rctx.remove(&x);
            let term = Computation::Leq;
            let term = Computation::App(Box::new(term), Box::new(Value::Var(x.clone())));
            let term = Computation::App(Box::new(term), Box::new(Value::Var(y.clone())));
            let term = Computation::Return(Box::new(Value::Thunk(Box::new(Computation::Lambda(
                (y, r#type::Value::Int),
                Box::new(term),
            )))));
            let term = Computation::Return(Box::new(Value::Thunk(Box::new(Computation::Lambda(
                (x, r#type::Value::Int),
                Box::new(term),
            )))));
            term
        }
    }
}

fn cbn_of_lambda_sub(term: &Term, rctx: &mut RenameContext) -> Computation {
    match term {
        Term::Var(x) => Computation::Force(Box::new(Value::Var(rctx.rename(x)))),
        Term::Int(i) => Computation::Return(Box::new(Value::Int(*i))),
        Term::Lambda(x, m) => {
            let x_new = rctx.add(x);
            let save_x = rctx.register_rename(x, &x_new);
            let cbn_m = cbn_of_lambda_sub(m, rctx);
            rctx.restore_rename(x, save_x);
            rctx.remove(&x_new);
            Computation::Lambda(
                (x_new, r#type::Value::Var(r#type::Value::mk_fresh_name())),
                Box::new(cbn_m),
            )
        }
        Term::App(m, n) => {
            let cbn_m = cbn_of_lambda_sub(m, rctx);
            let cbn_n = cbn_of_lambda_sub(n, rctx);
            Computation::App(Box::new(cbn_m), Box::new(Value::Thunk(Box::new(cbn_n))))
        }
        Term::Unit => Computation::Return(Box::new(Value::Unit)),
        Term::Inl(v) => {
            let cbn_v = cbn_of_lambda_sub(v, rctx);
            Computation::Return(Box::new(Value::Inl(
                Box::new(Value::Thunk(Box::new(cbn_v))),
                r#type::Value::Var(r#type::Value::mk_fresh_name()),
            )))
        }
        Term::Inr(v) => {
            let cbn_v = cbn_of_lambda_sub(v, rctx);
            Computation::Return(Box::new(Value::Inr(
                Box::new(Value::Thunk(Box::new(cbn_v))),
                r#type::Value::Var(r#type::Value::mk_fresh_name()),
            )))
        }
        Term::Case(v, x, m, y, n) => {
            let cbn_v = cbn_of_lambda_sub(v, rctx);
            let z = rctx.add("z");
            let x_new = rctx.add(x);
            let save_x = rctx.register_rename(x, &x_new);
            let cbn_m = cbn_of_lambda_sub(m, rctx);
            rctx.restore_rename(x, save_x);
            rctx.remove(&x_new);
            let y_new = rctx.add(y);
            let save_y = rctx.register_rename(y, &y_new);
            let cbn_n = cbn_of_lambda_sub(n, rctx);
            rctx.restore_rename(y, save_y);
            rctx.remove(&y_new);
            rctx.remove(&z);
            Computation::SeqComp(
                Box::new(cbn_v),
                (
                    z.clone(),
                    r#type::Value::Var(r#type::Value::mk_fresh_name()),
                ),
                Box::new(Computation::Case(
                    Box::new(Value::Var(z.clone())),
                    (x_new, r#type::Value::Var(r#type::Value::mk_fresh_name())),
                    Box::new(cbn_m),
                    (y_new, r#type::Value::Var(r#type::Value::mk_fresh_name())),
                    Box::new(cbn_n),
                )),
            )
        }
        Term::PatternMatch(v, x, y, m) => {
            let cbn_v = cbn_of_lambda_sub(v, rctx);
            let z = rctx.add("z");
            let x_new = rctx.add(x);
            let save_x = rctx.register_rename(x, &x_new);
            let y_new = rctx.add(y);
            let save_y = rctx.register_rename(y, &y_new);
            let cbn_m = cbn_of_lambda_sub(m, rctx);
            rctx.restore_rename(y, save_y);
            rctx.remove(&y_new);
            rctx.restore_rename(x, save_x);
            rctx.remove(&x_new);
            rctx.remove(&z);
            Computation::SeqComp(
                Box::new(cbn_v),
                (
                    z.clone(),
                    r#type::Value::Var(r#type::Value::mk_fresh_name()),
                ),
                Box::new(Computation::PatternMatch(
                    Box::new(Value::Var(z.clone())),
                    (x_new, r#type::Value::Var(r#type::Value::mk_fresh_name())),
                    (y_new, r#type::Value::Var(r#type::Value::mk_fresh_name())),
                    Box::new(cbn_m),
                )),
            )
        }
        Term::Explode(v) => {
            let cbn_v = cbn_of_lambda_sub(v, rctx);
            let z = rctx.add("z");
            rctx.remove(&z);
            Computation::SeqComp(
                Box::new(cbn_v),
                (z.clone(), r#type::Value::Empty),
                Box::new(Computation::Explode(
                    Box::new(Value::Var(z)),
                    r#type::Computation::Var(r#type::Computation::mk_fresh_name()),
                )),
            )
        }
        Term::Pair(v, w) => {
            let cbn_v = cbn_of_lambda_sub(v, rctx);
            let cbn_w = cbn_of_lambda_sub(w, rctx);
            Computation::Return(Box::new(Value::Pair(
                Box::new(Value::Thunk(Box::new(cbn_v))),
                Box::new(Value::Thunk(Box::new(cbn_w))),
            )))
        }
        Term::Fix(x, m) => {
            let x_new = rctx.add(x);
            let save_x = rctx.register_rename(x, &x_new);
            let cbn_m = cbn_of_lambda_sub(m, rctx);
            rctx.restore_rename(x, save_x);
            rctx.remove(&x_new);
            Computation::Fix(
                x_new,
                Box::new(cbn_m),
                r#type::Computation::Var(r#type::Computation::mk_fresh_name()),
            )
        }
        Term::Fail => {
            let x = rctx.add("x");
            let y = rctx.add("y");
            rctx.remove(&y);
            rctx.remove(&x);
            Computation::Lambda(
                (
                    x.clone(),
                    r#type::Value::U(Box::new(r#type::Computation::F(Box::new(
                        r#type::Value::Unit,
                    )))),
                ),
                Box::new(Computation::SeqComp(
                    Box::new(Computation::Force(Box::new(Value::Var(x)))),
                    (y.clone(), r#type::Value::Unit),
                    Box::new(Computation::App(
                        Box::new(Computation::Fail),
                        Box::new(Value::Var(y)),
                    )),
                )),
            )
        }
        Term::Add => {
            let xc = rctx.add("xc");
            let yc = rctx.add("yc");
            let xv = rctx.add("xv");
            let yv = rctx.add("yv");
            rctx.remove(&yv);
            rctx.remove(&xv);
            rctx.remove(&yc);
            rctx.remove(&xc);
            let term = Computation::Add;
            let term = Computation::App(Box::new(term), Box::new(Value::Var(xv.clone())));
            let term = Computation::App(Box::new(term), Box::new(Value::Var(yv.clone())));
            let term = Computation::SeqComp(
                Box::new(Computation::Force(Box::new(Value::Var(yc.clone())))),
                (yv, r#type::Value::Int),
                Box::new(term),
            );
            let term = Computation::Lambda(
                (
                    yc,
                    r#type::Value::U(Box::new(r#type::Computation::F(Box::new(
                        r#type::Value::Int,
                    )))),
                ),
                Box::new(term),
            );
            let term = Computation::SeqComp(
                Box::new(Computation::Force(Box::new(Value::Var(xc.clone())))),
                (xv, r#type::Value::Int),
                Box::new(term),
            );
            let term = Computation::Lambda(
                (
                    xc,
                    r#type::Value::U(Box::new(r#type::Computation::F(Box::new(
                        r#type::Value::Int,
                    )))),
                ),
                Box::new(term),
            );
            term
        }
        Term::Leq => {
            let xc = rctx.add("xc");
            let yc = rctx.add("yc");
            let xv = rctx.add("xv");
            let yv = rctx.add("yv");
            let z = rctx.add("z");
            let dummy = rctx.add("dummy");
            rctx.remove(&dummy);
            rctx.remove(&z);
            rctx.remove(&yv);
            rctx.remove(&xv);
            rctx.remove(&yc);
            rctx.remove(&xc);
            let term = Computation::Case(
                Box::new(Value::Var(z.clone())),
                (dummy.clone(), r#type::Value::Unit),
                Box::new(Computation::Return(Box::new(Value::Inl(
                    Box::new(Value::Thunk(Box::new(Computation::Return(Box::new(
                        Value::Unit,
                    ))))),
                    r#type::Value::U(Box::new(r#type::Computation::F(Box::new(
                        r#type::Value::Unit,
                    )))),
                )))),
                (dummy, r#type::Value::Unit),
                Box::new(Computation::Return(Box::new(Value::Inr(
                    Box::new(Value::Thunk(Box::new(Computation::Return(Box::new(
                        Value::Unit,
                    ))))),
                    r#type::Value::U(Box::new(r#type::Computation::F(Box::new(
                        r#type::Value::Unit,
                    )))),
                )))),
            );
            let term = Computation::SeqComp(
                Box::new(Computation::App(
                    Box::new(Computation::App(
                        Box::new(Computation::Leq),
                        Box::new(Value::Var(xv.clone())),
                    )),
                    Box::new(Value::Var(yv.clone())),
                )),
                (
                    z,
                    r#type::Value::Sum(
                        Box::new(r#type::Value::Unit),
                        Box::new(r#type::Value::Unit),
                    ),
                ),
                Box::new(term),
            );
            let term = Computation::SeqComp(
                Box::new(Computation::Force(Box::new(Value::Var(yc.clone())))),
                (yv, r#type::Value::Int),
                Box::new(term),
            );
            let term = Computation::Lambda(
                (
                    yc,
                    r#type::Value::U(Box::new(r#type::Computation::F(Box::new(
                        r#type::Value::Int,
                    )))),
                ),
                Box::new(term),
            );
            let term = Computation::SeqComp(
                Box::new(Computation::Force(Box::new(Value::Var(xc.clone())))),
                (xv, r#type::Value::Int),
                Box::new(term),
            );
            let term = Computation::Lambda(
                (
                    xc,
                    r#type::Value::U(Box::new(r#type::Computation::F(Box::new(
                        r#type::Value::Int,
                    )))),
                ),
                Box::new(term),
            );
            term
        }
    }
}
