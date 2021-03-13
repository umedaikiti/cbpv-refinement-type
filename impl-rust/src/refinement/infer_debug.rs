use super::super::context::Context;
use super::super::logic::{Formula, Term};
use super::super::underlying::r#type as utype;
use super::super::underlying::term;
use super::super::utils;
use super::r#type as rtype;

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Value {
    pub term: ValueTerm,
    pub ty: rtype::Value,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum ValueTerm {
    Var(String),
    Unit,
    Int(i64),
    Pair(Box<Value>, Box<Value>),
    Inr(Box<Value>, rtype::Value),
    Inl(Box<Value>, rtype::Value),
    Thunk(Box<Computation>),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Computation {
    pub term: ComputationTerm,
    pub ty: rtype::Computation,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum ComputationTerm {
    Return(Box<Value>),
    SeqComp(Box<Computation>, (String, rtype::Value), Box<Computation>),
    Lambda((String, rtype::Value), Box<Computation>),
    App(Box<Computation>, Box<Value>),
    PatternMatch(
        Box<Value>,
        (String, rtype::Value),
        (String, rtype::Value),
        Box<Computation>,
    ),
    Case(
        Box<Value>,
        (String, rtype::Value),
        Box<Computation>,
        (String, rtype::Value),
        Box<Computation>,
    ),
    Force(Box<Value>),
    Fix(String, Box<Computation>, rtype::Computation),
    Explode(Box<Value>, rtype::Computation),
    Fail,
    Add,
    Leq,
    NDInt,
}

pub fn value(
    ctx: &mut Context<rtype::Value>,
    v: &term::Value,
    used_pvar: &mut Context<Vec<utype::Value>>,
) -> (Vec<(Context<utype::Value>, Formula)>, Value) {
    match v {
        term::Value::Var(x) => match ctx.get(x) {
            Some(rtype::Value::Unit(v, _)) => {
                let v = utils::mk_fresh_name(v, &ctx.vars());
                (
                    Vec::new(),
                    Value {
                        term: ValueTerm::Var(x.clone()),
                        ty: rtype::Value::Unit(v, Formula::True),
                    },
                )
            }
            Some(rtype::Value::Int(v, _)) => {
                let v = utils::mk_fresh_name(v, &ctx.vars());
                (
                    Vec::new(),
                    Value {
                        term: ValueTerm::Var(x.clone()),
                        ty: rtype::Value::Int(
                            v.clone(),
                            Formula::Equal(Term::Var(v), Term::Var(x.clone())),
                        ),
                    },
                )
            }
            Some(a) => (
                Vec::new(),
                Value {
                    term: ValueTerm::Var(x.clone()),
                    ty: a.clone(),
                },
            ),
            None => panic!(format!("variable {} not found in the context", x)),
        },
        term::Value::Unit => {
            let v = utils::mk_fresh_name("unit_val", &ctx.vars());
            (
                Vec::new(),
                Value {
                    term: ValueTerm::Unit,
                    ty: rtype::Value::Unit(v, Formula::True),
                },
            )
        }
        term::Value::Int(i) => {
            let v = utils::mk_fresh_name(&format!("int_const_{}", i), &ctx.vars());
            (
                Vec::new(),
                Value {
                    term: ValueTerm::Int(*i),
                    ty: rtype::Value::Int(v.clone(), Formula::Equal(Term::Var(v), Term::Int(*i))),
                },
            )
        }
        term::Value::Pair(v, w) => {
            let (mut cv, tv) = value(ctx, v, used_pvar);
            let (cw, tw) = value(ctx, w, used_pvar);
            cv.extend(cw);
            let x = utils::mk_fresh_name("pair_fst", &ctx.vars());
            match Term::from_underlying_value(v) {
                Ok(v) => {
                    ctx.push(x.clone(), tv.ty.clone());
                    let rtw = rtype::Value::refinement_template(
                        ctx,
                        &tw.ty.erase(),
                        used_pvar,
                        "pair_snd",
                    );
                    ctx.pop();
                    let csub = rtype::Value::subtype(
                        ctx,
                        &tw.ty,
                        &rtw.subst_term(&vec![(x.clone(), v)].into_iter().collect()),
                    );
                    cv.extend(csub);
                    let ty = rtype::Value::Pair(x, Box::new(tv.ty.clone()), Box::new(rtw));
                    (
                        cv,
                        Value {
                            term: ValueTerm::Pair(Box::new(tv), Box::new(tw)),
                            ty: ty,
                        },
                    )
                }
                Err(_) => {
                    let ty =
                        rtype::Value::Pair(x, Box::new(tv.ty.clone()), Box::new(tw.ty.clone()));
                    (
                        cv,
                        Value {
                            term: ValueTerm::Pair(Box::new(tv), Box::new(tw)),
                            ty: ty,
                        },
                    )
                }
            }
        }
        term::Value::Inl(v, b) => {
            let (cv, tv) = value(ctx, v, used_pvar);
            let tb = rtype::Value::refinement_template(ctx, b, used_pvar, "sum_r");
            let ty = rtype::Value::Sum(Box::new(tv.ty.clone()), Box::new(tb.clone()));
            (
                cv,
                Value {
                    term: ValueTerm::Inl(Box::new(tv), tb),
                    ty: ty,
                },
            )
        }
        term::Value::Inr(v, a) => {
            let (cv, tv) = value(ctx, v, used_pvar);
            let ta = rtype::Value::refinement_template(ctx, a, used_pvar, "sum_l");
            let ty = rtype::Value::Sum(Box::new(ta.clone()), Box::new(tv.ty.clone()));
            (
                cv,
                Value {
                    term: ValueTerm::Inr(Box::new(tv), ta),
                    ty: ty,
                },
            )
        }
        term::Value::Thunk(m) => {
            let (cm, tm) = computation(ctx, m, used_pvar);
            let ty = rtype::Value::U(Box::new(tm.ty.clone()));
            (
                cm,
                Value {
                    term: ValueTerm::Thunk(Box::new(tm)),
                    ty: ty,
                },
            )
        }
    }
}
pub fn computation(
    ctx: &mut Context<rtype::Value>,
    m: &term::Computation,
    used_pvar: &mut Context<Vec<utype::Value>>,
) -> (Vec<(Context<utype::Value>, Formula)>, Computation) {
    match m {
        term::Computation::Return(v) => {
            let (cv, tv) = value(ctx, v, used_pvar);
            let ty = rtype::Computation::F(Box::new(tv.ty.clone()));
            (
                cv,
                Computation {
                    term: ComputationTerm::Return(Box::new(tv)),
                    ty: ty,
                },
            )
        }
        term::Computation::SeqComp(m, (x, _), n) => {
            let (mut cm, tm) = computation(ctx, m, used_pvar);
            match tm.ty.clone() {
                rtype::Computation::F(a) => {
                    let a = *a;
                    ctx.push(x, a);
                    let (cn, tn) = computation(ctx, n, used_pvar);
                    let (x, a) = ctx.pop().unwrap();
                    let ty = rtype::Computation::refinement_template(
                        ctx,
                        &tn.ty.erase(),
                        used_pvar,
                        "seq_comp_result",
                    );
                    ctx.push(x, a);
                    let csub = rtype::Computation::subtype(ctx, &tn.ty, &ty);
                    let (x, a) = ctx.pop().unwrap();
                    cm.extend(cn);
                    cm.extend(csub);
                    (
                        cm,
                        Computation {
                            term: ComputationTerm::SeqComp(Box::new(tm), (x, a), Box::new(tn)),
                            ty: ty,
                        },
                    )
                }
                _ => panic!("type error in sequential composition"),
            }
        }
        term::Computation::App(m, v) => {
            let (mut cm, tm) = computation(ctx, m, used_pvar);
            match tm.ty.clone() {
                rtype::Computation::Function(x, a, c) => {
                    let (cv, tv) = value(ctx, v, used_pvar);
                    let csub = rtype::Value::subtype(ctx, &tv.ty, &a);
                    cm.extend(cv);
                    cm.extend(csub);
                    (
                        cm,
                        Computation {
                            term: ComputationTerm::App(Box::new(tm), Box::new(tv)),
                            ty: match Term::from_underlying_value(v) {
                                Ok(v) => c.subst_term(&vec![(x, v)].into_iter().collect()),
                                Err(_) => *c,
                            },
                        },
                    )
                }
                _ => panic!("type error in function application"),
            }
        }
        term::Computation::Lambda((x, a), m) => {
            let ra = rtype::Value::refinement_template(ctx, a, used_pvar, "lambda_arg_var");
            ctx.push(x, ra);
            let (cm, tm) = computation(ctx, m, used_pvar);
            let (x, ra) = ctx.pop().unwrap();
            let ty = rtype::Computation::Function(
                x.clone(),
                Box::new(ra.clone()),
                Box::new(tm.ty.clone()),
            );
            (
                cm,
                Computation {
                    term: ComputationTerm::Lambda((x, ra), Box::new(tm)),
                    ty: ty,
                },
            )
        }
        term::Computation::Force(v) => {
            let (cv, tv) = value(ctx, v, used_pvar);
            match tv.ty.clone() {
                rtype::Value::U(c) => (
                    cv,
                    Computation {
                        term: ComputationTerm::Force(Box::new(tv)),
                        ty: *c,
                    },
                ),
                _ => panic!("type error in force"),
            }
        }
        term::Computation::PatternMatch(v, (x, _), (y, _), m) => {
            let (mut cv, tv) = value(ctx, v, used_pvar);
            match &tv.ty {
                rtype::Value::Pair(x0, a, b) => {
                    let a = (**a).clone();
                    let b = b.subst_term(
                        &vec![(x0.clone(), Term::Var(x.clone()))]
                            .into_iter()
                            .collect(),
                    );
                    ctx.push(x, a);
                    ctx.push(y, b);
                    let (cm, tm) = computation(ctx, m, used_pvar);
                    let (y, b) = ctx.pop().unwrap();
                    let (x, a) = ctx.pop().unwrap();
                    cv.extend(cm);
                    let tmpvar = utils::mk_fresh_name("tmp", &ctx.vars());
                    ctx.push(tmpvar.clone(), tv.ty.clone());
                    let rtm = rtype::Computation::refinement_template(
                        ctx,
                        &tm.ty.erase(),
                        used_pvar,
                        "pm_result",
                    );
                    ctx.pop();
                    ctx.push(x.clone(), a);
                    ctx.push(y.clone(), b);
                    let csub = rtype::Computation::subtype(
                        ctx,
                        &tm.ty,
                        &rtm.subst_term(
                            &vec![(
                                tmpvar.clone(),
                                Term::Pair(Box::new(Term::Var(x)), Box::new(Term::Var(y))),
                            )]
                            .into_iter()
                            .collect(),
                        ),
                    );
                    let (y, b) = ctx.pop().unwrap();
                    let (x, a) = ctx.pop().unwrap();
                    cv.extend(csub);
                    let term_v = match Term::from_underlying_value(v) {
                        Ok(v) => v,
                        Err(_) => Term::Var(tmpvar.clone()), // dummy
                    };
                    (
                        cv,
                        Computation {
                            term: ComputationTerm::PatternMatch(
                                Box::new(tv),
                                (x, a),
                                (y, b),
                                Box::new(tm),
                            ),
                            ty: rtm.subst_term(&vec![(tmpvar, term_v)].into_iter().collect()),
                        },
                    )
                }
                _ => panic!("type error in pattern match"),
            }
        }
        term::Computation::Case(v, (x, _), m, (y, _), n) => {
            let (mut cv, tv) = value(ctx, v, used_pvar);
            match &tv.ty {
                rtype::Value::Sum(a, b) => {
                    let a = (**a).clone();
                    let b = (**b).clone();
                    ctx.push(x, a);
                    let (cm, tm) = computation(ctx, m, used_pvar);
                    let (x, a) = ctx.pop().unwrap();
                    cv.extend(cm);
                    ctx.push(y, b);
                    let (cn, tn) = computation(ctx, n, used_pvar);
                    let (y, b) = ctx.pop().unwrap();
                    cv.extend(cn);
                    let tmpvar = utils::mk_fresh_name("tmp", &ctx.vars());
                    ctx.push(tmpvar.clone(), tv.ty.clone());
                    let ty = rtype::Computation::refinement_template(
                        ctx,
                        &tm.ty.erase(),
                        used_pvar,
                        "case_result",
                    );
                    ctx.pop();
                    ctx.push(x.clone(), a);
                    cv.extend(rtype::Computation::subtype(
                        ctx,
                        &tm.ty,
                        &ty.subst_term(
                            &vec![(tmpvar.clone(), Term::Inl(Box::new(Term::Var(x))))]
                                .into_iter()
                                .collect(),
                        ),
                    ));
                    let (x, a) = ctx.pop().unwrap();
                    ctx.push(y.clone(), b);
                    cv.extend(rtype::Computation::subtype(
                        ctx,
                        &tn.ty,
                        &ty.subst_term(
                            &vec![(tmpvar.clone(), Term::Inr(Box::new(Term::Var(y))))]
                                .into_iter()
                                .collect(),
                        ),
                    ));
                    let (y, b) = ctx.pop().unwrap();
                    let term_v = match Term::from_underlying_value(v) {
                        Ok(v) => v,
                        Err(_) => Term::Var(tmpvar.clone()), // dummy
                    };
                    (
                        cv,
                        Computation {
                            term: ComputationTerm::Case(
                                Box::new(tv),
                                (x, a),
                                Box::new(tm),
                                (y, b),
                                Box::new(tn),
                            ),
                            ty: ty.subst_term(&vec![(tmpvar, term_v)].into_iter().collect()),
                        },
                    )
                }
                _ => panic!("type error in case"),
            }
        }
        term::Computation::Fix(x, m, c) => {
            let rc = rtype::Computation::refinement_template(ctx, c, used_pvar, "fix_var");
            ctx.push(x, rtype::Value::U(Box::new(rc.clone())));
            let (mut cm, tm) = computation(ctx, m, used_pvar);
            cm.extend(rtype::Computation::subtype(ctx, &tm.ty, &rc));
            let (x, _) = ctx.pop().unwrap();
            (
                cm,
                Computation {
                    term: ComputationTerm::Fix(x, Box::new(tm), rc.clone()),
                    ty: rc,
                },
            )
        }
        term::Computation::Explode(v, c) => {
            let (cv, tv) = value(ctx, v, used_pvar);
            let rc = rtype::Computation::refinement_template(ctx, c, used_pvar, "explode_result");
            match &tv.ty {
                rtype::Value::Empty => (
                    cv,
                    Computation {
                        term: ComputationTerm::Explode(Box::new(tv), rc.clone()),
                        ty: rc,
                    },
                ),
                _ => panic!("type error in explode"),
            }
        }
        term::Computation::Fail => {
            let dummy = utils::mk_fresh_name("fail_dummy", &ctx.vars());
            (
                Vec::new(),
                Computation {
                    term: ComputationTerm::Fail,
                    ty: rtype::Computation::Function(
                        dummy.clone(),
                        Box::new(rtype::Value::Unit(dummy, Formula::False)),
                        Box::new(rtype::Computation::F(Box::new(rtype::Value::Empty))),
                    ),
                },
            )
        }
        term::Computation::Add => {
            let mut vars = ctx.vars();
            let x = utils::mk_fresh_name("add_arg_1", &vars);
            vars.insert(x.clone());
            let y = utils::mk_fresh_name("add_arg_2", &vars);
            vars.insert(y.clone());
            let z = utils::mk_fresh_name("add_result", &vars);
            (
                Vec::new(),
                Computation {
                    term: ComputationTerm::Add,
                    ty: rtype::Computation::Function(
                        x.clone(),
                        Box::new(rtype::Value::Int(x.clone(), Formula::True)),
                        Box::new(rtype::Computation::Function(
                            y.clone(),
                            Box::new(rtype::Value::Int(y.clone(), Formula::True)),
                            Box::new(rtype::Computation::F(Box::new(rtype::Value::Int(
                                z.clone(),
                                Formula::Equal(
                                    Term::Var(z),
                                    Term::Add(Box::new(Term::Var(x)), Box::new(Term::Var(y))),
                                ),
                            )))),
                        )),
                    ),
                },
            )
        }
        term::Computation::Leq => {
            let mut vars = ctx.vars();
            let x = utils::mk_fresh_name("leq_arg_1", &vars);
            vars.insert(x.clone());
            let y = utils::mk_fresh_name("leq_arg_2", &vars);
            vars.insert(y.clone());
            let z = utils::mk_fresh_name("leq_result_dummy", &vars);
            (
                Vec::new(),
                Computation {
                    term: ComputationTerm::Leq,
                    ty: rtype::Computation::Function(
                        x.clone(),
                        Box::new(rtype::Value::Int(x.clone(), Formula::True)),
                        Box::new(rtype::Computation::Function(
                            y.clone(),
                            Box::new(rtype::Value::Int(y.clone(), Formula::True)),
                            Box::new(rtype::Computation::F(Box::new(rtype::Value::Sum(
                                Box::new(rtype::Value::Unit(
                                    z.clone(),
                                    Formula::Leq(Term::Var(x.clone()), Term::Var(y.clone())),
                                )),
                                Box::new(rtype::Value::Unit(
                                    z,
                                    Formula::Implies(
                                        Box::new(Formula::Leq(Term::Var(x), Term::Var(y))),
                                        Box::new(Formula::False),
                                    ),
                                )),
                            )))),
                        )),
                    ),
                },
            )
        }
        term::Computation::NDInt => {
            let dummy = utils::mk_fresh_name("ndint", &ctx.vars());
            (
                Vec::new(),
                Computation {
                    term: ComputationTerm::NDInt,
                    ty: rtype::Computation::F(Box::new(rtype::Value::Int(dummy, Formula::True))),
                },
            )
        }
    }
}
