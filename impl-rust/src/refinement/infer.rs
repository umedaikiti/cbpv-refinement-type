use super::super::context::Context;
use super::super::logic::{Formula, Term};
use super::super::underlying::r#type as utype;
use super::super::underlying::term;
use super::super::utils;
use super::r#type as rtype;

impl rtype::Value {
    pub fn refinement_template(
        ctx: &mut Context<rtype::Value>,
        ut: &utype::Value,
        used_pvar: &mut Context<Vec<utype::Value>>,
        var_name_hint: &str,
    ) -> rtype::Value {
        match ut {
            utype::Value::Var(_) => panic!("refining type variables is not allowed"),
            utype::Value::Unit => {
                let pure_ctx = ctx.erase_purify();
                let pname = Formula::mk_fresh_pname();
                used_pvar.push(
                    pname.clone(),
                    pure_ctx.0.iter().map(|(_, a)| a.clone()).collect(),
                );
                let v = utils::mk_fresh_name(var_name_hint, &pure_ctx.vars());
                rtype::Value::Unit(
                    v,
                    Formula::PVar(
                        pname,
                        pure_ctx.0.into_iter().map(|(x, _)| Term::Var(x)).collect(),
                    ),
                )
            }
            utype::Value::Int => {
                let v = utils::mk_fresh_name(var_name_hint, &ctx.vars());
                let mut pure_ctx = ctx.erase_purify();
                pure_ctx.push(v.clone(), utype::Value::Int);
                let pname = Formula::mk_fresh_pname();
                used_pvar.push(
                    pname.clone(),
                    pure_ctx.0.iter().map(|(_, a)| a.clone()).collect(),
                );
                rtype::Value::Int(
                    v,
                    Formula::PVar(
                        pname,
                        pure_ctx.0.into_iter().map(|(x, _)| Term::Var(x)).collect(),
                    ),
                )
            }
            utype::Value::Empty => rtype::Value::Empty,
            utype::Value::Sum(a, b) => {
                let a = rtype::Value::refinement_template(
                    ctx,
                    a,
                    used_pvar,
                    &format!("{}_l", var_name_hint),
                );
                let b = rtype::Value::refinement_template(
                    ctx,
                    b,
                    used_pvar,
                    &format!("{}_r", var_name_hint),
                );
                rtype::Value::Sum(Box::new(a), Box::new(b))
            }
            utype::Value::Pair(a, b) => {
                let v_fst = format!("{}_fst", var_name_hint);
                let v_snd = format!("{}_snd", var_name_hint);
                let ra = rtype::Value::refinement_template(ctx, a, used_pvar, &v_fst);
                let x = utils::mk_fresh_name(&v_fst, &ctx.vars());
                ctx.push(x.clone(), ra.clone());
                let rb = rtype::Value::refinement_template(ctx, b, used_pvar, &v_snd);
                ctx.pop();
                rtype::Value::Pair(x, Box::new(ra), Box::new(rb))
            }
            utype::Value::U(c) => {
                let rc = rtype::Computation::refinement_template(ctx, c, used_pvar, var_name_hint);
                rtype::Value::U(Box::new(rc))
            }
        }
    }
}

impl rtype::Computation {
    pub fn refinement_template(
        ctx: &mut Context<rtype::Value>,
        ut: &utype::Computation,
        used_pvar: &mut Context<Vec<utype::Value>>,
        var_name_hint: &str,
    ) -> rtype::Computation {
        match ut {
            utype::Computation::Var(_) => panic!("refining type variables is not allowed"),
            utype::Computation::F(a) => {
                let ra = rtype::Value::refinement_template(ctx, a, used_pvar, var_name_hint);
                rtype::Computation::F(Box::new(ra))
            }
            utype::Computation::Function(a, c) => {
                let v_arg = format!("{}_arg", var_name_hint);
                let v_body = format!("{}_body", var_name_hint);
                let ra = rtype::Value::refinement_template(ctx, a, used_pvar, &v_arg);
                let x = utils::mk_fresh_name(&v_arg, &ctx.vars());
                ctx.push(x.clone(), ra.clone());
                let rc = rtype::Computation::refinement_template(ctx, c, used_pvar, &v_body);
                ctx.pop();
                rtype::Computation::Function(x, Box::new(ra), Box::new(rc))
            }
        }
    }
}

pub fn value(
    ctx: &mut Context<rtype::Value>,
    v: &term::Value,
    used_pvar: &mut Context<Vec<utype::Value>>,
) -> (Vec<(Context<utype::Value>, Formula)>, rtype::Value) {
    match v {
        term::Value::Var(x) => match ctx.get(x) {
            Some(rtype::Value::Unit(v, _)) => {
                let v = utils::mk_fresh_name(v, &ctx.vars());
                (Vec::new(), rtype::Value::Unit(v, Formula::True))
            }
            Some(rtype::Value::Int(v, _)) => {
                let v = utils::mk_fresh_name(v, &ctx.vars());
                (
                    Vec::new(),
                    rtype::Value::Int(
                        v.clone(),
                        Formula::Equal(Term::Var(v), Term::Var(x.clone())),
                    ),
                )
            }
            Some(a) => (Vec::new(), a.clone()),
            None => panic!(format!("variable {} not found in the context", x)),
        },
        term::Value::Unit => {
            let v = utils::mk_fresh_name("unit_val", &ctx.vars());
            (Vec::new(), rtype::Value::Unit(v, Formula::True))
        }
        term::Value::Int(i) => {
            let v = utils::mk_fresh_name(&format!("int_const_{}", i), &ctx.vars());
            (
                Vec::new(),
                rtype::Value::Int(v.clone(), Formula::Equal(Term::Var(v), Term::Int(*i))),
            )
        }
        term::Value::Pair(v, w) => {
            let (mut cv, tv) = value(ctx, v, used_pvar);
            let (cw, tw) = value(ctx, w, used_pvar);
            cv.extend(cw);
            let x = utils::mk_fresh_name("pair_fst", &ctx.vars());
            match Term::from_underlying_value(v) {
                Ok(v) => {
                    ctx.push(x.clone(), tv.clone());
                    let rtw =
                        rtype::Value::refinement_template(ctx, &tw.erase(), used_pvar, "pair_snd");
                    ctx.pop();
                    let csub = rtype::Value::subtype(
                        ctx,
                        &tw,
                        &rtw.subst_term(&vec![(x.clone(), v)].into_iter().collect()),
                    );
                    cv.extend(csub);
                    (cv, rtype::Value::Pair(x, Box::new(tv), Box::new(rtw)))
                }
                Err(_) => (cv, rtype::Value::Pair(x, Box::new(tv), Box::new(tw))),
            }
        }
        term::Value::Inl(v, b) => {
            let (cv, tv) = value(ctx, v, used_pvar);
            let tb = rtype::Value::refinement_template(ctx, b, used_pvar, "sum_r");
            (cv, rtype::Value::Sum(Box::new(tv), Box::new(tb)))
        }
        term::Value::Inr(v, a) => {
            let (cv, tv) = value(ctx, v, used_pvar);
            let ta = rtype::Value::refinement_template(ctx, a, used_pvar, "sum_l");
            (cv, rtype::Value::Sum(Box::new(ta), Box::new(tv)))
        }
        term::Value::Thunk(m) => {
            let (cm, tm) = computation(ctx, m, used_pvar);
            (cm, rtype::Value::U(Box::new(tm)))
        }
    }
}
pub fn computation(
    ctx: &mut Context<rtype::Value>,
    m: &term::Computation,
    used_pvar: &mut Context<Vec<utype::Value>>,
) -> (Vec<(Context<utype::Value>, Formula)>, rtype::Computation) {
    match m {
        term::Computation::Return(v) => {
            let (cv, tv) = value(ctx, v, used_pvar);
            (cv, rtype::Computation::F(Box::new(tv)))
        }
        term::Computation::SeqComp(m, (x, _), n) => {
            let (mut cm, tm) = computation(ctx, m, used_pvar);
            match tm {
                rtype::Computation::F(a) => {
                    let a = *a;
                    ctx.push(x, a);
                    let (cn, tn) = computation(ctx, n, used_pvar);
                    let (x, a) = ctx.pop().unwrap();
                    let ty = rtype::Computation::refinement_template(
                        ctx,
                        &tn.erase(),
                        used_pvar,
                        "seq_comp_result",
                    );
                    ctx.push(x, a);
                    let csub = rtype::Computation::subtype(ctx, &tn, &ty);
                    ctx.pop();
                    cm.extend(cn);
                    cm.extend(csub);
                    (cm, ty)
                }
                _ => panic!("type error in sequential composition"),
            }
        }
        term::Computation::App(m, v) => {
            let (mut cm, tm) = computation(ctx, m, used_pvar);
            match tm {
                rtype::Computation::Function(x, a, c) => {
                    let (cv, tv) = value(ctx, v, used_pvar);
                    let csub = rtype::Value::subtype(ctx, &tv, &a);
                    cm.extend(cv);
                    cm.extend(csub);
                    match Term::from_underlying_value(v) {
                        Ok(v) => (cm, c.subst_term(&vec![(x, v)].into_iter().collect())),
                        Err(_) => (cm, *c),
                    }
                }
                _ => panic!("type error in function application"),
            }
        }
        term::Computation::Lambda((x, a), m) => {
            let ra = rtype::Value::refinement_template(ctx, a, used_pvar, "lambda_arg_var");
            ctx.push(x, ra);
            let (cm, tm) = computation(ctx, m, used_pvar);
            let (x, ra) = ctx.pop().unwrap();
            (
                cm,
                rtype::Computation::Function(x, Box::new(ra), Box::new(tm)),
            )
        }
        term::Computation::Force(v) => {
            let (cv, tv) = value(ctx, v, used_pvar);
            match tv {
                rtype::Value::U(c) => (cv, *c),
                _ => panic!("type error in force"),
            }
        }
        term::Computation::PatternMatch(v, (x, _), (y, _), m) => {
            let (mut cv, tv) = value(ctx, v, used_pvar);
            match &tv {
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
                    ctx.push(tmpvar.clone(), tv);
                    let rtm = rtype::Computation::refinement_template(
                        ctx,
                        &tm.erase(),
                        used_pvar,
                        "pm_result",
                    );
                    ctx.pop();
                    ctx.push(x.clone(), a);
                    ctx.push(y.clone(), b);
                    let csub = rtype::Computation::subtype(
                        ctx,
                        &tm,
                        &rtm.subst_term(
                            &vec![(
                                tmpvar.clone(),
                                Term::Pair(Box::new(Term::Var(x)), Box::new(Term::Var(y))),
                            )]
                            .into_iter()
                            .collect(),
                        ),
                    );
                    ctx.pop();
                    ctx.pop();
                    cv.extend(csub);
                    let term_v = match Term::from_underlying_value(v) {
                        Ok(v) => v,
                        Err(_) => Term::Var(tmpvar.clone()), // dummy
                    };
                    (
                        cv,
                        rtm.subst_term(&vec![(tmpvar, term_v)].into_iter().collect()),
                    )
                }
                _ => panic!("type error in pattern match"),
            }
        }
        term::Computation::Case(v, (x, _), m, (y, _), n) => {
            let (mut cv, tv) = value(ctx, v, used_pvar);
            match &tv {
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
                    ctx.push(tmpvar.clone(), tv);
                    let ty = rtype::Computation::refinement_template(
                        ctx,
                        &tm.erase(),
                        used_pvar,
                        "case_result",
                    );
                    ctx.pop();
                    ctx.push(x.clone(), a);
                    cv.extend(rtype::Computation::subtype(
                        ctx,
                        &tm,
                        &ty.subst_term(
                            &vec![(tmpvar.clone(), Term::Inl(Box::new(Term::Var(x))))]
                                .into_iter()
                                .collect(),
                        ),
                    ));
                    ctx.pop();
                    ctx.push(y.clone(), b);
                    cv.extend(rtype::Computation::subtype(
                        ctx,
                        &tn,
                        &ty.subst_term(
                            &vec![(tmpvar.clone(), Term::Inr(Box::new(Term::Var(y))))]
                                .into_iter()
                                .collect(),
                        ),
                    ));
                    ctx.pop();
                    let term_v = match Term::from_underlying_value(v) {
                        Ok(v) => v,
                        Err(_) => Term::Var(tmpvar.clone()), // dummy
                    };
                    (
                        cv,
                        ty.subst_term(&vec![(tmpvar, term_v)].into_iter().collect()),
                    )
                }
                _ => panic!("type error in case"),
            }
        }
        term::Computation::Fix(x, m, c) => {
            let rc = rtype::Computation::refinement_template(ctx, c, used_pvar, "fix_var");
            ctx.push(x, rtype::Value::U(Box::new(rc.clone())));
            let (mut cm, tm) = computation(ctx, m, used_pvar);
            cm.extend(rtype::Computation::subtype(ctx, &tm, &rc));
            ctx.pop();
            (cm, rc)
        }
        term::Computation::Explode(v, c) => {
            let (cv, tv) = value(ctx, v, used_pvar);
            match tv {
                rtype::Value::Empty => (
                    cv,
                    rtype::Computation::refinement_template(ctx, c, used_pvar, "explode_result"),
                ),
                _ => panic!("type error in explode"),
            }
        }
        term::Computation::Fail => {
            let dummy = utils::mk_fresh_name("fail_dummy", &ctx.vars());
            (
                Vec::new(),
                rtype::Computation::Function(
                    dummy.clone(),
                    Box::new(rtype::Value::Unit(dummy, Formula::False)),
                    Box::new(rtype::Computation::F(Box::new(rtype::Value::Empty))),
                ),
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
                rtype::Computation::Function(
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
                rtype::Computation::Function(
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
            )
        }
        term::Computation::NDInt => {
            let dummy = utils::mk_fresh_name("ndint", &ctx.vars());
            (
                Vec::new(),
                rtype::Computation::F(Box::new(rtype::Value::Int(dummy, Formula::True))),
            )
        }
    }
}
