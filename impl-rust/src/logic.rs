use super::context::Context;
use super::smtlib;
use super::underlying::r#type;
use super::underlying::term::Value;
use super::utils;
use once_cell::sync::Lazy;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::sync::Mutex;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Term {
    Var(String),
    Unit,
    Int(i64),
    Pair(Box<Term>, Box<Term>),
    Inl(Box<Term>),
    Inr(Box<Term>),
    Add(Box<Term>, Box<Term>),
}
impl Term {
    pub fn subst(&self, map: &HashMap<String, Term>) -> Term {
        match self {
            Term::Var(x) => match map.get(x) {
                Some(t) => t.clone(),
                None => Term::Var(x.clone()),
            },
            Term::Unit => Term::Unit,
            Term::Int(i) => Term::Int(*i),
            Term::Pair(s, t) => Term::Pair(Box::new(s.subst(map)), Box::new(t.subst(map))),
            Term::Inl(t) => Term::Inl(Box::new(t.subst(map))),
            Term::Inr(t) => Term::Inr(Box::new(t.subst(map))),
            Term::Add(s, t) => Term::Add(Box::new(s.subst(map)), Box::new(t.subst(map))),
        }
    }
    pub fn fv(&self) -> HashSet<String> {
        match self {
            Term::Var(x) => vec![x.clone()].into_iter().collect(),
            Term::Unit | Term::Int(_) => HashSet::new(),
            Term::Inl(v) | Term::Inr(v) => v.fv(),
            Term::Pair(v, w) | Term::Add(v, w) => {
                let mut fvv = v.fv();
                fvv.extend(w.fv());
                fvv
            }
        }
    }
    pub fn from_underlying_value(v: &Value) -> Result<Term, String> {
        match v {
            Value::Var(x) => Ok(Term::Var(x.clone())),
            Value::Unit => Ok(Term::Unit),
            Value::Int(i) => Ok(Term::Int(*i)),
            Value::Pair(v, w) => {
                let v = Term::from_underlying_value(v)?;
                let w = Term::from_underlying_value(w)?;
                Ok(Term::Pair(Box::new(v), Box::new(w)))
            }
            Value::Inl(v, _) => {
                let v = Term::from_underlying_value(v)?;
                Ok(Term::Inl(Box::new(v)))
            }
            Value::Inr(v, _) => {
                let v = Term::from_underlying_value(v)?;
                Ok(Term::Inr(Box::new(v)))
            }
            Value::Thunk(_) => Err("impure value".to_string()),
        }
    }
    pub fn to_smtlib(&self) -> Option<smtlib::Term> {
        match self {
            Term::Var(x) => Some(smtlib::Term::Var(x.clone())),
            Term::Int(i) => Some(smtlib::Term::App(smtlib::Operation::Int(*i), Vec::new())),
            Term::Inl(t) => match **t {
                Term::Unit => Some(smtlib::Term::App(smtlib::Operation::True, Vec::new())),
                _ => None,
            },
            Term::Inr(t) => match **t {
                Term::Unit => Some(smtlib::Term::App(smtlib::Operation::False, Vec::new())),
                _ => None,
            },
            Term::Add(s, t) => {
                let s = s.to_smtlib()?;
                let t = t.to_smtlib()?;
                Some(smtlib::Term::App(smtlib::Operation::Add, vec![s, t]))
            }
            Term::Pair(_, _) | Term::Unit => None,
        }
    }
    fn pattern_match(&self, other: &Term) -> Option<HashMap<String, Term>> {
        match (self, other) {
            (Term::Var(x), _) => Some(vec![(x.clone(), other.clone())].into_iter().collect()),
            (Term::Int(i), Term::Int(j)) if *i == *j => Some(HashMap::new()),
            (Term::Unit, Term::Unit) => Some(HashMap::new()),
            (Term::Inl(pattern), Term::Inl(t)) => pattern.pattern_match(t),
            (Term::Inr(pattern), Term::Inr(t)) => pattern.pattern_match(t),
            (Term::Pair(p1, p2), Term::Pair(t1, t2)) => {
                let mut m1 = p1.pattern_match(t1)?;
                let m2 = p2.pattern_match(t2)?;
                let k1: HashSet<&String> = m1.keys().collect();
                let k2: HashSet<&String> = m2.keys().collect();
                if k1.is_disjoint(&k2) {
                    m1.extend(m2);
                    Some(m1)
                } else {
                    panic!("invalid pattern")
                }
            }
            _ => None,
        }
    }
    fn fmt_sub(&self, f: &mut fmt::Formatter, priority: i32) -> fmt::Result {
        match self {
            Term::Var(x) => write!(f, "{}", x),
            Term::Int(i) => write!(f, "{}", i),
            Term::Inl(t) => {
                let p = 40;
                if priority >= p {
                    write!(f, "(inl ")?;
                    t.fmt_sub(f, p - 1)?;
                    write!(f, ")")
                } else {
                    write!(f, "inl ")?;
                    t.fmt_sub(f, p - 1)
                }
            }
            _ => unimplemented!(),
        }
    }
}
impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.fmt_sub(f, 0)
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Formula {
    PVar(String, Vec<Term>),
    True,
    False,
    Equal(Term, Term),
    Leq(Term, Term),
    And(Vec<Formula>),
    Or(Vec<Formula>),
    Implies(Box<Formula>, Box<Formula>),
}

static PNAME_COUNTER: Lazy<Mutex<i32>> = Lazy::new(|| Mutex::new(0));

impl Formula {
    pub fn mk_fresh_pname() -> String {
        let mut c = PNAME_COUNTER.lock().unwrap();
        let s = format!("P{}", *c);
        *c += 1;
        s
    }
    pub fn reset_pname_counter() {
        let mut c = PNAME_COUNTER.lock().unwrap();
        *c = 0;
    }
    pub fn mk_and(mut p: Vec<Formula>) -> Formula {
        match p.len() {
            0 => Formula::True,
            1 => p.pop().unwrap(),
            _ => Formula::And(p),
        }
    }
    pub fn mk_or(mut p: Vec<Formula>) -> Formula {
        match p.len() {
            0 => Formula::False,
            1 => p.pop().unwrap(),
            _ => Formula::Or(p),
        }
    }

    pub fn fv(&self) -> HashSet<String> {
        match self {
            Formula::True | Formula::False => HashSet::new(),
            Formula::PVar(_, args) => {
                let mut v = HashSet::new();
                for t in args.iter() {
                    v.extend(t.fv());
                }
                v
            }
            Formula::Equal(s, t) | Formula::Leq(s, t) => {
                let mut v = s.fv();
                v.extend(t.fv());
                v
            }
            Formula::And(l) | Formula::Or(l) => {
                let mut v = HashSet::new();
                for f in l.iter() {
                    v.extend(f.fv());
                }
                v
            }
            Formula::Implies(f, g) => {
                let mut v = f.fv();
                v.extend(g.fv());
                v
            }
        }
    }
    pub fn subst_term(&self, map: &HashMap<String, Term>) -> Formula {
        match self {
            Formula::PVar(x, args) => {
                Formula::PVar(x.clone(), args.iter().map(|t| t.subst(map)).collect())
            }
            Formula::True => Formula::True,
            Formula::False => Formula::False,
            Formula::Equal(s, t) => Formula::Equal(s.subst(map), t.subst(map)),
            Formula::Leq(s, t) => Formula::Leq(s.subst(map), t.subst(map)),
            Formula::And(v) => Formula::And(v.iter().map(|f| f.subst_term(map)).collect()),
            Formula::Or(v) => Formula::Or(v.iter().map(|f| f.subst_term(map)).collect()),
            Formula::Implies(f, g) => {
                Formula::Implies(Box::new(f.subst_term(map)), Box::new(g.subst_term(map)))
            }
        }
    }
    pub fn rename_tvar(&self, from: &str, to: &str) -> Formula {
        self.subst_term(
            &vec![(from.to_string(), Term::Var(to.to_string()))]
                .into_iter()
                .collect(),
        )
    }
    pub fn simplify_equalities(&self) -> Self {
        match self {
            Formula::Equal(v, w) => {
                fn simplify(v: &Term, w: &Term) -> Vec<Formula> {
                    match (v, w) {
                        (Term::Unit, Term::Unit) => Vec::new(),
                        (Term::Inl(v), Term::Inl(w)) => simplify(v, w),
                        (Term::Inr(v), Term::Inr(w)) => simplify(v, w),
                        (Term::Inl(_), Term::Inr(_)) | (Term::Inr(_), Term::Inl(_)) => {
                            vec![Formula::False]
                        }
                        (Term::Pair(v1, v2), Term::Pair(w1, w2)) => {
                            let mut f = simplify(v1, w1);
                            f.extend(simplify(v2, w2));
                            f
                        }
                        _ => vec![Formula::Equal(v.clone(), w.clone())],
                    }
                }
                Formula::mk_and(simplify(v, w))
            }
            Formula::PVar(_, _) | Formula::True | Formula::False | Formula::Leq(_, _) => {
                self.clone()
            }
            Formula::And(l) => Formula::And(l.iter().map(|f| f.simplify_equalities()).collect()),
            Formula::Or(l) => Formula::Or(l.iter().map(|f| f.simplify_equalities()).collect()),
            Formula::Implies(f, g) => Formula::Implies(
                Box::new(f.simplify_equalities()),
                Box::new(g.simplify_equalities()),
            ),
        }
    }
    pub fn to_smtlib(&self) -> Option<smtlib::Formula> {
        match self {
            Formula::PVar(p, args) => {
                let mut new_args = Vec::new();
                for t in args.iter() {
                    let new_t = t.to_smtlib()?;
                    new_args.push(new_t);
                }
                Some(smtlib::Formula::App(
                    smtlib::Predicate::Var(p.clone()),
                    new_args,
                ))
            }
            Formula::True => Some(smtlib::Formula::True),
            Formula::False => Some(smtlib::Formula::False),
            Formula::And(l) => {
                let mut conj = Vec::new();
                for f in l.iter() {
                    let new_f = f.to_smtlib()?;
                    conj.push(new_f);
                }
                Some(smtlib::Formula::And(conj))
            }
            Formula::Or(l) => {
                let mut disj = Vec::new();
                for f in l.iter() {
                    let new_f = f.to_smtlib()?;
                    disj.push(new_f);
                }
                Some(smtlib::Formula::Or(disj))
            }
            Formula::Implies(f, g) => {
                let f = f.to_smtlib()?;
                let g = g.to_smtlib()?;
                Some(smtlib::Formula::Implies(Box::new(f), Box::new(g)))
            }
            Formula::Equal(s, t) => {
                let s = s.to_smtlib()?;
                let t = t.to_smtlib()?;
                Some(smtlib::Formula::App(smtlib::Predicate::Equal, vec![s, t]))
            }
            Formula::Leq(s, t) => {
                let s = s.to_smtlib()?;
                let t = t.to_smtlib()?;
                Some(smtlib::Formula::App(smtlib::Predicate::Leq, vec![s, t]))
            }
        }
    }
    fn replace_pvar(
        &mut self,
        p: &String,
        replace: &Vec<(Vec<Term>, (String, Vec<Term>, Vec<r#type::Value>))>,
    ) {
        match self {
            Formula::PVar(q, args) => {
                if q == p {
                    fn pattern_match(
                        p: &Vec<Term>,
                        t: &Vec<Term>,
                    ) -> Option<HashMap<String, Term>> {
                        assert_eq!(p.len(), t.len());
                        let mut map = HashMap::new();
                        for (p, t) in p.iter().zip(t.iter()) {
                            let m = p.pattern_match(t)?;
                            let map_keys: HashSet<&String> = map.keys().collect();
                            if map_keys.is_disjoint(&m.keys().collect()) {
                                map.extend(m);
                            } else {
                                return None;
                            }
                        }
                        Some(map)
                    }
                    match replace
                        .iter()
                        .find_map(|(pattern, (new_p, new_p_args, _))| {
                            let map = pattern_match(pattern, args)?;
                            Some((map, new_p.clone(), new_p_args))
                        }) {
                        Some((map, new_p, new_p_args)) => {
                            *q = new_p;
                            *args = new_p_args.iter().map(|t| t.subst(&map)).collect();
                        }
                        None => {}
                    }
                }
            }
            Formula::And(l) | Formula::Or(l) => {
                for f in l.iter_mut() {
                    f.replace_pvar(p, replace);
                }
            }
            Formula::Implies(f, g) => {
                f.replace_pvar(p, replace);
                g.replace_pvar(p, replace);
            }
            Formula::True | Formula::False => {}
            Formula::Equal(_, _) | Formula::Leq(_, _) => {}
        }
    }
    //fn replace_pvar(&mut self, pattern: (&String, &Vec<Term>), to: (&String, &Vec<Term>)) {
    //    match self {
    //        Formula::PVar(p, args) => {
    //            if p == pattern.0 {
    //                fn pattern_match(
    //                    p: &Vec<Term>,
    //                    t: &Vec<Term>,
    //                ) -> Option<HashMap<String, Term>> {
    //                    assert_eq!(p.len(), t.len());
    //                    let mut map = HashMap::new();
    //                    for (p, t) in p.iter().zip(t.iter()) {
    //                        let m = p.pattern_match(t)?;
    //                        let map_keys: HashSet<&String> = map.keys().collect();
    //                        if map_keys.is_disjoint(&m.keys().collect()) {
    //                            map.extend(m);
    //                        } else {
    //                            return None;
    //                        }
    //                    }
    //                    Some(map)
    //                }
    //                match pattern_match(&pattern.1, args) {
    //                    Some(map) => {
    //                        *p = to.0.clone();
    //                        *args = to.1.iter().map(|t| t.subst(&map)).collect();
    //                    }
    //                    None => {}
    //                }
    //            }
    //        }
    //        Formula::And(l) | Formula::Or(l) => {
    //            for f in l.iter_mut() {
    //                f.replace_pvar(pattern, to);
    //            }
    //        }
    //        Formula::Implies(f, g) => {
    //            f.replace_pvar(pattern, to);
    //            g.replace_pvar(pattern, to);
    //        }
    //        Formula::True | Formula::False => {}
    //        Formula::Equal(_, _) | Formula::Leq(_, _) => {}
    //    }
    //}
}
//#[test]
//fn test_replace_pvar() {
//    let mut f = Formula::PVar(
//        "P".to_string(),
//        vec![Term::Inl(Box::new(Term::Var("x".to_string())))],
//    );
//    f.replace_pvar(
//        (
//            &"P".to_string(),
//            &vec![Term::Inl(Box::new(Term::Var("x".to_string())))],
//        ),
//        (&"Q".to_string(), &vec![Term::Var("x".to_string())]),
//    );
//    assert_eq!(
//        f,
//        Formula::PVar("Q".to_string(), vec![Term::Var("x".to_string())])
//    );
//}

impl r#type::Value {
    pub fn to_smtlib(&self) -> Option<smtlib::Sort> {
        match self {
            r#type::Value::Int => Some(smtlib::Sort::Int),
            r#type::Value::Pair(a, b)
                if **a == r#type::Value::Unit && **b == r#type::Value::Unit =>
            {
                Some(smtlib::Sort::Bool)
            }
            _ => None,
        }
    }
}

pub fn to_smtlib(
    pctx: &Context<Vec<r#type::Value>>,
    constraints: &Vec<(Context<r#type::Value>, Formula)>,
) -> Option<smtlib::SmtLib> {
    let mut preds = Vec::new();
    for (x, params) in pctx.0.iter() {
        let mut new_params = Vec::new();
        for a in params.iter() {
            let a = a.to_smtlib()?;
            new_params.push(a);
        }
        preds.push((x.clone(), new_params));
    }
    let mut new_constraints = Vec::new();
    for (ctx, f) in constraints.iter() {
        let mut new_ctx = Context::new();
        for (x, a) in ctx.0.iter() {
            let a = a.to_smtlib()?;
            new_ctx.push(x, a);
        }
        let f = f.to_smtlib()?;
        new_constraints.push((new_ctx, f));
    }
    Some(smtlib::SmtLib {
        preds: preds,
        constraints: new_constraints,
    })
}

fn gen_term(
    t: &r#type::Value,
    used_var: &mut HashSet<String>,
) -> Vec<(Term, Context<r#type::Value>)> {
    match t {
        r#type::Value::Var(_) => panic!("type variable not allowed"),
        r#type::Value::U(_) => panic!("impure"),
        r#type::Value::Empty => Vec::new(),
        r#type::Value::Unit => vec![(Term::Unit, Context::new())],
        r#type::Value::Int => {
            let x = utils::mk_fresh_name("x", used_var);
            used_var.insert(x.clone());
            vec![(Term::Var(x.clone()), vec![(x, r#type::Value::Int)].into())]
        }
        r#type::Value::Sum(a, b) => {
            let mut l: Vec<(Term, Context<r#type::Value>)> = gen_term(a, used_var)
                .into_iter()
                .map(|(t, ctx)| (Term::Inl(Box::new(t)), ctx))
                .collect();
            let r: Vec<(Term, Context<r#type::Value>)> = gen_term(b, used_var)
                .into_iter()
                .map(|(t, ctx)| (Term::Inr(Box::new(t)), ctx))
                .collect();
            l.extend(r);
            l
        }
        r#type::Value::Pair(a, b) => {
            let l = gen_term(a, used_var);
            let r = gen_term(b, used_var);
            let mut v = Vec::new();
            for (tl, ctxl) in l.iter() {
                for (tr, ctxr) in r.iter() {
                    let mut ctx = ctxl.clone();
                    ctx.extend(ctxr.clone());
                    v.push((Term::Pair(Box::new(tl.clone()), Box::new(tr.clone())), ctx));
                }
            }
            v
        }
    }
}

fn gen_pred_replace(
    p: &str,
    params: &Vec<r#type::Value>,
    used_pvar: &mut HashSet<String>,
) -> Vec<(Vec<Term>, (String, Vec<Term>, Vec<r#type::Value>))> {
    let mut r: Vec<(Vec<Term>, Context<r#type::Value>)> = vec![(Vec::new(), Context::new())];
    let mut used_var = HashSet::new();
    for param in params.iter() {
        let v = gen_term(param, &mut used_var);
        let mut new_r = Vec::new();
        for (vt, ctx) in r.iter() {
            for (t, c) in v.iter() {
                let mut vt = vt.clone();
                vt.push(t.clone());
                let mut ctx = ctx.clone();
                ctx.extend(c.clone());
                new_r.push((vt, ctx));
            }
        }
        r = new_r;
    }
    r.into_iter()
        .map(|(pattern, ctx)| {
            let p = utils::mk_fresh_name(p, used_pvar);
            used_pvar.insert(p.clone());
            let mut tm = Vec::new();
            let mut types = Vec::new();
            for (x, ty) in ctx.0.into_iter() {
                tm.push(Term::Var(x));
                types.push(ty);
            }
            (pattern, (p, tm, types))
        })
        .collect()
}

#[test]
fn test_simplify() {
    assert_eq!(
        simplify(
            Context::new(),
            vec![(
                vec![("x".to_string(), r#type::Value::Empty)].into(),
                Formula::False
            )]
        ),
        (Context::new(), Vec::new())
    );
    assert_eq!(
        simplify(
            vec![(
                "P".to_string(),
                vec![
                    r#type::Value::Sum(
                        Box::new(r#type::Value::Int),
                        Box::new(r#type::Value::Empty)
                    ),
                    r#type::Value::Unit
                ]
            )]
            .into(),
            vec![(
                vec![
                    (
                        "x".to_string(),
                        r#type::Value::Sum(
                            Box::new(r#type::Value::Int),
                            Box::new(r#type::Value::Empty)
                        )
                    ),
                    ("y".to_string(), r#type::Value::Unit)
                ]
                .into(),
                Formula::PVar(
                    "P".to_string(),
                    vec![Term::Var("x".to_string()), Term::Var("y".to_string())]
                )
            )]
        ),
        (
            vec![("P".to_string(), vec![r#type::Value::Int])].into(),
            vec![(
                vec![("x".to_string(), r#type::Value::Int)].into(),
                Formula::PVar("P".to_string(), vec![Term::Var("x".to_string())])
            )]
        )
    );
}

pub fn simplify(
    pvar_ctx: Context<Vec<r#type::Value>>,
    constraints: Vec<(Context<r#type::Value>, Formula)>,
) -> (
    Context<Vec<r#type::Value>>,
    Vec<(Context<r#type::Value>, Formula)>,
) {
    fn is_empty_type(t: &r#type::Value) -> bool {
        match t {
            r#type::Value::Empty => true,
            r#type::Value::Unit | r#type::Value::Int => false,
            r#type::Value::Sum(a, b) => is_empty_type(a) && is_empty_type(b),
            r#type::Value::Pair(a, b) => is_empty_type(a) || is_empty_type(b),
            _ => panic!("impure type"),
        }
    }
    let mut constraints_new = Vec::new();
    for (mut ctx, fml) in constraints.into_iter() {
        let fv = fml.fv();
        ctx.0.retain(|(x, a)| fv.contains(x) || is_empty_type(a));
        constraints_new.extend(remove_pair_sum_unit_empty(ctx, fml));
    }
    let mut new_pvar_ctx = Context::new();
    let mut new_used_pvar = HashSet::new();
    for (p, arg_types) in pvar_ctx.0.iter() {
        let replace = gen_pred_replace(&p, arg_types, &mut new_used_pvar);
        for (_, fml) in constraints_new.iter_mut() {
            fml.replace_pvar(&p, &replace);
        }
        for (_, (new_p, _, new_p_arg_types)) in replace.into_iter() {
            new_pvar_ctx.push(new_p, new_p_arg_types);
        }
    }
    (new_pvar_ctx, constraints_new)
}

pub fn remove_pair_sum_unit_empty(
    ctx: Context<r#type::Value>,
    fml: Formula,
) -> Vec<(Context<r#type::Value>, Formula)> {
    let mut used_var = ctx.vars();
    remove_pair_sum_unit_empty_sub(ctx, &mut used_var, fml)
}

fn remove_pair_sum_unit_empty_sub(
    mut ctx: Context<r#type::Value>,
    used_var: &mut HashSet<String>,
    mut fml: Formula,
) -> Vec<(Context<r#type::Value>, Formula)> {
    match ctx.0.pop() {
        Some((x, a)) => match a {
            r#type::Value::Unit => {
                used_var.remove(&x);
                remove_pair_sum_unit_empty_sub(
                    ctx,
                    used_var,
                    fml.subst_term(&vec![(x, Term::Unit)].into_iter().collect()),
                )
            }
            r#type::Value::Pair(a, b) => {
                let xa = x.clone();
                let xb = utils::mk_fresh_name(&x, &used_var);
                used_var.insert(xb.clone());
                fml = fml.subst_term(
                    &vec![(
                        x,
                        Term::Pair(
                            Box::new(Term::Var(xa.clone())),
                            Box::new(Term::Var(xb.clone())),
                        ),
                    )]
                    .into_iter()
                    .collect(),
                );
                ctx.push(xa, *a);
                ctx.push(xb, *b);
                remove_pair_sum_unit_empty_sub(ctx, used_var, fml)
            }
            r#type::Value::Sum(a, b) => {
                let fml_inl = fml.subst_term(
                    &vec![(x.clone(), Term::Inl(Box::new(Term::Var(x.clone()))))]
                        .into_iter()
                        .collect(),
                );
                let fml_inr = fml.subst_term(
                    &vec![(x.clone(), Term::Inr(Box::new(Term::Var(x.clone()))))]
                        .into_iter()
                        .collect(),
                );
                let mut ctx_l = ctx.clone();
                ctx_l.push(x.clone(), *a);
                let mut ctx_r = ctx;
                ctx_r.push(x, *b);
                let mut result = remove_pair_sum_unit_empty_sub(ctx_l, used_var, fml_inl);
                result.extend(remove_pair_sum_unit_empty_sub(ctx_r, used_var, fml_inr));
                result
            }
            r#type::Value::Empty => Vec::new(),
            a => remove_pair_sum_unit_empty_sub(ctx, used_var, fml)
                .into_iter()
                .map(|(mut ctx, fml)| {
                    ctx.push(x.clone(), a.clone());
                    (ctx, fml)
                })
                .collect(),
        },
        None => {
            vec![(Context::new(), fml.simplify_equalities())]
        }
    }
}
