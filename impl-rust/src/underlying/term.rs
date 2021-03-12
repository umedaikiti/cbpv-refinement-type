use super::super::utils;
use super::r#type;
use super::r#type::VarSet;
use std::collections::{HashMap, HashSet};

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Value {
    Var(String),
    Unit,
    Int(i64),
    Pair(Box<Value>, Box<Value>),
    Inr(Box<Value>, r#type::Value),
    Inl(Box<Value>, r#type::Value),
    Thunk(Box<Computation>),
}

impl Value {
    pub fn subst_type(&self, map: &r#type::Map) -> Self {
        match self {
            Value::Var(x) => Value::Var(x.clone()),
            Value::Unit => Value::Unit,
            Value::Int(i) => Value::Int(*i),
            Value::Pair(v, w) => {
                Value::Pair(Box::new(v.subst_type(map)), Box::new(w.subst_type(map)))
            }
            Value::Inr(v, b) => Value::Inr(Box::new(v.subst_type(map)), b.subst(map)),
            Value::Inl(v, a) => Value::Inr(Box::new(v.subst_type(map)), a.subst(map)),
            Value::Thunk(m) => Value::Thunk(Box::new(m.subst_type(map))),
        }
    }
    pub fn simplify(&self, used_var: &HashSet<String>) -> Self {
        match self {
            Value::Var(x) => Value::Var(x.clone()),
            Value::Unit => Value::Unit,
            Value::Int(i) => Value::Int(*i),
            Value::Pair(v, w) => Value::Pair(
                Box::new(v.simplify(used_var)),
                Box::new(w.simplify(used_var)),
            ),
            Value::Inl(v, b) => Value::Inl(Box::new(v.simplify(used_var)), b.clone()),
            Value::Inr(v, a) => Value::Inr(Box::new(v.simplify(used_var)), a.clone()),
            Value::Thunk(m) => Value::Thunk(Box::new(m.simplify(used_var))),
        }
    }
    pub fn subst(&self, map: &HashMap<String, Value>, used_var: &HashSet<String>) -> Self {
        match self {
            Value::Var(x) => match map.get(x) {
                Some(t) => (*t).subst(&HashMap::new(), used_var), // to remove shadowing
                None => Value::Var(x.clone()),
            },
            Value::Unit => Value::Unit,
            Value::Int(i) => Value::Int(*i),
            Value::Pair(v, w) => Value::Pair(
                Box::new(v.subst(map, used_var)),
                Box::new(w.subst(map, used_var)),
            ),
            Value::Inl(v, b) => Value::Inl(Box::new(v.subst(map, used_var)), b.clone()),
            Value::Inr(v, a) => Value::Inr(Box::new(v.subst(map, used_var)), a.clone()),
            Value::Thunk(m) => Value::Thunk(Box::new(m.subst(map, used_var))),
        }
    }
    pub fn free_type_vars(&self) -> VarSet {
        match self {
            Value::Var(_) | Value::Unit | Value::Int(_) => VarSet::new(),
            Value::Pair(v, w) => {
                let mut fv = v.free_type_vars();
                fv.extend(w.free_type_vars());
                fv
            }
            Value::Inl(v, a) | Value::Inr(v, a) => {
                let mut fv = v.free_type_vars();
                fv.extend(a.fv());
                fv
            }
            Value::Thunk(m) => m.free_type_vars(),
        }
    }
    //pub fn bv(&self) -> Option<Context<r#type::Value>> {
    //    match self {
    //        Value::Var(_) | Value::Unit | Value::Int(_) => Some(Context::new()),
    //        Value::Pair(v, w) => {
    //            let bv_v = v.bv()?;
    //            let bv_w = w.bv()?;
    //            Context::disjoint_union(bv_v, bv_w)
    //        }
    //        Value::Inl(v, _) | Value::Inr(v, _) => v.bv(),
    //        Value::Thunk(m) => m.bv(),
    //    }
    //}
    //pub fn elim_shadow(
    //    &mut self,
    //    used_var: &mut HashSet<String>,
    //    map: &mut HashMap<String, String>,
    //) {
    //    match self {
    //        Value::Var(x) => match map.get(x) {
    //            Some(y) => {
    //                *x = y.clone();
    //            }
    //            None => {}
    //        },
    //        Value::Unit | Value::Int(_) => {}
    //        Value::Pair(v, w) => {
    //            v.elim_shadow(used_var, map);
    //            w.elim_shadow(used_var, map);
    //        }
    //        Value::Inl(v, _) | Value::Inr(v, _) => {
    //            v.elim_shadow(used_var, map);
    //        }
    //        Value::Thunk(m) => {
    //            m.elim_shadow(used_var, map);
    //        }
    //    }
    //}
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Computation {
    Return(Box<Value>),
    SeqComp(Box<Computation>, (String, r#type::Value), Box<Computation>),
    Lambda((String, r#type::Value), Box<Computation>),
    App(Box<Computation>, Box<Value>),
    PatternMatch(
        Box<Value>,
        (String, r#type::Value),
        (String, r#type::Value),
        Box<Computation>,
    ),
    Case(
        Box<Value>,
        (String, r#type::Value),
        Box<Computation>,
        (String, r#type::Value),
        Box<Computation>,
    ),
    Force(Box<Value>),
    Fix(String, Box<Computation>, r#type::Computation),
    Explode(Box<Value>, r#type::Computation),
    Fail,
    Add,
    Leq,
    NDInt,
}

impl Computation {
    pub fn subst_type(&self, map: &r#type::Map) -> Self {
        match self {
            Computation::Return(v) => Computation::Return(Box::new(v.subst_type(map))),
            Computation::SeqComp(m, (x, a), n) => Computation::SeqComp(
                Box::new(m.subst_type(map)),
                (x.clone(), a.subst(map)),
                Box::new(n.subst_type(map)),
            ),
            Computation::Lambda((x, a), m) => {
                Computation::Lambda((x.clone(), a.subst(map)), Box::new(m.subst_type(map)))
            }
            Computation::App(m, v) => {
                Computation::App(Box::new(m.subst_type(map)), Box::new(v.subst_type(map)))
            }
            Computation::PatternMatch(v, (x, a), (y, b), m) => Computation::PatternMatch(
                Box::new(v.subst_type(map)),
                (x.clone(), a.subst(map)),
                (y.clone(), b.subst(map)),
                Box::new(m.subst_type(map)),
            ),
            Computation::Case(v, (x, a), m, (y, b), n) => Computation::Case(
                Box::new(v.subst_type(map)),
                (x.clone(), a.subst(map)),
                Box::new(m.subst_type(map)),
                (y.clone(), b.subst(map)),
                Box::new(n.subst_type(map)),
            ),
            Computation::Force(v) => Computation::Force(Box::new(v.subst_type(map))),
            Computation::Fix(x, m, c) => {
                Computation::Fix(x.clone(), Box::new(m.subst_type(map)), c.subst(map))
            }
            Computation::Explode(v, c) => {
                Computation::Explode(Box::new(v.subst_type(map)), c.subst(map))
            }
            Computation::Fail => Computation::Fail,
            Computation::Add => Computation::Add,
            Computation::Leq => Computation::Leq,
            Computation::NDInt => Computation::NDInt,
        }
    }
    pub fn free_type_vars(&self) -> VarSet {
        match self {
            Computation::Return(v) => v.free_type_vars(),
            Computation::SeqComp(m, (_, a), n) => {
                let mut fv = m.free_type_vars();
                fv.extend(a.fv());
                fv.extend(n.free_type_vars());
                fv
            }
            Computation::Lambda((_, a), m) => {
                let mut fv = a.fv();
                fv.extend(m.free_type_vars());
                fv
            }
            Computation::App(m, v) => {
                let mut fv = m.free_type_vars();
                fv.extend(v.free_type_vars());
                fv
            }
            Computation::PatternMatch(v, (_, a), (_, b), m) => {
                let mut fv = v.free_type_vars();
                fv.extend(a.fv());
                fv.extend(b.fv());
                fv.extend(m.free_type_vars());
                fv
            }
            Computation::Case(v, (_, a), m, (_, b), n) => {
                let mut fv = v.free_type_vars();
                fv.extend(a.fv());
                fv.extend(m.free_type_vars());
                fv.extend(b.fv());
                fv.extend(n.free_type_vars());
                fv
            }
            Computation::Force(v) => v.free_type_vars(),
            Computation::Fix(_, m, c) => {
                let mut fv = m.free_type_vars();
                fv.extend(c.fv());
                fv
            }
            Computation::Explode(v, c) => {
                let mut fv = v.free_type_vars();
                fv.extend(c.fv());
                fv
            }
            Computation::Fail | Computation::Add | Computation::Leq | Computation::NDInt => {
                VarSet::new()
            }
        }
    }
    pub fn simplify(&self, used_var: &HashSet<String>) -> Self {
        match self {
            Computation::Return(v) => Computation::Return(Box::new(v.simplify(used_var))),
            Computation::SeqComp(m, (x, a), n) => {
                let mut used_var_n = used_var.clone();
                used_var_n.insert(x.clone());
                match (m.simplify(used_var), n.simplify(&used_var_n)) {
                    (Computation::Return(v), n) => n
                        .subst(&vec![(x.clone(), *v)].into_iter().collect(), &used_var_n)
                        .simplify(used_var),
                    (m, Computation::Return(v)) => match *v {
                        Value::Var(y) if *x == y => m,
                        v => Computation::SeqComp(
                            Box::new(m),
                            (x.clone(), a.clone()),
                            Box::new(Computation::Return(Box::new(v))),
                        ),
                    },
                    (m, n) => {
                        Computation::SeqComp(Box::new(m), (x.clone(), a.clone()), Box::new(n))
                    }
                }
            }
            Computation::Lambda((x, a), m) => {
                let mut used_var = used_var.clone();
                used_var.insert(x.clone());
                Computation::Lambda((x.clone(), a.clone()), Box::new(m.simplify(&used_var)))
            }
            Computation::App(m, v) => {
                let v = v.simplify(used_var);
                match m.simplify(used_var) {
                    Computation::Lambda((x, _), m) => {
                        let mut used_var_x = used_var.clone();
                        used_var_x.insert(x.clone());
                        let mv = m.subst(&vec![(x, v)].into_iter().collect(), &used_var_x);
                        mv.simplify(used_var)
                    }
                    m => Computation::App(Box::new(m), Box::new(v)),
                }
            }
            Computation::PatternMatch(v, (x, a), (y, b), m) => {
                let mut used_var_m = used_var.clone();
                used_var_m.insert(x.clone());
                used_var_m.insert(y.clone());
                let m = m.simplify(&used_var_m);
                match v.simplify(used_var) {
                    Value::Pair(v1, v2) => m
                        .subst(
                            &vec![(x.clone(), *v1), (y.clone(), *v2)]
                                .into_iter()
                                .collect(),
                            &used_var_m,
                        )
                        .simplify(used_var),
                    v => Computation::PatternMatch(
                        Box::new(v),
                        (x.clone(), a.clone()),
                        (y.clone(), b.clone()),
                        Box::new(m),
                    ),
                }
            }
            Computation::Case(v, (x, a), m, (y, b), n) => {
                let mut used_var_m = used_var.clone();
                used_var_m.insert(x.clone());
                let mut used_var_n = used_var.clone();
                used_var_n.insert(y.clone());
                match v.simplify(used_var) {
                    Value::Inl(v, _) => {
                        let m = m.simplify(&used_var_m);
                        m.subst(&vec![(x.clone(), *v)].into_iter().collect(), &used_var_m)
                            .simplify(used_var)
                    }
                    Value::Inr(v, _) => {
                        let n = n.simplify(&used_var_n);
                        n.subst(&vec![(x.clone(), *v)].into_iter().collect(), &used_var_n)
                            .simplify(used_var)
                    }
                    v => Computation::Case(
                        Box::new(v),
                        (x.clone(), a.clone()),
                        Box::new(m.simplify(&used_var_m)),
                        (y.clone(), b.clone()),
                        Box::new(n.simplify(&used_var_n)),
                    ),
                }
            }
            Computation::Force(v) => match v.simplify(used_var) {
                Value::Thunk(m) => *m,
                v => Computation::Force(Box::new(v)),
            },
            Computation::Fix(x, m, c) => {
                let mut used_var = used_var.clone();
                used_var.insert(x.clone());
                Computation::Fix(x.clone(), Box::new(m.simplify(&used_var)), c.clone())
            }
            Computation::Explode(v, c) => {
                Computation::Explode(Box::new(v.simplify(used_var)), c.clone())
            }
            Computation::Fail => Computation::Fail,
            Computation::Add => Computation::Add,
            Computation::Leq => Computation::Leq,
            Computation::NDInt => Computation::NDInt,
        }
    }
    // fv(map) is a subset of used_var
    pub fn subst(&self, map: &HashMap<String, Value>, used_var: &HashSet<String>) -> Self {
        fn rename_bvar<F, T>(
            x: &String,
            mut map: HashMap<String, Value>,
            mut used_var: HashSet<String>,
            func: F,
        ) -> T
        where
            F: FnOnce((String, HashMap<String, Value>, HashSet<String>)) -> T,
        {
            let x_new = utils::mk_fresh_name(x, &used_var);
            used_var.insert(x_new.clone());
            map.insert(x.clone(), Value::Var(x_new.clone()));
            func((x_new, map, used_var))
        }
        match self {
            Computation::Return(v) => Computation::Return(Box::new(v.subst(map, used_var))),
            Computation::SeqComp(m, (x, a), n) => rename_bvar(
                x,
                map.clone(),
                used_var.clone(),
                |(x_new, map_n, used_var_n)| {
                    Computation::SeqComp(
                        Box::new(m.subst(map, used_var)),
                        (x_new, a.clone()),
                        Box::new(n.subst(&map_n, &used_var_n)),
                    )
                },
            ),
            Computation::Lambda((x, a), m) => rename_bvar(
                x,
                map.clone(),
                used_var.clone(),
                |(x_new, map, used_var)| {
                    Computation::Lambda((x_new, a.clone()), Box::new(m.subst(&map, &used_var)))
                },
            ),
            Computation::App(m, v) => Computation::App(
                Box::new(m.subst(map, used_var)),
                Box::new(v.subst(map, used_var)),
            ),
            Computation::PatternMatch(v, (x, a), (y, b), m) => {
                let v_subst = v.subst(map, used_var);
                rename_bvar(
                    x,
                    map.clone(),
                    used_var.clone(),
                    |(x_new, map, used_var)| {
                        rename_bvar(y, map, used_var, |(y_new, map, used_var)| {
                            Computation::PatternMatch(
                                Box::new(v_subst),
                                (x_new, a.clone()),
                                (y_new, b.clone()),
                                Box::new(m.subst(&map, &used_var)),
                            )
                        })
                    },
                )
            }
            Computation::Case(v, (x, a), m, (y, b), n) => rename_bvar(
                x,
                map.clone(),
                used_var.clone(),
                |(x_new, map_m, used_var_m)| {
                    rename_bvar(
                        y,
                        map.clone(),
                        used_var.clone(),
                        |(y_new, map_n, used_var_n)| {
                            Computation::Case(
                                Box::new(v.subst(map, used_var)),
                                (x_new, a.clone()),
                                Box::new(m.subst(&map_m, &used_var_m)),
                                (y_new, b.clone()),
                                Box::new(n.subst(&map_n, &used_var_n)),
                            )
                        },
                    )
                },
            ),
            Computation::Force(v) => Computation::Force(Box::new(v.subst(map, used_var))),
            Computation::Fix(x, m, c) => rename_bvar(
                x,
                map.clone(),
                used_var.clone(),
                |(x_new, map, used_var)| {
                    Computation::Fix(x_new, Box::new(m.subst(&map, &used_var)), c.clone())
                },
            ),
            Computation::Explode(v, c) => {
                Computation::Explode(Box::new(v.subst(map, used_var)), c.clone())
            }
            Computation::Fail => Computation::Fail,
            Computation::Add => Computation::Add,
            Computation::Leq => Computation::Leq,
            Computation::NDInt => Computation::NDInt,
        }
    }
    //pub fn elim_shadow(
    //    &mut self,
    //    used_var: &mut HashSet<String>,
    //    map: &mut HashMap<String, String>,
    //) {
    //    #[must_use]
    //    fn update(
    //        used_var: &mut HashSet<String>,
    //        map: &mut HashMap<String, String>,
    //        x: &mut String,
    //    ) -> (String, Option<String>) {
    //        let x_new = utils::mk_fresh_name(x, used_var);
    //        used_var.insert(x_new.clone());
    //        let x_old = std::mem::replace(x, x_new.clone());
    //        (x_old.clone(), map.insert(x_old, x_new))
    //    }
    //    fn restore(map: &mut HashMap<String, String>, save: (String, Option<String>)) {
    //        match save {
    //            (key, Some(value)) => {
    //                map.insert(key, value);
    //            }
    //            (key, None) => {
    //                map.remove(&key);
    //            }
    //        }
    //    }
    //    match self {
    //        Computation::Return(v) => {
    //            v.elim_shadow(used_var, map);
    //        }
    //        Computation::SeqComp(m, (x, _), n) => {
    //            m.elim_shadow(used_var, map);
    //            let save_x = update(used_var, map, x);
    //            n.elim_shadow(used_var, map);
    //            restore(map, save_x);
    //        }
    //        Computation::Lambda((x, _), m) => {
    //            let save_x = update(used_var, map, x);
    //            m.elim_shadow(used_var, map);
    //            restore(map, save_x);
    //        }
    //        Computation::App(m, v) => {
    //            m.elim_shadow(used_var, map);
    //            v.elim_shadow(used_var, map);
    //        }
    //        Computation::PatternMatch(v, (x, _), (y, _), m) => {
    //            v.elim_shadow(used_var, map);
    //            let save_x = update(used_var, map, x);
    //            let save_y = update(used_var, map, y);
    //            m.elim_shadow(used_var, map);
    //            restore(map, save_y);
    //            restore(map, save_x);
    //        }
    //        Computation::Case(v, (x, _), m, (y, _), n) => {
    //            v.elim_shadow(used_var, map);
    //            let save_x = update(used_var, map, x);
    //            m.elim_shadow(used_var, map);
    //            restore(map, save_x);
    //            let save_y = update(used_var, map, y);
    //            n.elim_shadow(used_var, map);
    //            restore(map, save_y);
    //        }
    //        Computation::Force(v) => {
    //            v.elim_shadow(used_var, map);
    //        }
    //        Computation::Fix(x, m, _) => {
    //            let save_x = update(used_var, map, x);
    //            m.elim_shadow(used_var, map);
    //            restore(map, save_x);
    //        }
    //        Computation::Explode(v, _) => {
    //            v.elim_shadow(used_var, map);
    //        }
    //        Computation::Fail => {}
    //    }
    //}
    //pub fn bv(&self) -> Option<Context<r#type::Value>> {
    //    match self {
    //        Computation::Return(v) => v.bv(),
    //        Computation::SeqComp(m, (x, a), n) => {
    //            let mut bv = Context::new();
    //            bv.push(x, a.clone());
    //            let bv_m = m.bv()?;
    //            let bv_n = n.bv()?;
    //            let bv = Context::disjoint_union(bv, bv_m)?;
    //            let bv = Context::disjoint_union(bv, bv_n);
    //            bv
    //        }
    //        Computation::Lambda((x, a), m) => {
    //            let mut bv = Context::new();
    //            bv.push(x, a.clone());
    //            let bv_m = m.bv()?;
    //            Context::disjoint_union(bv, bv_m)
    //        }
    //        Computation::App(m, v) => {
    //            let bv_m = m.bv()?;
    //            let bv_v = v.bv()?;
    //            Context::disjoint_union(bv_m, bv_v)
    //        }
    //        Computation::PatternMatch(v, (x, a), (y, b), m) => {
    //            let mut bv = Context::new();
    //            bv.push(x, a.clone());
    //            bv.push(y, b.clone());
    //            let bv_v = v.bv()?;
    //            let bv_m = m.bv()?;
    //            let bv = Context::disjoint_union(bv, bv_v)?;
    //            Context::disjoint_union(bv, bv_m)
    //        }
    //        Computation::Case(v, (x, a), m, (y, b), n) => {
    //            let mut bv = Context::new();
    //            bv.push(x, a.clone());
    //            bv.push(y, b.clone());
    //            let bv_v = v.bv()?;
    //            let bv_m = m.bv()?;
    //            let bv_n = n.bv()?;
    //            let bv = Context::disjoint_union(bv, bv_v)?;
    //            let bv = Context::disjoint_union(bv, bv_m)?;
    //            Context::disjoint_union(bv, bv_n)
    //        }
    //        Computation::Force(v) => v.bv(),
    //        Computation::Fix(x, m, c) => {
    //            let mut bv = Context::new();
    //            bv.push(x, r#type::Value::U(Box::new(c.clone())));
    //            let bv_m = m.bv()?;
    //            Context::disjoint_union(bv, bv_m)
    //        }
    //        Computation::Explode(v, _) => v.bv(),
    //        Computation::Fail | Computation::Add => Some(Context::new()),
    //    }
    //}
}
