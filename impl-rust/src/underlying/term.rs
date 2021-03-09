use super::r#type;
use std::collections::HashMap;

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
    pub fn simplify(&self) -> Self {
        match self {
            Value::Var(x) => Value::Var(x.clone()),
            Value::Unit => Value::Unit,
            Value::Int(i) => Value::Int(*i),
            Value::Pair(v, w) => Value::Pair(Box::new(v.simplify()), Box::new(w.simplify())),
            Value::Inl(v, b) => Value::Inl(Box::new(v.simplify()), b.clone()),
            Value::Inr(v, a) => Value::Inr(Box::new(v.simplify()), a.clone()),
            Value::Thunk(m) => Value::Thunk(Box::new(m.simplify())),
        }
    }
    pub fn subst(&self, map: &HashMap<String, Value>) -> Self {
        match self {
            Value::Var(x) => match map.get(x) {
                Some(t) => (*t).clone(),
                None => Value::Var(x.clone()),
            },
            Value::Unit => Value::Unit,
            Value::Int(i) => Value::Int(*i),
            Value::Pair(v, w) => Value::Pair(Box::new(v.subst(map)), Box::new(w.subst(map))),
            Value::Inl(v, b) => Value::Inl(Box::new(v.subst(map)), b.clone()),
            Value::Inr(v, a) => Value::Inr(Box::new(v.subst(map)), a.clone()),
            Value::Thunk(m) => Value::Thunk(Box::new(m.subst(map))),
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
        }
    }
    pub fn simplify(&self) -> Self {
        match self {
            Computation::Return(v) => Computation::Return(Box::new(v.simplify())),
            Computation::SeqComp(m, (x, a), n) => match (m.simplify(), n.simplify()) {
                (Computation::Return(v), n) => n
                    .subst(&vec![(x.clone(), *v)].into_iter().collect())
                    .simplify(),
                (m, Computation::Return(v)) => match *v {
                    Value::Var(y) if *x == y => m,
                    v => Computation::SeqComp(
                        Box::new(m),
                        (x.clone(), a.clone()),
                        Box::new(Computation::Return(Box::new(v))),
                    ),
                },
                (m, n) => Computation::SeqComp(Box::new(m), (x.clone(), a.clone()), Box::new(n)),
            },
            Computation::Lambda((x, a), m) => {
                Computation::Lambda((x.clone(), a.clone()), Box::new(m.simplify()))
            }
            Computation::App(m, v) => {
                let v = v.simplify();
                match m.simplify() {
                    Computation::Lambda((x, _), m) => {
                        let mv = m.subst(&vec![(x, v)].into_iter().collect());
                        mv.simplify()
                    }
                    m => Computation::App(Box::new(m), Box::new(v)),
                }
            }
            Computation::PatternMatch(v, (x, a), (y, b), m) => {
                let m = m.simplify();
                match v.simplify() {
                    Value::Pair(v1, v2) => m
                        .subst(
                            &vec![(x.clone(), *v1), (y.clone(), *v2)]
                                .into_iter()
                                .collect(),
                        )
                        .simplify(),
                    v => Computation::PatternMatch(
                        Box::new(v),
                        (x.clone(), a.clone()),
                        (y.clone(), b.clone()),
                        Box::new(m),
                    ),
                }
            }
            Computation::Case(v, (x, a), m, (y, b), n) => match v.simplify() {
                Value::Inl(v, _) => {
                    let m = m.simplify();
                    m.subst(&vec![(x.clone(), *v)].into_iter().collect())
                        .simplify()
                }
                Value::Inr(v, _) => {
                    let n = n.simplify();
                    n.subst(&vec![(x.clone(), *v)].into_iter().collect())
                        .simplify()
                }
                v => Computation::Case(
                    Box::new(v),
                    (x.clone(), a.clone()),
                    Box::new(m.simplify()),
                    (y.clone(), b.clone()),
                    Box::new(n.simplify()),
                ),
            },
            Computation::Force(v) => match v.simplify() {
                Value::Thunk(m) => *m,
                v => Computation::Force(Box::new(v)),
            },
            Computation::Fix(x, m, c) => {
                Computation::Fix(x.clone(), Box::new(m.simplify()), c.clone())
            }
            Computation::Explode(v, c) => Computation::Explode(Box::new(v.simplify()), c.clone()),
            Computation::Fail => Computation::Fail,
            Computation::Add => Computation::Add,
            Computation::Leq => Computation::Leq,
        }
    }
    pub fn subst(&self, map: &HashMap<String, Value>) -> Self {
        match self {
            Computation::Return(v) => Computation::Return(Box::new(v.subst(map))),
            Computation::SeqComp(m, (x, a), n) => Computation::SeqComp(
                Box::new(m.subst(map)),
                (x.clone(), a.clone()),
                Box::new(n.subst(map)),
            ),
            Computation::Lambda((x, a), m) => {
                Computation::Lambda((x.clone(), a.clone()), Box::new(m.subst(map)))
            }
            Computation::App(m, v) => {
                Computation::App(Box::new(m.subst(map)), Box::new(v.subst(map)))
            }
            Computation::PatternMatch(v, (x, a), (y, b), m) => Computation::PatternMatch(
                Box::new(v.subst(map)),
                (x.clone(), a.clone()),
                (y.clone(), b.clone()),
                Box::new(m.subst(map)),
            ),
            Computation::Case(v, (x, a), m, (y, b), n) => Computation::Case(
                Box::new(v.subst(map)),
                (x.clone(), a.clone()),
                Box::new(m.subst(map)),
                (y.clone(), b.clone()),
                Box::new(n.subst(map)),
            ),
            Computation::Force(v) => Computation::Force(Box::new(v.subst(map))),
            Computation::Fix(x, m, c) => {
                Computation::Fix(x.clone(), Box::new(m.subst(map)), c.clone())
            }
            Computation::Explode(v, c) => Computation::Explode(Box::new(v.subst(map)), c.clone()),
            Computation::Fail => Computation::Fail,
            Computation::Add => Computation::Add,
            Computation::Leq => Computation::Leq,
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
