use super::super::context::Context;
use once_cell::sync::Lazy;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::sync::Mutex;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Value {
    Var(String),
    Int,
    Unit,
    Pair(Box<Value>, Box<Value>),
    Empty,
    Sum(Box<Value>, Box<Value>),
    U(Box<Computation>),
}

impl Value {
    fn fmt_sub(&self, f: &mut fmt::Formatter, priority: i32) -> fmt::Result {
        match self {
            Value::Var(x) => write!(f, "{}", x),
            Value::Int => write!(f, "int"),
            Value::Unit => write!(f, "unit"),
            Value::Empty => write!(f, "empty"),
            Value::Pair(a, b) => {
                let p = 20;
                if priority >= p {
                    write!(f, "(")?;
                    a.fmt_sub(f, p)?;
                    write!(f, " * ")?;
                    b.fmt_sub(f, p)?;
                    write!(f, ")")
                } else {
                    a.fmt_sub(f, p)?;
                    write!(f, " * ")?;
                    b.fmt_sub(f, p)
                }
            }
            Value::Sum(a, b) => {
                let p = 10;
                if priority >= p {
                    write!(f, "(")?;
                    a.fmt_sub(f, p)?;
                    write!(f, " + ")?;
                    b.fmt_sub(f, p)?;
                    write!(f, ")")
                } else {
                    a.fmt_sub(f, p)?;
                    write!(f, " + ")?;
                    b.fmt_sub(f, p)
                }
            }
            Value::U(c) => {
                let p = 40;
                if priority >= p {
                    write!(f, "(U ")?;
                    c.fmt_sub(f, p - 1)?;
                    write!(f, ")")
                } else {
                    write!(f, "U ")?;
                    c.fmt_sub(f, p - 1)
                }
            }
        }
    }
}
impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.fmt_sub(f, 0)
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Computation {
    Var(String),
    Function(Box<Value>, Box<Computation>),
    F(Box<Value>),
}

impl Computation {
    fn fmt_sub(&self, f: &mut fmt::Formatter, priority: i32) -> fmt::Result {
        match self {
            Computation::Var(x) => write!(f, "{}", x),
            Computation::Function(a, c) => {
                let p = 30;
                if priority >= p {
                    write!(f, "(")?;
                    a.fmt_sub(f, p)?;
                    write!(f, " -> ")?;
                    c.fmt_sub(f, p - 1)?;
                    write!(f, ")")
                } else {
                    a.fmt_sub(f, p)?;
                    write!(f, " -> ")?;
                    c.fmt_sub(f, p - 1)
                }
            }
            Computation::F(a) => {
                let p = 40;
                if priority >= p {
                    write!(f, "(F ")?;
                    a.fmt_sub(f, p - 1)?;
                    write!(f, ")")
                } else {
                    write!(f, "F ")?;
                    a.fmt_sub(f, p - 1)
                }
            }
        }
    }
}

impl fmt::Display for Computation {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.fmt_sub(f, 0)
    }
}

/// Mapping from type variables to types.
#[derive(Debug)]
pub struct Map {
    pub value: HashMap<String, Value>,
    pub computation: HashMap<String, Computation>,
}
impl Map {
    pub fn new() -> Map {
        Map {
            value: HashMap::new(),
            computation: HashMap::new(),
        }
    }
    pub fn compose(self, other: Map) -> Map {
        let mut map = Map {
            value: self
                .value
                .into_iter()
                .map(|(k, v)| (k, v.subst(&other)))
                .collect(),
            computation: self
                .computation
                .into_iter()
                .map(|(k, v)| (k, v.subst(&other)))
                .collect(),
        };
        for (k, v) in other.value.into_iter() {
            if !map.value.contains_key(&k) {
                map.value.insert(k, v);
            }
        }
        for (k, v) in other.computation.into_iter() {
            if !map.computation.contains_key(&k) {
                map.computation.insert(k, v);
            }
        }
        map
    }
    pub fn dom(&self) -> VarSet {
        VarSet {
            value: self.value.keys().cloned().collect(),
            computation: self.computation.keys().cloned().collect(),
        }
    }
    pub fn fv_cod(&self) -> VarSet {
        let mut fv = VarSet::new();
        for val in self.value.values() {
            fv.extend(val.fv());
        }
        for val in self.computation.values() {
            fv.extend(val.fv());
        }
        fv
    }
}

/// Set of type variables.
pub struct VarSet {
    pub value: HashSet<String>,
    pub computation: HashSet<String>,
}
impl VarSet {
    pub fn extend(&mut self, other: VarSet) {
        self.value.extend(other.value);
        self.computation.extend(other.computation);
    }
    pub fn new() -> VarSet {
        VarSet {
            value: HashSet::new(),
            computation: HashSet::new(),
        }
    }
    pub fn is_disjoint(&self, other: &VarSet) -> bool {
        self.value.is_disjoint(&other.value) && self.computation.is_disjoint(&other.computation)
    }
    pub fn is_empty(&self) -> bool {
        self.value.is_empty() && self.computation.is_empty()
    }
}

static VALUE_COUNTER: Lazy<Mutex<i32>> = Lazy::new(|| Mutex::new(0));

impl Value {
    /// Make a fresh name for a value type variable.
    pub fn mk_fresh_name() -> String {
        let mut c = VALUE_COUNTER.lock().unwrap();
        let s = format!("var-val#{}", *c);
        *c += 1;
        s
    }

    pub fn subst(&self, map: &Map) -> Self {
        match self {
            Value::Var(x) => match map.value.get(x) {
                Some(t) => t.clone(),
                None => Value::Var(x.clone()),
            },
            Value::Int => Value::Int,
            Value::Unit => Value::Unit,
            Value::Pair(a, b) => Value::Pair(Box::new(a.subst(map)), Box::new(b.subst(map))),
            Value::Empty => Value::Empty,
            Value::Sum(a, b) => Value::Sum(Box::new(a.subst(map)), Box::new(b.subst(map))),
            Value::U(c) => Value::U(Box::new(c.subst(map))),
        }
    }
    pub fn fv(&self) -> VarSet {
        match self {
            Value::Var(x) => VarSet {
                value: vec![x.clone()].into_iter().collect(),
                computation: HashSet::new(),
            },
            Value::Int => VarSet::new(),
            Value::Unit => VarSet::new(),
            Value::Empty => VarSet::new(),
            Value::Pair(a, b) => {
                let mut fv = a.fv();
                fv.extend(b.fv());
                fv
            }
            Value::Sum(a, b) => {
                let mut fv = a.fv();
                fv.extend(b.fv());
                fv
            }
            Value::U(c) => c.fv(),
        }
    }
    pub fn is_pure(&self) -> bool {
        match self {
            Value::Var(_) => unimplemented!(),
            Value::Int | Value::Unit | Value::Empty => true,
            Value::Pair(a, b) | Value::Sum(a, b) => a.is_pure() && b.is_pure(),
            Value::U(_) => false,
        }
    }
}

impl Context<Value> {
    pub fn purify(&mut self) {
        self.0.retain(|(_, a)| a.is_pure());
    }
}

static COMPUTATION_COUNTER: Lazy<Mutex<i32>> = Lazy::new(|| Mutex::new(0));

impl Computation {
    pub fn mk_fresh_name() -> String {
        let mut c = COMPUTATION_COUNTER.lock().unwrap();
        let s = format!("var-comp#{}", *c);
        *c += 1;
        s
    }

    pub fn subst(&self, map: &Map) -> Self {
        match self {
            Computation::Var(x) => match map.computation.get(x) {
                Some(t) => t.clone(),
                None => Computation::Var(x.clone()),
            },
            Computation::Function(a, c) => {
                Computation::Function(Box::new(a.subst(map)), Box::new(c.subst(map)))
            }
            Computation::F(a) => Computation::F(Box::new(a.subst(map))),
        }
    }
    pub fn fv(&self) -> VarSet {
        match self {
            Computation::Var(x) => VarSet {
                value: HashSet::new(),
                computation: vec![x.clone()].into_iter().collect(),
            },
            Computation::Function(a, c) => {
                let mut fv = a.fv();
                fv.extend(c.fv());
                fv
            }
            Computation::F(a) => a.fv(),
        }
    }
}
