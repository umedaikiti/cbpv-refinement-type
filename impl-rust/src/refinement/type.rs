use super::super::context::Context;
use super::super::logic::{Formula, Term};
use super::super::underlying;
use std::collections::HashMap;
use std::fmt;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Value {
    Int(String, Formula),
    Unit(String, Formula),
    Pair(String, Box<Value>, Box<Value>),
    Empty,
    Sum(Box<Value>, Box<Value>),
    U(Box<Computation>),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Computation {
    Function(String, Box<Value>, Box<Computation>),
    F(Box<Value>),
}

impl Value {
    pub fn erase(&self) -> underlying::r#type::Value {
        match self {
            Value::Int(_, _) => underlying::r#type::Value::Int,
            Value::Unit(_, _) => underlying::r#type::Value::Unit,
            Value::Pair(_, a, b) => {
                underlying::r#type::Value::Pair(Box::new(a.erase()), Box::new(b.erase()))
            }
            Value::Empty => underlying::r#type::Value::Empty,
            Value::Sum(a, b) => {
                underlying::r#type::Value::Sum(Box::new(a.erase()), Box::new(b.erase()))
            }
            Value::U(c) => underlying::r#type::Value::U(Box::new(c.erase())),
        }
    }
    pub fn subtype(
        ctx: &mut Context<Value>,
        a: &Value,
        b: &Value,
    ) -> Vec<(Context<underlying::r#type::Value>, Formula)> {
        match (a, b) {
            (Value::Int(x, f), Value::Int(y, g)) => {
                let mut p = ctx.collect_predicate();
                p.push(f.clone());
                let mut ctx_constraint = ctx.erase_purify();
                ctx_constraint.push(x, underlying::r#type::Value::Int);
                vec![(
                    ctx_constraint,
                    Formula::Implies(Box::new(Formula::mk_and(p)), Box::new(g.rename_tvar(y, x))),
                )]
            }
            (Value::Unit(x, f), Value::Unit(y, g)) => {
                let mut p = ctx.collect_predicate();
                p.push(f.clone());
                let mut ctx_constraint = ctx.erase_purify();
                ctx_constraint.push(x, underlying::r#type::Value::Unit);
                vec![(
                    ctx_constraint,
                    Formula::Implies(Box::new(Formula::mk_and(p)), Box::new(g.rename_tvar(y, x))),
                )]
            }
            (Value::Pair(x1, a1, b1), Value::Pair(x2, a2, b2)) => {
                let mut ca = Value::subtype(ctx, a1, a2);
                let b2 = &b2.subst_term(
                    &vec![(x2.clone(), Term::Var(x1.clone()))]
                        .into_iter()
                        .collect(),
                );
                ctx.push(x1, (**a1).clone());
                let cb = Value::subtype(ctx, b1, b2);
                ctx.pop();
                ca.extend(cb);
                ca
            }
            (Value::Empty, Value::Empty) => Vec::new(),
            (Value::Sum(a1, b1), Value::Sum(a2, b2)) => {
                let mut ca = Value::subtype(ctx, a1, a2);
                let cb = Value::subtype(ctx, b1, b2);
                ca.extend(cb);
                ca
            }
            (Value::U(c), Value::U(d)) => Computation::subtype(ctx, c, d),
            (a, b) => panic!("type mismatch: {} <-> {}", a, b),
        }
    }
    pub fn subst_term(&self, map: &HashMap<String, Term>) -> Value {
        match self {
            Value::Int(x, f) => {
                debug_assert!(!map.contains_key(x));
                Value::Int(x.clone(), f.subst_term(map))
            }
            Value::Unit(x, f) => {
                debug_assert!(!map.contains_key(x));
                Value::Unit(x.clone(), f.subst_term(map))
            }
            Value::Pair(x, a, b) => {
                debug_assert!(!map.contains_key(x));
                Value::Pair(
                    x.clone(),
                    Box::new(a.subst_term(map)),
                    Box::new(b.subst_term(map)),
                )
            }
            Value::Empty => Value::Empty,
            Value::Sum(a, b) => {
                Value::Sum(Box::new(a.subst_term(map)), Box::new(b.subst_term(map)))
            }
            Value::U(c) => Value::U(Box::new(c.subst_term(map))),
        }
    }
    fn fmt_sub(&self, f: &mut fmt::Formatter, priority: i32) -> fmt::Result {
        match self {
            Value::Int(x, fml) => write!(f, "{{ {}:int | {} }}", x, fml),
            Value::Unit(x, fml) => write!(f, "{{ {}:unit | {} }}", x, fml),
            Value::Empty => write!(f, "empty"),
            Value::Pair(x, a, b) => {
                let p = 20;
                if priority >= p {
                    write!(f, "(({}:", x)?;
                    a.fmt_sub(f, 0)?;
                    write!(f, ") * ")?;
                    b.fmt_sub(f, p)?;
                    write!(f, ")")
                } else {
                    write!(f, "({}:", x)?;
                    a.fmt_sub(f, p)?;
                    write!(f, ") * ")?;
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

impl Computation {
    pub fn erase(&self) -> underlying::r#type::Computation {
        match self {
            Computation::Function(_, a, c) => {
                underlying::r#type::Computation::Function(Box::new(a.erase()), Box::new(c.erase()))
            }
            Computation::F(a) => underlying::r#type::Computation::F(Box::new(a.erase())),
        }
    }
    pub fn subst_term(&self, map: &HashMap<String, Term>) -> Computation {
        match self {
            Computation::Function(x, a, c) => {
                debug_assert!(!map.contains_key(x));
                Computation::Function(
                    x.clone(),
                    Box::new(a.subst_term(map)),
                    Box::new(c.subst_term(map)),
                )
            }
            Computation::F(a) => Computation::F(Box::new(a.subst_term(map))),
        }
    }
    pub fn subtype(
        ctx: &mut Context<Value>,
        c: &Computation,
        d: &Computation,
    ) -> Vec<(Context<underlying::r#type::Value>, Formula)> {
        match (c, d) {
            (Computation::Function(x1, a1, c1), Computation::Function(x2, a2, c2)) => {
                let mut constraints = Value::subtype(ctx, a2, a1);
                let c2 = &c2.subst_term(
                    &vec![(x2.clone(), Term::Var(x1.clone()))]
                        .into_iter()
                        .collect(),
                );
                ctx.push(x1, (**a2).clone());
                constraints.extend(Computation::subtype(ctx, c1, c2));
                ctx.pop();
                constraints
            }
            (Computation::F(a), Computation::F(b)) => Value::subtype(ctx, a, b),
            _ => panic!("type mismatch"),
        }
    }
    fn fmt_sub(&self, f: &mut fmt::Formatter, priority: i32) -> fmt::Result {
        match self {
            Computation::Function(x, a, c) => {
                let p = 30;
                if priority >= p {
                    write!(f, "(({}:", x)?;
                    a.fmt_sub(f, 0)?;
                    write!(f, ") -> ")?;
                    c.fmt_sub(f, p - 1)?;
                    write!(f, ")")
                } else {
                    write!(f, "({}:", x)?;
                    a.fmt_sub(f, 0)?;
                    write!(f, ") -> ")?;
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

impl Context<Value> {
    pub fn erase_purify(&self) -> Context<underlying::r#type::Value> {
        Context(
            self.0
                .iter()
                .filter_map(|(x, a)| {
                    let a = a.erase();
                    if a.is_pure() {
                        Some((x.clone(), a))
                    } else {
                        None
                    }
                })
                .collect(),
        )
    }
    pub fn collect_predicate(&self) -> Vec<Formula> {
        self.0
            .iter()
            .filter_map(|(x, a)| match a {
                Value::Int(v, p) | Value::Unit(v, p) => Some(p.rename_tvar(v, x)),
                _ => None,
            })
            .collect()
    }
}
