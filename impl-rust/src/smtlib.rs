use super::context::Context;
use std::fmt;

pub enum Sort {
    Int,
    Bool,
}

impl fmt::Display for Sort {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Sort::Int => write!(f, "Int"),
            Sort::Bool => write!(f, "Bool"),
        }
    }
}

pub enum Operation {
    Add,
    Sub,
    Mul,
    Int(i64),
    True,
    False,
}
impl fmt::Display for Operation {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Operation::Add => write!(f, "+"),
            Operation::Sub => write!(f, "-"),
            Operation::Mul => write!(f, "*"),
            Operation::Int(i) => write!(f, "{}", i),
            Operation::True => write!(f, "true"),
            Operation::False => write!(f, "false"),
        }
    }
}

pub enum Term {
    Var(String),
    App(Operation, Vec<Term>),
}
impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Term::Var(x) => write!(f, "{}", x),
            Term::App(op, args) => {
                if args.is_empty() {
                    write!(f, "{}", op)
                } else {
                    write!(f, "({}", op)?;
                    for t in args.iter() {
                        write!(f, " {}", t)?;
                    }
                    write!(f, ")")
                }
            }
        }
    }
}

pub enum Predicate {
    Var(String),
    Leq,
    Geq,
    Lt,
    Gt,
    Equal,
}
impl fmt::Display for Predicate {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Predicate::Var(p) => write!(f, "{}", p),
            Predicate::Leq => write!(f, "<="),
            Predicate::Geq => write!(f, ">="),
            Predicate::Lt => write!(f, "<"),
            Predicate::Gt => write!(f, ">"),
            Predicate::Equal => write!(f, "="),
        }
    }
}

pub enum Formula {
    True,
    False,
    App(Predicate, Vec<Term>),
    And(Vec<Formula>),
    Or(Vec<Formula>),
    Implies(Box<Formula>, Box<Formula>),
}
impl fmt::Display for Formula {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Formula::True => write!(f, "true"),
            Formula::False => write!(f, "false"),
            Formula::App(p, args) => {
                if args.is_empty() {
                    write!(f, "{}", p)
                } else {
                    write!(f, "({}", p)?;
                    for t in args.iter() {
                        write!(f, " {}", t)?;
                    }
                    write!(f, ")")
                }
            }
            Formula::And(fs) => {
                write!(f, "(and")?;
                for fml in fs.iter() {
                    write!(f, " {}", fml)?;
                }
                write!(f, ")")
            }
            Formula::Or(fs) => {
                write!(f, "(or")?;
                for fml in fs.iter() {
                    write!(f, " {}", fml)?;
                }
                write!(f, ")")
            }
            Formula::Implies(g, h) => {
                write!(f, "(=> {} {})", g, h)
            }
        }
    }
}

pub struct SmtLib {
    pub preds: Vec<(String, Vec<Sort>)>,
    pub constraints: Vec<(Context<Sort>, Formula)>,
}

impl fmt::Display for SmtLib {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "(set-logic HORN)")?;
        writeln!(f, "(set-info :status sat)")?;
        writeln!(f, "")?;
        for (p, sorts) in self.preds.iter() {
            write!(
                f,
                "(declare-fun {} ({}) Bool)\n",
                p,
                sorts
                    .iter()
                    .map(|sort| sort.to_string())
                    .collect::<Vec<_>>()
                    .join(" ")
            )?;
        }
        writeln!(f, "")?;
        for (ctx, fml) in self.constraints.iter() {
            write!(
                f,
                "(assert (forall ({}) {}))\n",
                ctx.0
                    .iter()
                    .map(|(x, sort)| format!("({} {})", x, sort))
                    .collect::<Vec<_>>()
                    .join(" "),
                fml
            )?;
        }
        writeln!(f, "(check-sat)")
    }
}
