#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Term {
    Var(String),
    Lambda(String, Box<Term>),
    App(Box<Term>, Box<Term>),
    Unit,
    Int(i64),
    Pair(Box<Term>, Box<Term>),
    Inr(Box<Term>),
    Inl(Box<Term>),
    Case(Box<Term>, String, Box<Term>, String, Box<Term>),
    PatternMatch(Box<Term>, String, String, Box<Term>),
    Fail,
    Add,
    Leq,
    Explode(Box<Term>),
    Fix(String, Box<Term>),
}
