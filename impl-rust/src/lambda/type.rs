#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Type {
    Var(String),
    Unit,
    //Empty,
    Pair(Box<Type>, Box<Type>),
    Sum(Box<Type>, Box<Type>),
    Function(Box<Type>, Box<Type>),
}

