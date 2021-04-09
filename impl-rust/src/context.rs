/// (Ordered) list of variables and their associated types.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Context<T>(pub Vec<(String, T)>);

impl<T> Context<T> {
    /// Get the type for `var`.
    pub fn get(&self, var: &str) -> Option<&T> {
        self.0
            .iter()
            .rev()
            .find_map(|(x, a)| if x == var { Some(a) } else { None })
    }
    /// Create an empty context.
    pub fn new() -> Context<T> {
        Context(Vec::new())
    }
    /// Push `x` : `a` at the end of the context.
    pub fn push<S: Into<String>>(&mut self, x: S, a: T) {
        self.0.push((x.into(), a))
    }
    /// Pop the last entry of the context.
    pub fn pop(&mut self) -> Option<(String, T)> {
        self.0.pop()
    }
    /// Return the set of variables.
    pub fn vars(&self) -> std::collections::HashSet<String> {
        self.0.iter().map(|(x, _)| x).cloned().collect()
    }
    pub fn extend(&mut self, other: Self) {
        self.0.extend(other.0);
    }
}

impl<T> From<Vec<(String, T)>> for Context<T> {
    fn from(v: Vec<(String, T)>) -> Self {
        Context(v)
    }
}
