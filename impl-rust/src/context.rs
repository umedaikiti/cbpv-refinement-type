#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Context<T>(pub Vec<(String, T)>);

impl<T> Context<T> {
    pub fn get(&self, var: &str) -> Option<&T> {
        self.0
            .iter()
            .rev()
            .find_map(|(x, a)| if x == var { Some(a) } else { None })
    }
    pub fn new() -> Context<T> {
        Context(Vec::new())
    }
    pub fn push<S: Into<String>>(&mut self, x: S, a: T) {
        self.0.push((x.into(), a))
    }
    pub fn pop(&mut self) -> Option<(String, T)> {
        self.0.pop()
    }
    pub fn vars(&self) -> std::collections::HashSet<String> {
        self.0.iter().map(|(x, _)| x).cloned().collect()
    }
    pub fn extend(&mut self, other: Self) {
        self.0.extend(other.0);
    }
    pub fn disjoint_union(mut ctx1: Self, ctx2: Self) -> Option<Self> {
        if ctx1.vars().is_disjoint(&ctx2.vars()) {
            ctx1.extend(ctx2);
            Some(ctx1)
        } else {
            None
        }
    }
}

impl<T> From<Vec<(String, T)>> for Context<T> {
    fn from(v: Vec<(String, T)>) -> Self {
        Context(v)
    }
}
