use super::r#type::{Computation, Map, Value};

#[derive(Debug, Clone)]
pub struct Constraints {
    pub value: Vec<(Value, Value)>,
    pub computation: Vec<(Computation, Computation)>,
}
impl Constraints {
    pub fn extend(&mut self, other: Constraints) {
        self.value.extend(other.value);
        self.computation.extend(other.computation);
    }
    pub fn from_map(map: Map) -> Constraints {
        Constraints {
            value: map
                .value
                .into_iter()
                .map(|(x, t)| (Value::Var(x), t))
                .collect(),
            computation: map
                .computation
                .into_iter()
                .map(|(x, t)| (Computation::Var(x), t))
                .collect(),
        }
    }
    pub fn unify(self) -> Result<Map, String> {
        unify_sub(self, Map::new())
    }
}

fn unify_sub(mut constraints: Constraints, map: Map) -> Result<Map, String> {
    debug_assert!(map.dom().is_disjoint(&map.fv_cod()));
    match constraints.value.pop() {
        Some(c) => match c {
            (Value::Var(x), Value::Var(y)) if x == y => unify_sub(constraints, map),
            (Value::Var(x), t) => match map.value.get(&x) {
                Some(u) => {
                    constraints.value.push((u.clone(), t));
                    unify_sub(constraints, map)
                }
                None => {
                    let t = t.subst(&map);
                    let fv = t.fv();
                    if fv.value.contains(&x) {
                        Err(format!("{:?} != {:?}", Value::Var(x), t))
                    } else {
                        let mut x2t = Map::new();
                        x2t.value.insert(x, t);
                        let map = map.compose(x2t);
                        unify_sub(constraints, map)
                    }
                }
            },
            (t, Value::Var(x)) => {
                constraints.value.push((Value::Var(x), t));
                unify_sub(constraints, map)
            }
            (Value::Int, Value::Int) => unify_sub(constraints, map),
            (Value::Unit, Value::Unit) => unify_sub(constraints, map),
            (Value::Empty, Value::Empty) => unify_sub(constraints, map),
            (Value::Pair(a1, b1), Value::Pair(a2, b2)) => {
                constraints.value.push((*a1, *a2));
                constraints.value.push((*b1, *b2));
                unify_sub(constraints, map)
            }
            (Value::Sum(a1, b1), Value::Sum(a2, b2)) => {
                constraints.value.push((*a1, *a2));
                constraints.value.push((*b1, *b2));
                unify_sub(constraints, map)
            }
            (Value::U(c1), Value::U(c2)) => {
                constraints.computation.push((*c1, *c2));
                unify_sub(constraints, map)
            }
            (t, u) => Err(format!("{:?} != {:?}", t, u)),
        },
        None => match constraints.computation.pop() {
            Some(c) => match c {
                (Computation::Var(x), Computation::Var(y)) if x == y => unify_sub(constraints, map),
                (Computation::Var(x), t) => match map.computation.get(&x) {
                    Some(u) => {
                        constraints.computation.push((u.clone(), t));
                        unify_sub(constraints, map)
                    }
                    None => {
                        let t = t.subst(&map);
                        let fv = t.fv();
                        if fv.computation.contains(&x) {
                            Err(format!("{:?} != {:?}", Computation::Var(x), t))
                        } else {
                            let mut x2t = Map::new();
                            x2t.computation.insert(x, t);
                            let map = map.compose(x2t);
                            unify_sub(constraints, map)
                        }
                    }
                },
                (t, Computation::Var(x)) => {
                    constraints.computation.push((Computation::Var(x), t));
                    unify_sub(constraints, map)
                }
                (Computation::Function(a1, c1), Computation::Function(a2, c2)) => {
                    constraints.value.push((*a1, *a2));
                    constraints.computation.push((*c1, *c2));
                    unify_sub(constraints, map)
                }
                (Computation::F(a1), Computation::F(a2)) => {
                    constraints.value.push((*a1, *a2));
                    unify_sub(constraints, map)
                }
                (t, u) => Err(format!("{:?} != {:?}", t, u)),
            },
            None => Ok(map),
        },
    }
}
