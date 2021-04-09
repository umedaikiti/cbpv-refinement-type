use super::super::context::Context;
use super::r#type;
use super::term;
use super::unification::Constraints;

impl term::Value {
    /// Hindley–Milner type inference.
    pub fn infer(
        &self,
        ctx: &mut Context<r#type::Value>,
    ) -> Result<(r#type::Map, r#type::Value), String> {
        match self {
            term::Value::Var(x) => match ctx.get(x) {
                Some(t) => Ok((r#type::Map::new(), t.clone())),
                None => Err(format!("unbound variable: {}", x)),
            },
            term::Value::Unit => Ok((r#type::Map::new(), r#type::Value::Unit)),
            term::Value::Int(_) => Ok((r#type::Map::new(), r#type::Value::Int)),
            term::Value::Pair(v, w) => {
                let (mv, tv) = v.infer(ctx)?;
                let (mw, tw) = w.infer(ctx)?;
                let mut constraints = Constraints::from_map(mv);
                constraints.extend(Constraints::from_map(mw));
                let m = constraints.unify()?;
                Ok((m, r#type::Value::Pair(Box::new(tv), Box::new(tw))))
            }
            term::Value::Inl(v, b) => {
                let (m, t) = v.infer(ctx)?;
                Ok((m, r#type::Value::Sum(Box::new(t), Box::new(b.clone()))))
            }
            term::Value::Inr(v, a) => {
                let (m, t) = v.infer(ctx)?;
                Ok((m, r#type::Value::Sum(Box::new(a.clone()), Box::new(t))))
            }
            term::Value::Thunk(m) => {
                let (map, t) = m.infer(ctx)?;
                Ok((map, r#type::Value::U(Box::new(t))))
            }
        }
    }
}

impl term::Computation {
    pub fn infer(
        &self,
        ctx: &mut Context<r#type::Value>,
    ) -> Result<(r#type::Map, r#type::Computation), String> {
        match self {
            term::Computation::Return(v) => {
                let (map, t) = v.infer(ctx)?;
                Ok((map, r#type::Computation::F(Box::new(t))))
            }
            term::Computation::SeqComp(m, (x, a), n) => {
                let (mm, tm) = m.infer(ctx)?;
                ctx.push(x, a.clone());
                let (mn, tn) = n.infer(ctx)?;
                let mut constraints = Constraints {
                    value: Vec::new(),
                    computation: vec![(r#type::Computation::F(Box::new(a.clone())), tm)],
                };
                constraints.extend(Constraints::from_map(mm));
                constraints.extend(Constraints::from_map(mn));
                let map = constraints.unify()?;
                Ok((map, tn))
            }
            term::Computation::Lambda((x, a), m) => {
                ctx.push(x, a.clone());
                let (map, t) = m.infer(ctx)?;
                Ok((
                    map,
                    r#type::Computation::Function(Box::new(a.clone()), Box::new(t)),
                ))
            }
            term::Computation::App(m, v) => {
                let (mm, tm) = m.infer(ctx)?;
                let (mv, tv) = v.infer(ctx)?;
                let c = r#type::Computation::Var(r#type::Computation::mk_fresh_name());
                let mut constraints = Constraints {
                    value: Vec::new(),
                    computation: vec![(
                        r#type::Computation::Function(Box::new(tv), Box::new(c.clone())),
                        tm,
                    )],
                };
                constraints.extend(Constraints::from_map(mm));
                constraints.extend(Constraints::from_map(mv));
                let map = constraints.unify()?;
                Ok((map, c))
            }
            term::Computation::PatternMatch(v, (x, a), (y, b), m) => {
                let (mv, tv) = v.infer(ctx)?;
                ctx.push(x, a.clone());
                ctx.push(y, b.clone());
                let (mm, tm) = m.infer(ctx)?;
                let mut constraints = Constraints {
                    value: vec![(
                        r#type::Value::Pair(Box::new(a.clone()), Box::new(b.clone())),
                        tv,
                    )],
                    computation: Vec::new(),
                };
                constraints.extend(Constraints::from_map(mv));
                constraints.extend(Constraints::from_map(mm));
                let map = constraints.unify()?;
                Ok((map, tm))
            }
            term::Computation::Case(v, (x, a), m, (y, b), n) => {
                let (mv, tv) = v.infer(ctx)?;
                let ctx_m = &mut ctx.clone();
                let ctx_n = ctx;
                ctx_m.push(x, a.clone());
                ctx_n.push(y, b.clone());
                let (mm, tm) = m.infer(ctx_m)?;
                let (mn, tn) = n.infer(ctx_n)?;
                let mut constraints = Constraints {
                    value: vec![(
                        r#type::Value::Sum(Box::new(a.clone()), Box::new(b.clone())),
                        tv,
                    )],
                    computation: vec![(tm.clone(), tn)],
                };
                constraints.extend(Constraints::from_map(mv));
                constraints.extend(Constraints::from_map(mm));
                constraints.extend(Constraints::from_map(mn));
                let map = constraints.unify()?;
                Ok((map, tm))
            }
            term::Computation::Force(v) => {
                let (mv, tv) = v.infer(ctx)?;
                let c = r#type::Computation::Var(r#type::Computation::mk_fresh_name());
                let mut constraints = Constraints {
                    value: vec![(r#type::Value::U(Box::new(c.clone())), tv)],
                    computation: Vec::new(),
                };
                constraints.extend(Constraints::from_map(mv));
                let map = constraints.unify()?;
                Ok((map, c))
            }
            term::Computation::Fix(x, m, c) => {
                ctx.push(x, r#type::Value::U(Box::new(c.clone())));
                let (mm, tm) = m.infer(ctx)?;
                let mut constraints = Constraints {
                    value: Vec::new(),
                    computation: vec![(c.clone(), tm)],
                };
                constraints.extend(Constraints::from_map(mm));
                let map = constraints.unify()?;
                Ok((map, c.clone()))
            }
            term::Computation::Explode(v, c) => {
                let (mv, tv) = v.infer(ctx)?;
                let mut constraints = Constraints {
                    value: vec![(r#type::Value::Empty, tv)],
                    computation: Vec::new(),
                };
                constraints.extend(Constraints::from_map(mv));
                let map = constraints.unify()?;
                Ok((map, c.clone()))
            }
            term::Computation::Fail => Ok((
                r#type::Map::new(),
                r#type::Computation::Function(
                    Box::new(r#type::Value::Unit),
                    Box::new(r#type::Computation::F(Box::new(r#type::Value::Empty))),
                ),
            )),
            term::Computation::Add => Ok((
                r#type::Map::new(),
                r#type::Computation::Function(
                    Box::new(r#type::Value::Int),
                    Box::new(r#type::Computation::Function(
                        Box::new(r#type::Value::Int),
                        Box::new(r#type::Computation::F(Box::new(r#type::Value::Int))),
                    )),
                ),
            )),
            term::Computation::Leq => Ok((
                r#type::Map::new(),
                r#type::Computation::Function(
                    Box::new(r#type::Value::Int),
                    Box::new(r#type::Computation::Function(
                        Box::new(r#type::Value::Int),
                        Box::new(r#type::Computation::F(Box::new(r#type::Value::Sum(
                            Box::new(r#type::Value::Unit),
                            Box::new(r#type::Value::Unit),
                        )))),
                    )),
                ),
            )),
            term::Computation::NDInt => Ok((
                r#type::Map::new(),
                r#type::Computation::F(Box::new(r#type::Value::Int)),
            )),
        }
    }
}

#[test]
fn test() {
    let mut ctx = Context::new();
    let (_, ty) = term::Computation::Add.infer(&mut ctx).unwrap();
    assert_eq!(format!("{}", ty), "int -> int -> F int");
    let (_, ty) = term::Computation::Fail.infer(&mut ctx).unwrap();
    assert_eq!(format!("{}", ty), "unit -> F empty");
}
