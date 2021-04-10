use crate::lambda::term::Term;
use nom::{
    branch::alt, bytes::complete::tag, character::complete::*, combinator::*, multi::*,
    sequence::*, IResult,
};
use num_bigint::BigInt;
use num_traits::Num;

fn ident(s: &str) -> IResult<&str, String> {
    let reserved = [
        "with", "in", "match", "fun", "case", "of", "inl", "inr", "fail", "let", "rec",
    ];
    let (s, id) = verify(
        recognize(nom::sequence::pair(
            alt((alpha1, tag("_"))),
            many0(alt((alphanumeric1, tag("_")))),
        )),
        |id: &str| !reserved.contains(&id),
    )(s)?;
    Ok((s, id.to_string()))
}

fn variable(s: &str) -> IResult<&str, Term> {
    let (s, id) = ident(s)?;
    Ok((s, Term::Var(id)))
}

fn abstraction(s: &str) -> IResult<&str, Term> {
    let (s, _) = tag("fun")(s)?;
    let (s, _) = multispace1(s)?;
    let (s, v) = nom::multi::separated_list1(multispace1, ident)(s)?;
    let (s, _) = multispace0(s)?;
    let (s, _) = tag("->")(s)?;
    let (s, _) = multispace0(s)?;
    let (s, mut t) = term(s)?;
    for id in v.into_iter().rev() {
        t = Term::Lambda(id, Box::new(t));
    }
    Ok((s, t))
}

fn parenthesis(s: &str) -> IResult<&str, Term> {
    let (s, _) = char('(')(s)?;
    let (s, t) = term(s)?;
    let (s, _) = char(')')(s)?;
    Ok((s, t))
}

fn unit(s: &str) -> IResult<&str, Term> {
    let (s, _) = tag("()")(s)?;
    Ok((s, Term::Unit))
}

fn pair(s: &str) -> IResult<&str, Term> {
    // let (s, v) = nom::multi::separated_list1(char(','), term)(s)?;
    let (s, _) = char('(')(s)?;
    let (s, t1) = term(s)?;
    let (s, _) = char(',')(s)?;
    let (s, t2) = term(s)?;
    let (s, _) = char(')')(s)?;
    Ok((s, Term::Pair(Box::new(t1), Box::new(t2))))
}

fn inl(s: &str) -> IResult<&str, Term> {
    let (s, _) = tag("inl")(s)?;
    let (s, t) = term(s)?;
    Ok((s, Term::Inl(Box::new(t))))
}

fn inr(s: &str) -> IResult<&str, Term> {
    let (s, _) = tag("inr")(s)?;
    let (s, t) = term(s)?;
    Ok((s, Term::Inr(Box::new(t))))
}

fn case_pattern<'a>(t: &str, s: &'a str) -> IResult<&'a str, (String, Term)> {
    let (s, _) = tag(t)(s)?;
    let (s, _) = multispace1(s)?;
    let (s, id) = ident(s)?;
    let (s, _) = multispace0(s)?;
    let (s, _) = tag("->")(s)?;
    let (s, _) = multispace0(s)?;
    let (s, t) = term(s)?;
    Ok((s, (id, t)))
}

fn inr_inl(s: &str) -> IResult<&str, (String, Term, String, Term)> {
    let (s, (idr, tr)) = case_pattern("inr", s)?;
    let (s, _) = multispace0(s)?;
    let (s, _) = char('|')(s)?;
    let (s, _) = multispace0(s)?;
    let (s, (idl, tl)) = case_pattern("inl", s)?;
    Ok((s, (idl, tl, idr, tr)))
}

fn inl_inr(s: &str) -> IResult<&str, (String, Term, String, Term)> {
    let (s, (idl, tl)) = case_pattern("inl", s)?;
    let (s, _) = multispace0(s)?;
    let (s, _) = char('|')(s)?;
    let (s, _) = multispace0(s)?;
    let (s, (idr, tr)) = case_pattern("inr", s)?;
    Ok((s, (idl, tl, idr, tr)))
}

fn case(s: &str) -> IResult<&str, Term> {
    let (s, _) = tag("case")(s)?;
    let (s, _) = multispace1(s)?;
    let (s, t) = term(s)?;
    let (s, _) = multispace0(s)?;
    let (s, _) = tag("of")(s)?;
    let (s, _) = multispace1(s)?;
    let (s, (idl, tl, idr, tr)) = alt((inr_inl, inl_inr))(s)?;
    Ok((
        s,
        Term::Case(Box::new(t), idl, Box::new(tl), idr, Box::new(tr)),
    ))
}

fn pattern_match(s: &str) -> IResult<&str, Term> {
    let (s, _) = tag("match")(s)?;
    let (s, _) = multispace1(s)?;
    let (s, v) = term(s)?;
    let (s, _) = multispace0(s)?;
    let (s, _) = tag("with")(s)?;
    let (s, _) = multispace0(s)?;
    let (s, _) = char('(')(s)?;
    let (s, _) = multispace0(s)?;
    let (s, x) = ident(s)?;
    let (s, _) = multispace0(s)?;
    let (s, _) = char(',')(s)?;
    let (s, _) = multispace0(s)?;
    let (s, y) = ident(s)?;
    let (s, _) = multispace0(s)?;
    let (s, _) = char(')')(s)?;
    let (s, _) = multispace0(s)?;
    let (s, _) = tag("->")(s)?;
    let (s, _) = multispace0(s)?;
    let (s, t) = term(s)?;
    Ok((s, Term::PatternMatch(Box::new(v), x, y, Box::new(t))))
}

fn integer(s: &str) -> IResult<&str, Term> {
    let (s, i) = map_res(
        recognize(nom::sequence::pair(many_m_n(0, 1, tag("-")), digit1)),
        |i| BigInt::from_str_radix(i, 10),
    )(s)?;
    Ok((s, Term::Int(i)))
}

fn fail(s: &str) -> IResult<&str, Term> {
    let (s, _) = tag("fail")(s)?;
    Ok((
        s,
        Term::Explode(Box::new(Term::App(
            Box::new(Term::Fail),
            Box::new(Term::Unit),
        ))),
    ))
}

fn add(s: &str) -> IResult<&str, Term> {
    let (s, _) = tag("(+)")(s)?;
    Ok((s, Term::Add))
}

fn leq(s: &str) -> IResult<&str, Term> {
    let (s, _) = tag("(<=)")(s)?;
    Ok((s, Term::Leq))
}

fn let_rec(s: &str) -> IResult<&str, Term> {
    let (s, _) = tag("let")(s)?;
    let (s, _) = multispace1(s)?;
    let (s, _) = tag("rec")(s)?;
    let (s, _) = multispace1(s)?;
    let (s, ids) = nom::multi::separated_list1(multispace1, ident)(s)?;
    let (s, _) = multispace0(s)?;
    let (s, _) = tag("=")(s)?;
    let (s, _) = multispace0(s)?;
    let (s, mut m) = term(s)?;
    let (s, _) = multispace0(s)?;
    let (s, _) = tag("in")(s)?;
    let (s, _) = multispace1(s)?;
    let (s, n) = term(s)?;
    let mut ids: Vec<String> = ids.into_iter().rev().collect();
    let f = ids.pop().unwrap();
    for x in ids.into_iter() {
        m = Term::Lambda(x, Box::new(m));
    }
    Ok((
        s,
        Term::App(
            Box::new(Term::Lambda(f.clone(), Box::new(n))),
            Box::new(Term::Fix(f, Box::new(m))),
        ),
    ))
}

fn nondet_int(s: &str) -> IResult<&str, Term> {
    let (s, _) = tag("?")(s)?;
    Ok((s, Term::NDInt))
}

pub fn term(s: &str) -> IResult<&str, Term> {
    let (s, v) = delimited(
        multispace0,
        nom::multi::separated_list1(
            multispace1,
            alt((
                unit,
                parenthesis,
                pair,
                inl,
                inr,
                abstraction,
                case,
                pattern_match,
                let_rec,
                integer,
                fail,
                add,
                leq,
                nondet_int,
                variable,
            )),
        ),
        multispace0,
    )(s)?;
    let mut iter = v.into_iter();
    let mut r = iter.next().unwrap();
    for t in iter {
        r = Term::App(Box::new(r), Box::new(t));
    }
    Ok((s, r))
}
