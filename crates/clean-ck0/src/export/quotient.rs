//! Quotient records grant no authority: compare with the four canonical
//! signatures, validate their prerequisites, then install only that primitive.
use super::signature::{app, arrow, c, checked, eq, pi, s, v, Spec};
use super::*;
use crate::validate::{Env, QuotKind};
use crate::RawLevel;

fn quotient(u: RawLevel) -> Spec {
    app(c("Quot", vec![u]), [v("α"), v("r")])
}
fn mk(u: RawLevel, a: Spec) -> Spec {
    app(c("Quot.mk", vec![u]), [v("α"), v("r"), a])
}
fn parameters(u: RawLevel, body: Spec) -> Spec {
    pi(
        "α",
        s(u),
        pi("r", arrow(v("α"), arrow(v("α"), s(RawLevel::Zero))), body),
    )
}
fn signature(kind: QuotKind) -> Spec {
    let u = RawLevel::Param(0);
    match kind {
        QuotKind::Type => parameters(u.clone(), s(u)),
        QuotKind::Mk => parameters(u.clone(), pi("a", v("α"), quotient(u))),
        QuotKind::Lift => {
            let w = RawLevel::Param(1);
            let respects = pi(
                "a",
                v("α"),
                pi(
                    "b",
                    v("α"),
                    arrow(
                        app(v("r"), [v("a"), v("b")]),
                        eq(
                            w.clone(),
                            v("β"),
                            app(v("f"), [v("a")]),
                            app(v("f"), [v("b")]),
                        ),
                    ),
                ),
            );
            let result = pi("q", quotient(u.clone()), v("β"));
            let hypothesis = pi("h", respects, result);
            let function = pi("f", arrow(v("α"), v("β")), hypothesis);
            parameters(u, pi("β", s(w), function))
        }
        QuotKind::Ind => {
            let motive_ty = arrow(quotient(u.clone()), s(RawLevel::Zero));
            let minor = pi("a", v("α"), app(v("motive"), [mk(u.clone(), v("a"))]));
            parameters(
                u.clone(),
                pi(
                    "motive",
                    motive_ty,
                    pi(
                        "minor",
                        minor,
                        pi("q", quotient(u), app(v("motive"), [v("q")])),
                    ),
                ),
            )
        }
    }
}
impl Replay {
    pub(super) fn quotient(&mut self, data: &Value, name: &Name) -> Result<(), Refusal> {
        fields(data, &["name", "levelParams", "type", "kind"])?;
        let (expected, kind, nlp) = match text(field(data, "kind")?)? {
            "type" => ("Quot", QuotKind::Type, 1),
            "ctor" => ("Quot.mk", QuotKind::Mk, 1),
            "lift" => ("Quot.lift", QuotKind::Lift, 2),
            "ind" => ("Quot.ind", QuotKind::Ind, 1),
            _ => return Err(malformed("quotient kind")),
        };
        if *name != Name::from_dotted(expected) {
            return Err(Refusal::Primitive("quotient identity".into()));
        }
        let params = self.params(data)?;
        if u32::try_from(params.len()).map_err(|_| Refusal::Limit)? != nlp {
            return Err(Refusal::Primitive("quotient universe signature".into()));
        }
        if kind != QuotKind::Type
            && self.env.quot_kind(&Name::from_dotted("Quot")) != Some(QuotKind::Type)
        {
            return Err(Refusal::Primitive("missing canonical Quot".into()));
        }
        if kind == QuotKind::Ind
            && self.env.quot_kind(&Name::from_dotted("Quot.mk")) != Some(QuotKind::Mk)
        {
            return Err(Refusal::Primitive("missing canonical Quot.mk".into()));
        }
        if kind == QuotKind::Lift && !signature::canonical_eq(&self.env)? {
            return Err(Refusal::Primitive("Quot.lift requires canonical Eq".into()));
        }
        let actual = self.term(&self.env, nat(field(data, "type")?)?, &params)?;
        crate::infer_sort(&self.env, &actual, &mut Budget::default_budget())?;
        let expected = checked(&self.env, signature(kind), nlp)?;
        if !terms::same_term(&actual, &expected) {
            return Err(Refusal::Primitive("quotient type".into()));
        }
        let candidates = self.canonical.candidate("quot", data, &self.tables)?;
        let advice = target::prepare("quot", data, &self.tables, self.env.string_literal_view())?;
        self.env = std::mem::take(&mut self.env)
            .with_const_typed(name.clone(), nlp, expected)
            .with_quot(name.clone(), nlp, kind);
        self.canonical.commit(candidates, &mut self.env);
        self.graph.extend(advice);
        Ok(())
    }
}
