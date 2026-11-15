//! Iterate the bounded advice DAG without expanding shared expression trees.
use super::*;
impl Tables {
    pub(super) fn dependencies(
        &self,
        index: u64,
        out: &mut HashSet<Name>,
        string_view: bool,
    ) -> Result<(), Refusal> {
        let mut seen = HashSet::new();
        let mut todo = vec![index];
        while let Some(i) = todo.pop() {
            if !seen.insert(i) {
                continue;
            }
            let (kind, data, _, _) = self.expr_entry(i)?;
            match kind.as_str() {
                "const" => {
                    out.insert(self.name(nat(field(data, "name")?)?)?);
                }
                "proj" => {
                    out.insert(self.name(nat(field(data, "typeName")?)?)?);
                }
                "natVal" => {
                    out.insert(Name::from_dotted("Nat"));
                }
                "strVal" => {
                    out.insert(Name::from_dotted("String"));
                    if string_view {
                        out.insert(Name::from_dotted("String.ofList"));
                        out.insert(Name::from_dotted("Char.ofNat"));
                    }
                }
                _ => {}
            }
            todo.extend(self.expr_children(kind, data)?);
        }
        Ok(())
    }
}
