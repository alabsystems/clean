use super::*;
use clean_kernel::Name;

fn document_and_names(names: Vec<(Name, &str)>) -> (Document, ElaboratedDocument) {
    let document = Document::new(
        Url::parse("file:///typed-hover.lean").unwrap(),
        1,
        String::new(),
        "lean".to_owned(),
    );
    let elaborated = ElaboratedDocument {
        errors: vec![],
        warnings: vec![],
        term_infos: Vec::new(),
        holes: vec![],
        widget_modules: vec![],
        declarations: names
            .into_iter()
            .map(|(identity, ty)| ElaboratedDecl {
                identity,
                // Deliberately identical labels: type lookup must use only Name.
                name: "same display label".to_owned(),
                type_str: ty.to_owned(),
                start: 0,
                end: 0,
            })
            .collect(),
    };
    (document, elaborated)
}

#[test]
fn hover_lookup_distinguishes_quoted_and_hierarchical_names() {
    let (document, elaborated) = document_and_names(vec![
        (Name::anon().str("A").str("B"), "nested type"),
        (Name::anon().str("A.B"), "quoted type"),
    ]);
    assert_eq!(
        CleanBackend::hover_type_of_name(&document, &elaborated, "A.B"),
        Some("nested type".to_owned())
    );
    assert_eq!(
        CleanBackend::hover_type_of_name(&document, &elaborated, "«A.B»"),
        Some("quoted type".to_owned())
    );
    for (source, ty) in [("A.B", "nested type"), ("«A.B»", "quoted type")] {
        let document = Document::new(
            Url::parse("file:///typed-hover.lean").unwrap(),
            1,
            source.to_owned(),
            "lean".to_owned(),
        );
        for (offset, _) in source.char_indices() {
            let actual =
                CleanBackend::hover_identifier_at(&document, &elaborated, source, offset).unwrap();
            assert_eq!(actual, (0, source.len(), source.to_owned(), ty.to_owned()));
        }
    }
}

#[test]
fn hover_suffix_uses_one_structural_component_not_display_tail() {
    let (document, elaborated) = document_and_names(vec![
        (Name::anon().str("A").str("B"), "nested type"),
        (Name::anon().str("A.B"), "quoted type"),
    ]);
    assert_eq!(
        CleanBackend::hover_type_of_name(&document, &elaborated, "B"),
        Some("nested type".to_owned())
    );
    assert_eq!(
        CleanBackend::hover_type_of_name(&document, &elaborated, "same display label"),
        None
    );
}

#[test]
fn hover_numeric_name_cannot_impersonate_quoted_string_numeral() {
    let (document, elaborated) = document_and_names(vec![(Name::anon().num(7), "numeric type")]);
    assert_eq!(
        CleanBackend::hover_type_of_name(&document, &elaborated, "«7»"),
        None
    );
    let (document, elaborated) = document_and_names(vec![(Name::anon().str("7"), "string type")]);
    assert_eq!(
        CleanBackend::hover_type_of_name(&document, &elaborated, "«7»"),
        Some("string type".to_owned())
    );
}
