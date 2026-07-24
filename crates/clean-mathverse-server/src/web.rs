//! Minimal server-rendered web UI (`/` and `/decl/{name}`).
//!
//! Presentation only — no kernel/corpus mutation. Hand-rolled HTML keeps the
//! dependency surface (and blast radius) tiny.

use axum::extract::{Path, Query, State};
use axum::response::Html;
use axum::routing::get;
use axum::Router;
use serde::Deserialize;

use crate::corpus::{DeclDetail, SearchHit};
use crate::stats::CorpusStats;
use crate::AppState;

pub fn routes() -> Router<AppState> {
    Router::new()
        .route("/", get(index))
        .route("/decl/{name}", get(decl_page))
}

#[derive(Deserialize)]
struct IndexQuery {
    q: Option<String>,
}

async fn index(State(app): State<AppState>, Query(p): Query<IndexQuery>) -> Html<String> {
    let corpus = &app.corpus;
    let stats = corpus.stats();
    let mut body = String::new();

    body.push_str(&format!(
        "<h1>Mathverse</h1><p class=\"sub\">A package manager for verified mathematics — \
         generation <code>{}</code></p>",
        esc(corpus.generation())
    ));

    body.push_str(
        "<div class=\"banner\">This MVP serves <b>stored trust labels</b> faithfully and does \
         <b>not</b> re-verify proofs. <code>KernelVerified</code> is the only re-earned badge; \
         everything else is import/source confidence. See <a href=\"/v1/trust\">/v1/trust</a>.</div>",
    );

    body.push_str(&stats_cards(stats));

    let q = p.q.unwrap_or_default();
    body.push_str(&format!(
        "<form method=\"get\" action=\"/\" class=\"search\">\
         <input type=\"text\" name=\"q\" value=\"{}\" placeholder=\"search declarations by name…\" autofocus>\
         <button type=\"submit\">Search</button></form>",
        esc(&q)
    ));

    if !q.trim().is_empty() {
        let hits = corpus.search(&q, 50);
        body.push_str(&format!(
            "<h2>{} result{} for <code>{}</code></h2>",
            hits.len(),
            if hits.len() == 1 { "" } else { "s" },
            esc(&q)
        ));
        body.push_str(&results_table(&hits));
    }

    body.push_str(&format!(
        "<p class=\"foot\"><a href=\"/v1/stats\">JSON stats</a> · \
         <a href=\"/v1/trust\">trust statement</a> · \
         <a href=\"/v1/foundational-axioms\">foundational axioms</a> · \
         {} declarations across {} shard(s)</p>",
        stats.total_declarations, stats.shards_loaded
    ));

    Html(page("Mathverse", &body))
}

async fn decl_page(State(app): State<AppState>, Path(name): Path<String>) -> Html<String> {
    match app.corpus.decl(&name) {
        Some(d) => Html(page(&d.name, &decl_body(&d))),
        None => Html(page(
            "Not found",
            &format!(
                "<h1>Not found</h1><p>No declaration named <code>{}</code>.</p>\
                 <p><a href=\"/\">← back to search</a></p>",
                esc(&name)
            ),
        )),
    }
}

fn stats_cards(s: &CorpusStats) -> String {
    let card = |label: &str, value: String, hint: &str| {
        format!(
            "<div class=\"card\"><div class=\"num\">{}</div><div class=\"label\">{}</div>\
             <div class=\"hint\">{}</div></div>",
            value,
            esc(label),
            esc(hint)
        )
    };
    format!(
        "<div class=\"cards\">{}{}{}{}</div>",
        card(
            "declarations",
            group(s.total_declarations),
            "total in this Core"
        ),
        card(
            "kernel-verified",
            group(s.kernel_verified),
            "re-earned by the Clean kernel"
        ),
        card("with proof term", group(s.with_proof_term), "carry a value"),
        card(
            "shards",
            s.shards_loaded.to_string(),
            "merged into the library"
        ),
    )
}

fn results_table(hits: &[SearchHit]) -> String {
    if hits.is_empty() {
        return "<p>No matches.</p>".to_string();
    }
    let mut t = String::from(
        "<table><thead><tr><th>name</th><th>system</th><th>trust</th><th>kind</th>\
         <th>proof</th></tr></thead><tbody>",
    );
    for h in hits {
        t.push_str(&format!(
            "<tr><td><a href=\"/decl/{}\">{}</a></td><td>{}</td>\
             <td><span class=\"trust {}\">{}</span></td><td>{}</td><td>{}</td></tr>",
            esc(&path_seg(&h.name)),
            esc(&h.name),
            esc(&h.source_system),
            trust_class(&h.trust_level),
            esc(&h.trust_level),
            esc(&h.decl_kind),
            if h.has_proof_term { "✓" } else { "—" },
        ));
    }
    t.push_str("</tbody></table>");
    t
}

fn decl_body(d: &DeclDetail) -> String {
    let mut b = String::new();
    b.push_str(&format!("<h1><code>{}</code></h1>", esc(&d.name)));
    b.push_str("<table class=\"kv\">");
    b.push_str(&row("source system", &d.source_system));
    b.push_str(&format!(
        "<tr><th>trust level</th><td><span class=\"trust {}\">{}</span></td></tr>",
        trust_class(&d.trust_level),
        esc(&d.trust_level)
    ));
    b.push_str(&row("declaration kind", &d.decl_kind));
    b.push_str(&row(
        "has proof term",
        if d.has_proof_term { "yes" } else { "no" },
    ));
    b.push_str(&row("axiom count", &d.axiom_count.to_string()));
    b.push_str(&row(
        "axioms",
        &if d.axioms.is_empty() {
            "none".to_string()
        } else {
            d.axioms.join(", ")
        },
    ));
    b.push_str(&row("dependencies", &d.dependency_count.to_string()));
    b.push_str("</table>");

    b.push_str(&format!(
        "<div class=\"banner\">{}</div>",
        esc(&d.trust_note)
    ));

    if !d.dependencies.is_empty() {
        b.push_str(&format!(
            "<h2>Dependencies{}</h2><ul class=\"deps\">",
            if d.dependencies_truncated {
                format!(" (first {})", d.dependencies.len())
            } else {
                String::new()
            }
        ));
        for dep in &d.dependencies {
            b.push_str(&format!(
                "<li><a href=\"/decl/{}\">{}</a></li>",
                esc(&path_seg(dep)),
                esc(dep)
            ));
        }
        b.push_str("</ul>");
    }
    b.push_str(
        "<p class=\"foot\"><a href=\"/\">← back to search</a> · \
                <a href=\"/v1/decl/",
    );
    b.push_str(&esc(&path_seg(&d.name)));
    b.push_str("\">JSON</a></p>");
    b
}

fn row(k: &str, v: &str) -> String {
    format!("<tr><th>{}</th><td>{}</td></tr>", esc(k), esc(v))
}

fn trust_class(level: &str) -> &'static str {
    match level {
        "KernelVerified" => "kv",
        "SourceVerified" | "Translated" => "mid",
        _ => "low",
    }
}

/// Group a number with thousands separators (e.g. 1052886 → "1,052,886").
fn group(n: u64) -> String {
    let s = n.to_string();
    let bytes = s.as_bytes();
    let mut out = String::with_capacity(s.len() + s.len() / 3);
    let first = bytes.len() % 3;
    for (i, c) in bytes.iter().enumerate() {
        if i != 0 && (i - first) % 3 == 0 && (i >= first) {
            out.push(',');
        }
        out.push(*c as char);
    }
    out
}

/// HTML-escape text content.
fn esc(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '"' => out.push_str("&quot;"),
            '\'' => out.push_str("&#39;"),
            _ => out.push(c),
        }
    }
    out
}

/// Percent-encode a single URL path segment (everything outside the unreserved
/// set). Declaration names contain `.`, `_`, `'`, unicode, etc.
fn path_seg(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for b in s.bytes() {
        let unreserved = b.is_ascii_alphanumeric() || matches!(b, b'-' | b'_' | b'.' | b'~');
        if unreserved {
            out.push(b as char);
        } else {
            out.push_str(&format!("%{b:02X}"));
        }
    }
    out
}

fn page(title: &str, body: &str) -> String {
    format!(
        "<!doctype html><html lang=\"en\"><head><meta charset=\"utf-8\">\
         <meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\
         <title>{} · Mathverse</title><style>{}</style></head><body><main>{}</main></body></html>",
        esc(title),
        CSS,
        body
    )
}

const CSS: &str = "\
:root{--bg:#0f1115;--fg:#e6e6e6;--mut:#9aa3b2;--acc:#7aa2f7;--card:#171a21;--line:#262b36}\
*{box-sizing:border-box}body{margin:0;background:var(--bg);color:var(--fg);\
font:15px/1.5 ui-sans-serif,system-ui,-apple-system,Segoe UI,Roboto,sans-serif}\
main{max-width:880px;margin:0 auto;padding:32px 20px}\
h1{font-size:1.7rem;margin:.2em 0}h2{font-size:1.2rem;margin:1.4em 0 .5em;color:var(--mut)}\
.sub{color:var(--mut);margin-top:0}a{color:var(--acc);text-decoration:none}a:hover{text-decoration:underline}\
code{background:#11141a;padding:1px 5px;border-radius:4px;font-size:.92em}\
.banner{background:#1b2030;border:1px solid var(--line);border-left:3px solid var(--acc);\
padding:10px 14px;border-radius:6px;margin:16px 0;color:var(--mut)}\
.cards{display:grid;grid-template-columns:repeat(auto-fit,minmax(150px,1fr));gap:12px;margin:18px 0}\
.card{background:var(--card);border:1px solid var(--line);border-radius:8px;padding:14px}\
.card .num{font-size:1.6rem;font-weight:700}.card .label{color:var(--fg)}\
.card .hint{color:var(--mut);font-size:.82rem}\
.search{display:flex;gap:8px;margin:18px 0}\
.search input{flex:1;padding:10px 12px;background:#11141a;border:1px solid var(--line);\
border-radius:6px;color:var(--fg);font-size:1rem}\
.search button{padding:10px 18px;background:var(--acc);color:#0b0e14;border:0;border-radius:6px;\
font-weight:600;cursor:pointer}\
table{width:100%;border-collapse:collapse;margin:10px 0}\
th,td{text-align:left;padding:7px 10px;border-bottom:1px solid var(--line);vertical-align:top}\
th{color:var(--mut);font-weight:600}table.kv th{width:170px}\
.trust{font-size:.8rem;padding:1px 7px;border-radius:10px;border:1px solid var(--line)}\
.trust.kv{color:#7ee787;border-color:#2ea04326}.trust.mid{color:#e3b341}.trust.low{color:var(--mut)}\
ul.deps{columns:2;gap:18px}ul.deps li{break-inside:avoid}\
.foot{color:var(--mut);margin-top:28px;border-top:1px solid var(--line);padding-top:12px;font-size:.9rem}\
";
