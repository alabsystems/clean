//! The loaded Mathverse Core: a merged, read-only view over a directory of
//! `.mathverse` shards, plus name search, declaration lookup, and stats.
//!
//! Loading is *tolerant*: a shard that fails to parse or collides with an
//! already-loaded constant is skipped and recorded, never fatal — so an
//! incomplete or messy corpus directory still yields a coherent, serveable
//! subset (and an empty directory yields an honest empty corpus).

use std::path::{Path, PathBuf};

use clean_mathverse::library::MathverseLibrary;
use clean_mathverse::shard::ShardReader;
use clean_mathverse::trust::policy::TrustPolicy;
use serde::Serialize;

use crate::error::ServerResult;
use crate::stats::{decode_axioms, CorpusStats};

/// A single search result row.
#[derive(Debug, Clone, Serialize)]
pub struct SearchHit {
    pub name: String,
    pub source_system: String,
    pub trust_level: String,
    pub decl_kind: String,
    pub has_proof_term: bool,
}

/// Full detail for one declaration.
#[derive(Debug, Clone, Serialize)]
pub struct DeclDetail {
    pub name: String,
    pub source_system: String,
    pub trust_level: String,
    pub decl_kind: String,
    pub has_proof_term: bool,
    pub axioms: Vec<String>,
    pub axiom_count: u32,
    pub dependency_count: usize,
    /// First [`DeclDetail::DEP_LIMIT`] dependency names (the closure can be large).
    pub dependencies: Vec<String>,
    pub dependencies_truncated: bool,
    /// Honest note on what `trust_level` does and does not mean.
    pub trust_note: String,
}

impl DeclDetail {
    const DEP_LIMIT: usize = 200;
}

/// The merged, read-only corpus.
pub struct Corpus {
    library: MathverseLibrary,
    stats: CorpusStats,
    dir: PathBuf,
    generation: String,
    shards_loaded: Vec<String>,
    shards_skipped: Vec<(String, String)>,
}

impl Corpus {
    /// Scan `dir` recursively for `*.mathverse` shards, merge up to
    /// `max_shards` of them (sorted, deterministic), and compute stats.
    pub fn load(dir: &Path, max_shards: Option<usize>) -> ServerResult<Self> {
        let mut shard_paths = collect_shards(dir);
        shard_paths.sort();
        if let Some(m) = max_shards {
            shard_paths.truncate(m);
        }

        let mut library = MathverseLibrary::new(TrustPolicy::default());
        let mut loaded = Vec::new();
        let mut skipped = Vec::new();

        for path in &shard_paths {
            let rel = path.strip_prefix(dir).unwrap_or(path).display().to_string();
            match ShardReader::from_file(path) {
                Ok(reader) => match library.load_shard(&reader) {
                    Ok(_) => {
                        tracing::info!(shard = %rel, "loaded shard");
                        loaded.push(rel);
                    }
                    Err(e) => {
                        tracing::warn!(shard = %rel, error = %e, "skipped shard (merge failed)");
                        skipped.push((rel, e.to_string()));
                    }
                },
                Err(e) => {
                    tracing::warn!(shard = %rel, error = %e, "skipped shard (unreadable)");
                    skipped.push((rel, e.to_string()));
                }
            }
        }

        library.build_deps();
        let stats = CorpusStats::compute(&library, loaded.len(), skipped.len());
        let generation = dir
            .file_name()
            .map(|s| s.to_string_lossy().to_string())
            .unwrap_or_else(|| "corpus".to_string());

        tracing::info!(
            declarations = stats.total_declarations,
            shards_loaded = loaded.len(),
            shards_skipped = skipped.len(),
            kernel_verified = stats.kernel_verified,
            "corpus loaded"
        );

        Ok(Corpus {
            library,
            stats,
            dir: dir.to_path_buf(),
            generation,
            shards_loaded: loaded,
            shards_skipped: skipped,
        })
    }

    pub fn stats(&self) -> &CorpusStats {
        &self.stats
    }

    pub fn generation(&self) -> &str {
        &self.generation
    }

    pub fn dir(&self) -> &Path {
        &self.dir
    }

    pub fn shards_loaded(&self) -> &[String] {
        &self.shards_loaded
    }

    pub fn shards_skipped(&self) -> &[(String, String)] {
        &self.shards_skipped
    }

    pub fn declaration_count(&self) -> usize {
        self.library.constant_count()
    }

    /// Case-insensitive name search. Ranks exact > prefix > substring, then by
    /// shorter name. Linear scan — adequate for the MVP's mounted subset.
    pub fn search(&self, query: &str, limit: usize) -> Vec<SearchHit> {
        let q = query.trim().to_lowercase();
        if q.is_empty() {
            return Vec::new();
        }
        let n = self.library.constant_count() as u32;
        let mut ranked: Vec<(u8, usize, u32)> = Vec::new();
        for idx in 0..n {
            let Some(name) = self.library.get_name(idx) else {
                continue;
            };
            let lname = name.to_lowercase();
            let rank = if lname == q {
                0u8
            } else if lname.starts_with(&q) {
                1
            } else if lname.contains(&q) {
                2
            } else {
                continue;
            };
            ranked.push((rank, name.len(), idx));
        }
        ranked.sort_by(|a, b| a.0.cmp(&b.0).then(a.1.cmp(&b.1)));
        ranked.truncate(limit);
        ranked
            .into_iter()
            .filter_map(|(_, _, idx)| self.hit(idx))
            .collect()
    }

    fn hit(&self, idx: u32) -> Option<SearchHit> {
        let h = self.library.get_constant(idx)?;
        let name = self.library.get_name(idx)?.to_string();
        Some(SearchHit {
            name,
            source_system: source_name(h),
            trust_level: trust_name(h),
            decl_kind: kind_name(h),
            has_proof_term: h.has_value(),
        })
    }

    /// Full detail for `name`, or `None` if not present.
    pub fn decl(&self, name: &str) -> Option<DeclDetail> {
        let idx = self.library.lookup_constant_idx(name)?;
        let h = self.library.get_constant(idx)?;
        let profile = h.profile();
        let deps = self.library.deps();
        let dep_idxs = deps.get(idx as usize);
        let dependency_count = dep_idxs.map(|d| d.len()).unwrap_or(0);
        let dependencies: Vec<String> = dep_idxs
            .into_iter()
            .flatten()
            .take(DeclDetail::DEP_LIMIT)
            .filter_map(|d| self.library.get_name(*d))
            .map(|s| s.to_string())
            .collect();
        Some(DeclDetail {
            name: name.to_string(),
            source_system: source_name(h),
            trust_level: trust_name(h),
            decl_kind: kind_name(h),
            has_proof_term: h.has_value(),
            axioms: decode_axioms(profile),
            axiom_count: profile.axiom_count(),
            dependency_count,
            dependencies_truncated: dependency_count > DeclDetail::DEP_LIMIT,
            dependencies,
            trust_note: trust_note_for(h),
        })
    }
}

fn source_name(h: &clean_mathverse::types::MathverseConstantHeader) -> String {
    h.source()
        .map(|s| format!("{s:?}"))
        .unwrap_or_else(|raw| format!("Unknown({raw})"))
}

fn trust_name(h: &clean_mathverse::types::MathverseConstantHeader) -> String {
    h.confidence()
        .map(|c| format!("{c:?}"))
        .unwrap_or_else(|raw| format!("Unknown({raw})"))
}

fn kind_name(h: &clean_mathverse::types::MathverseConstantHeader) -> String {
    h.decl_kind()
        .map(|k| format!("{k:?}"))
        .unwrap_or_else(|raw| format!("Unknown({raw})"))
}

fn trust_note_for(h: &clean_mathverse::types::MathverseConstantHeader) -> String {
    match h.confidence() {
        Ok(clean_mathverse::types::ImportConfidence::KernelVerified) => {
            "Re-checked by the Clean kernel from the shard's proof term.".to_string()
        }
        _ => "Import/source confidence — NOT independently re-verified by the Clean kernel. \
              See /v1/trust."
            .to_string(),
    }
}

/// Recursively collect every `*.mathverse` file under `dir`.
fn collect_shards(dir: &Path) -> Vec<PathBuf> {
    let mut out = Vec::new();
    let mut stack = vec![dir.to_path_buf()];
    while let Some(d) = stack.pop() {
        let Ok(rd) = std::fs::read_dir(&d) else {
            continue;
        };
        for entry in rd.flatten() {
            let p = entry.path();
            if p.is_dir() {
                stack.push(p);
            } else if p.extension().and_then(|s| s.to_str()) == Some("mathverse") {
                out.push(p);
            }
        }
    }
    out
}
