// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Keyword tag index for Mathverse Library constants.
//!
//! Provides a searchable index mapping keyword tags to constant indices,
//! supporting AND/OR queries, persistence, and bulk construction from
//! shard metadata sidecars.

use std::path::Path;

use hashbrown::HashMap;

use crate::error::{MathverseError, MathverseResult};

/// A searchable keyword index for mathverse constants.
///
/// Maintains a bidirectional mapping: tags to constant indices and
/// constant indices back to their tags. Supports AND/OR multi-tag
/// queries with O(min-bucket) intersection.
#[derive(Clone, Debug, Default)]
pub struct TagIndex {
    /// tag_name -> sorted set of constant indices.
    index: HashMap<String, Vec<u32>>,
    /// constant index -> list of tags.
    reverse: HashMap<u32, Vec<String>>,
}

impl TagIndex {
    /// Create an empty tag index.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a tag to a constant. Duplicate (constant, tag) pairs are ignored.
    pub fn add_tag(&mut self, constant_idx: u32, tag: &str) {
        let tag_lower = tag.to_lowercase();

        let indices = self.index.entry(tag_lower.clone()).or_default();
        if let Err(pos) = indices.binary_search(&constant_idx) {
            indices.insert(pos, constant_idx);
        }

        let tags = self.reverse.entry(constant_idx).or_default();
        if !tags.iter().any(|t| t == &tag_lower) {
            tags.push(tag_lower);
        }
    }

    /// Search for constants with a specific tag. Returns a sorted slice of indices.
    #[must_use]
    pub fn search_tag(&self, tag: &str) -> &[u32] {
        let tag_lower = tag.to_lowercase();
        self.index.get(&tag_lower).map_or(&[], |v| v.as_slice())
    }

    /// Search for constants matching ANY of the given tags (OR query).
    ///
    /// Returns a sorted, deduplicated list of constant indices.
    #[must_use]
    pub fn search_tags_any(&self, tags: &[&str]) -> Vec<u32> {
        let mut result = Vec::new();
        for tag in tags {
            result.extend_from_slice(self.search_tag(tag));
        }
        result.sort_unstable();
        result.dedup();
        result
    }

    /// Search for constants matching ALL of the given tags (AND query).
    ///
    /// Uses sorted intersection starting from the smallest bucket.
    #[must_use]
    pub fn search_tags_all(&self, tags: &[&str]) -> Vec<u32> {
        if tags.is_empty() {
            return Vec::new();
        }

        // Collect non-empty buckets, sorted by size (smallest first).
        let mut buckets: Vec<&[u32]> = tags.iter().map(|t| self.search_tag(t)).collect();
        buckets.sort_by_key(|b| b.len());

        // If any tag has no matches, the intersection is empty.
        if buckets.first().is_none_or(|b| b.is_empty()) {
            return Vec::new();
        }

        // Intersect progressively.
        let mut current: Vec<u32> = buckets[0].to_vec();
        for bucket in &buckets[1..] {
            current = sorted_intersect(&current, bucket);
            if current.is_empty() {
                break;
            }
        }
        current
    }

    /// Return the tags for a specific constant index.
    #[must_use]
    pub fn tags_for(&self, constant_idx: u32) -> &[String] {
        self.reverse
            .get(&constant_idx)
            .map_or(&[], |v| v.as_slice())
    }

    /// List all known tags with their counts, sorted by count descending.
    #[must_use]
    pub fn all_tags(&self) -> Vec<(&str, usize)> {
        let mut tags: Vec<(&str, usize)> = self
            .index
            .iter()
            .map(|(tag, indices)| (tag.as_str(), indices.len()))
            .collect();
        tags.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(b.0)));
        tags
    }

    /// Total number of distinct tags.
    #[must_use]
    pub fn tag_count(&self) -> usize {
        self.index.len()
    }

    /// Total number of tagged constants.
    #[must_use]
    pub fn constant_count(&self) -> usize {
        self.reverse.len()
    }

    /// Build a tag index from JSON metadata sidecar files in a directory.
    ///
    /// Each file should be named `<shard_id>.tags.json` and contain a JSON
    /// object mapping constant index (as string) to list of tag strings.
    pub fn build_from_metadata_dir(dir: &Path) -> MathverseResult<Self> {
        let mut index = Self::new();
        let entries = std::fs::read_dir(dir)?;
        for entry in entries {
            let entry = entry?;
            let path = entry.path();
            if path.extension().and_then(|e| e.to_str()) != Some("json") {
                continue;
            }
            let file_name = path.file_name().and_then(|f| f.to_str()).unwrap_or("");
            if !file_name.ends_with(".tags.json") {
                continue;
            }
            let content = std::fs::read_to_string(&path)?;
            let parsed: HashMap<String, Vec<String>> = serde_json::from_str(&content)?;
            for (idx_str, tags) in parsed {
                let idx: u32 = idx_str.parse().map_err(|_| {
                    MathverseError::Kernel(format!(
                        "invalid constant index in {file_name}: {idx_str}"
                    ))
                })?;
                for tag in &tags {
                    index.add_tag(idx, tag);
                }
            }
        }
        Ok(index)
    }

    /// Serialize the index to a JSON file for caching.
    pub fn save(&self, path: &Path) -> MathverseResult<()> {
        let serializable: HashMap<&str, &[u32]> = self
            .index
            .iter()
            .map(|(k, v)| (k.as_str(), v.as_slice()))
            .collect();
        let json = serde_json::to_string(&serializable)?;
        std::fs::write(path, json)?;
        Ok(())
    }

    /// Deserialize a tag index from a cached JSON file.
    pub fn load(path: &Path) -> MathverseResult<Self> {
        let content = std::fs::read_to_string(path)?;
        let parsed: HashMap<String, Vec<u32>> = serde_json::from_str(&content)?;
        let mut index = Self::new();
        for (tag, indices) in parsed {
            for idx in indices {
                index.add_tag(idx, &tag);
            }
        }
        Ok(index)
    }
}

/// Sorted intersection of two sorted slices.
fn sorted_intersect(a: &[u32], b: &[u32]) -> Vec<u32> {
    let mut result = Vec::new();
    let (mut i, mut j) = (0, 0);
    while i < a.len() && j < b.len() {
        match a[i].cmp(&b[j]) {
            std::cmp::Ordering::Less => i += 1,
            std::cmp::Ordering::Greater => j += 1,
            std::cmp::Ordering::Equal => {
                result.push(a[i]);
                i += 1;
                j += 1;
            }
        }
    }
    result
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tag_index_add_search() {
        let mut idx = TagIndex::new();
        idx.add_tag(0, "algebra");
        idx.add_tag(1, "algebra");
        idx.add_tag(2, "topology");
        idx.add_tag(0, "commutative");

        assert_eq!(idx.search_tag("algebra"), &[0, 1]);
        assert_eq!(idx.search_tag("topology"), &[2]);
        assert_eq!(idx.search_tag("nonexistent"), &[] as &[u32]);

        // Case insensitivity.
        idx.add_tag(3, "Algebra");
        assert_eq!(idx.search_tag("ALGEBRA"), &[0, 1, 3]);
    }

    #[test]
    fn test_tag_index_and_or() {
        let mut idx = TagIndex::new();
        idx.add_tag(0, "algebra");
        idx.add_tag(0, "commutative");
        idx.add_tag(1, "algebra");
        idx.add_tag(1, "group");
        idx.add_tag(2, "topology");
        idx.add_tag(2, "commutative");

        // OR: algebra OR topology -> {0, 1, 2}
        let or_result = idx.search_tags_any(&["algebra", "topology"]);
        assert_eq!(or_result, vec![0, 1, 2]);

        // AND: algebra AND commutative -> {0}
        let and_result = idx.search_tags_all(&["algebra", "commutative"]);
        assert_eq!(and_result, vec![0]);

        // AND: algebra AND group -> {1}
        let and_result2 = idx.search_tags_all(&["algebra", "group"]);
        assert_eq!(and_result2, vec![1]);

        // AND: algebra AND topology -> {} (no constant has both)
        let and_result3 = idx.search_tags_all(&["algebra", "topology"]);
        assert!(and_result3.is_empty());

        // Empty tags.
        assert!(idx.search_tags_all(&[]).is_empty());
        assert!(idx.search_tags_any(&[]).is_empty());
    }

    #[test]
    fn test_tag_index_all_tags() {
        let mut idx = TagIndex::new();
        idx.add_tag(0, "algebra");
        idx.add_tag(1, "algebra");
        idx.add_tag(2, "algebra");
        idx.add_tag(0, "topology");
        idx.add_tag(1, "number_theory");

        let tags = idx.all_tags();
        assert_eq!(tags.len(), 3);
        // Sorted by count descending: algebra(3), then number_theory(1), topology(1) alphabetically.
        assert_eq!(tags[0], ("algebra", 3));
        assert_eq!(tags[1], ("number_theory", 1));
        assert_eq!(tags[2], ("topology", 1));
    }

    #[test]
    fn test_tag_index_tags_for() {
        let mut idx = TagIndex::new();
        idx.add_tag(0, "algebra");
        idx.add_tag(0, "commutative");
        idx.add_tag(1, "topology");

        let tags0 = idx.tags_for(0);
        assert_eq!(tags0.len(), 2);
        assert!(tags0.contains(&"algebra".to_string()));
        assert!(tags0.contains(&"commutative".to_string()));

        assert_eq!(idx.tags_for(1), &["topology".to_string()]);
        assert!(idx.tags_for(99).is_empty());
    }

    #[test]
    fn test_tag_index_dedup() {
        let mut idx = TagIndex::new();
        idx.add_tag(0, "algebra");
        idx.add_tag(0, "algebra"); // duplicate
        idx.add_tag(0, "ALGEBRA"); // case-normalized duplicate

        assert_eq!(idx.search_tag("algebra"), &[0]);
        assert_eq!(idx.tags_for(0).len(), 1);
    }

    #[test]
    fn test_tag_index_save_load() {
        let dir = std::env::temp_dir().join("mathverse_tag_test");
        let _ = std::fs::create_dir_all(&dir);
        let path = dir.join("test_tags.json");

        let mut idx = TagIndex::new();
        idx.add_tag(0, "algebra");
        idx.add_tag(1, "algebra");
        idx.add_tag(0, "commutative");
        idx.save(&path).unwrap();

        let loaded = TagIndex::load(&path).unwrap();
        assert_eq!(loaded.search_tag("algebra"), &[0, 1]);
        assert_eq!(loaded.search_tag("commutative"), &[0]);
        assert_eq!(loaded.tags_for(0).len(), 2);

        let _ = std::fs::remove_file(&path);
        let _ = std::fs::remove_dir(&dir);
    }

    #[test]
    fn test_tag_index_counts() {
        let mut idx = TagIndex::new();
        assert_eq!(idx.tag_count(), 0);
        assert_eq!(idx.constant_count(), 0);

        idx.add_tag(0, "a");
        idx.add_tag(1, "b");
        idx.add_tag(0, "b");

        assert_eq!(idx.tag_count(), 2);
        assert_eq!(idx.constant_count(), 2);
    }

    #[test]
    fn test_sorted_intersect() {
        assert_eq!(sorted_intersect(&[1, 3, 5, 7], &[2, 3, 5, 8]), vec![3, 5]);
        assert_eq!(sorted_intersect(&[1, 2, 3], &[1, 2, 3]), vec![1, 2, 3]);
        assert!(sorted_intersect(&[1, 2], &[3, 4]).is_empty());
        assert!(sorted_intersect(&[], &[1, 2]).is_empty());
    }
}
