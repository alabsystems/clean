#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0

"""
arXiv LaTeX theorem/definition/proof extractor for Mathverse Engine pilot.

Extracts structured mathematical results from LaTeX source files,
handling standard amsthm environments and common custom variants.
Outputs JSON for downstream formalization pipeline.
"""

import json
import os
import re
import sys
import tarfile
from dataclasses import asdict, dataclass, field
from pathlib import Path


# ---------------------------------------------------------------------------
# Types
# ---------------------------------------------------------------------------

@dataclass
class ExtractedDefinition:
    """A mathematical definition extracted from a paper."""
    label: str  # e.g., "Definition 2.1"
    kind: str   # "definition", "notation", "convention"
    latex: str
    ref_label: str = ""  # \label{...} value
    dependencies: list = field(default_factory=list)  # referenced labels


@dataclass
class ExtractedTheorem:
    """A mathematical result extracted from a paper."""
    label: str  # e.g., "Theorem 1.3"
    kind: str   # "theorem", "lemma", "proposition", "corollary", "conjecture", "claim"
    statement_latex: str
    proof_latex: str = ""
    ref_label: str = ""
    dependencies: list = field(default_factory=list)


@dataclass
class PaperExtraction:
    """Complete extraction result for one paper."""
    paper_id: str
    title: str = ""
    authors: str = ""
    abstract_latex: str = ""
    macro_definitions: dict = field(default_factory=dict)
    custom_environments: dict = field(default_factory=dict)
    definitions: list = field(default_factory=list)
    theorems: list = field(default_factory=list)
    # Quality metrics
    num_environments_found: int = 0
    num_proofs_found: int = 0
    extraction_warnings: list = field(default_factory=list)


# ---------------------------------------------------------------------------
# LaTeX parsing
# ---------------------------------------------------------------------------

# Standard amsthm-like environments
THEOREM_ENVS = {
    "theorem", "lemma", "proposition", "corollary", "conjecture",
    "claim", "fact", "observation",
}

DEFINITION_ENVS = {
    "definition", "notation", "convention", "example", "remark",
    "assumption", "hypothesis", "axiom",
}

PROOF_ENV = "proof"

# Regex for \newtheorem declarations (to discover custom environments)
RE_NEWTHEOREM = re.compile(
    r'\\newtheorem\{(\w+)\}(?:\[(\w+)\])?\{([^}]+)\}'
)

# Regex for \newtheorem* (unnumbered)
RE_NEWTHEOREM_STAR = re.compile(
    r'\\newtheorem\*\{(\w+)\}\{([^}]+)\}'
)

# Regex for custom \newvtheorem style macros
RE_CUSTOM_THEOREM = re.compile(
    r'\\(?:newv|newcustom)(?:theorem|lemma|claim|remark|proposition)\{(\w+)\}\{([^}]+)\}'
)

# Regex to extract \label{...}
RE_LABEL = re.compile(r'\\label\{([^}]+)\}')

# Regex to extract references (\ref, \eqref, \cref)
RE_REF = re.compile(r'\\(?:ref|eqref|cref|Cref|autoref)\{([^}]+)\}')

# Regex for macro definitions
RE_NEWCOMMAND = re.compile(
    r'\\(?:newcommand|renewcommand|DeclareMathOperator)\*?\{?\\(\w+)\}?'
    r'(?:\[(\d+)\])?\{([^{}]*(?:\{[^{}]*\}[^{}]*)*)\}'
)


def find_custom_environments(latex: str) -> dict:
    """Discover custom theorem-like environments from preamble."""
    envs = {}
    for m in RE_NEWTHEOREM.finditer(latex):
        env_name = m.group(1)
        display_name = m.group(3).lower()
        if any(k in display_name for k in ("theorem", "lemma", "proposition",
               "corollary", "conjecture", "claim", "fact")):
            envs[env_name] = "theorem"
        elif any(k in display_name for k in ("definition", "notation",
                 "example", "remark", "convention", "assumption")):
            envs[env_name] = "definition"
    for m in RE_NEWTHEOREM_STAR.finditer(latex):
        env_name = m.group(1)
        display_name = m.group(2).lower()
        if any(k in display_name for k in ("theorem", "lemma", "proposition",
               "corollary", "conjecture", "claim")):
            envs[env_name] = "theorem"
        elif any(k in display_name for k in ("definition", "notation",
                 "example", "remark")):
            envs[env_name] = "definition"
    for m in RE_CUSTOM_THEOREM.finditer(latex):
        env_name = m.group(1)
        display_name = m.group(2).lower()
        if any(k in display_name for k in ("theorem", "lemma", "proposition",
               "corollary", "conjecture", "claim")):
            envs[env_name] = "theorem"
        elif any(k in display_name for k in ("definition", "notation",
                 "example", "remark")):
            envs[env_name] = "definition"
    return envs


def extract_macros(latex: str) -> dict:
    """Extract user-defined macros from preamble."""
    macros = {}
    for m in RE_NEWCOMMAND.finditer(latex):
        name = m.group(1)
        nargs = int(m.group(2)) if m.group(2) else 0
        body = m.group(3)
        macros[name] = {"nargs": nargs, "body": body}
    return macros


def extract_environment(latex: str, env_name: str, start_pos: int = 0):
    """Extract the next occurrence of \\begin{env_name}...\\end{env_name}.

    Returns (content, label, end_pos) or None if not found.
    Handles nested environments of the same name.
    """
    begin_tag = f"\\begin{{{env_name}}}"
    end_tag = f"\\end{{{env_name}}}"

    idx = latex.find(begin_tag, start_pos)
    if idx == -1:
        return None

    content_start = idx + len(begin_tag)

    # Handle nesting
    depth = 1
    pos = content_start
    while depth > 0 and pos < len(latex):
        next_begin = latex.find(begin_tag, pos)
        next_end = latex.find(end_tag, pos)
        if next_end == -1:
            break
        if next_begin != -1 and next_begin < next_end:
            depth += 1
            pos = next_begin + len(begin_tag)
        else:
            depth -= 1
            if depth == 0:
                content = latex[content_start:next_end].strip()
                end_pos = next_end + len(end_tag)
                # Extract label if present
                label_match = RE_LABEL.search(content)
                ref_label = label_match.group(1) if label_match else ""
                # Extract references
                refs = RE_REF.findall(content)
                return content, ref_label, refs, end_pos
            pos = next_end + len(end_tag)

    return None


def find_proof_for(latex: str, theorem_end_pos: int) -> str:
    """Find the proof that follows a theorem statement.

    Looks for \\begin{proof} within 500 chars after the theorem ends.
    """
    search_region = latex[theorem_end_pos:theorem_end_pos + 500]
    result = extract_environment(latex, "proof", theorem_end_pos)
    if result is None:
        return ""
    content, _, _, _ = result
    # Only accept if it starts within 500 chars
    proof_start = latex.find("\\begin{proof}", theorem_end_pos)
    if proof_start != -1 and proof_start - theorem_end_pos < 500:
        return content
    return ""


def extract_abstract(latex: str) -> str:
    """Extract the abstract."""
    result = extract_environment(latex, "abstract")
    if result:
        return result[0]
    # Try \begin{abstract} ... \end{abstract} or \abstract{...}
    m = re.search(r'\\abstract\{([^{}]*(?:\{[^{}]*\}[^{}]*)*)\}', latex)
    if m:
        return m.group(1)
    return ""


def extract_paper(paper_id: str, latex: str) -> PaperExtraction:
    """Extract all structured math from a LaTeX document."""
    result = PaperExtraction(paper_id=paper_id)

    # Extract title
    title_m = re.search(r'\\title(?:\[.*?\])?\{([^{}]*(?:\{[^{}]*\}[^{}]*)*)\}', latex)
    if title_m:
        result.title = title_m.group(1).strip()

    # Extract authors
    author_m = re.search(r'\\author\{([^{}]*(?:\{[^{}]*\}[^{}]*)*)\}', latex)
    if author_m:
        result.authors = author_m.group(1).strip()

    # Extract abstract
    result.abstract_latex = extract_abstract(latex)

    # Extract macros
    result.macro_definitions = extract_macros(latex)

    # Discover custom environments
    custom_envs = find_custom_environments(latex)
    result.custom_environments = custom_envs

    # Build complete set of environments to search
    all_theorem_envs = set(THEOREM_ENVS)
    all_definition_envs = set(DEFINITION_ENVS)
    for env_name, env_type in custom_envs.items():
        if env_type == "theorem":
            all_theorem_envs.add(env_name)
        else:
            all_definition_envs.add(env_name)

    # Extract definitions (definitions first — they're the dependency base)
    def_counter = 0
    for env_name in sorted(all_definition_envs):
        pos = 0
        while True:
            result_env = extract_environment(latex, env_name, pos)
            if result_env is None:
                break
            content, ref_label, refs, end_pos = result_env
            def_counter += 1
            result.definitions.append(ExtractedDefinition(
                label=f"{env_name.capitalize()} {def_counter}",
                kind=env_name,
                latex=content,
                ref_label=ref_label,
                dependencies=refs,
            ))
            result.num_environments_found += 1
            pos = end_pos

    # Extract theorems + their proofs
    thm_counter = 0
    for env_name in sorted(all_theorem_envs):
        pos = 0
        while True:
            result_env = extract_environment(latex, env_name, pos)
            if result_env is None:
                break
            content, ref_label, refs, end_pos = result_env
            thm_counter += 1

            # Look for associated proof
            proof_content = find_proof_for(latex, end_pos)
            if proof_content:
                result.num_proofs_found += 1

            result.theorems.append(ExtractedTheorem(
                label=f"{env_name.capitalize()} {thm_counter}",
                kind=env_name,
                statement_latex=content,
                proof_latex=proof_content,
                ref_label=ref_label,
                dependencies=refs,
            ))
            result.num_environments_found += 1
            pos = end_pos

    return result


# ---------------------------------------------------------------------------
# File handling
# ---------------------------------------------------------------------------

def find_main_tex(directory: str) -> str:
    """Find the main .tex file in a directory.

    Heuristic: look for \\documentclass, prefer files with \\begin{document}.
    """
    tex_files = list(Path(directory).glob("*.tex"))
    if not tex_files:
        return ""

    if len(tex_files) == 1:
        return str(tex_files[0])

    # Score each file
    best_score = -1
    best_file = str(tex_files[0])
    for f in tex_files:
        content = f.read_text(errors="replace")
        score = 0
        if "\\documentclass" in content:
            score += 10
        if "\\begin{document}" in content:
            score += 10
        if "\\maketitle" in content:
            score += 5
        if "main" in f.stem.lower():
            score += 3
        if score > best_score:
            best_score = score
            best_file = str(f)

    return best_file


def extract_from_tarball(paper_id: str, tar_path: str, work_dir: str) -> PaperExtraction:
    """Extract math from a tar.gz arXiv source package."""
    extract_dir = os.path.join(work_dir, paper_id.replace("/", "_"))
    os.makedirs(extract_dir, exist_ok=True)

    try:
        with tarfile.open(tar_path, "r:gz") as tf:
            tf.extractall(extract_dir)
    except (tarfile.TarError, EOFError) as e:
        result = PaperExtraction(paper_id=paper_id)
        result.extraction_warnings.append(f"Failed to extract tar: {e}")
        return result

    main_tex = find_main_tex(extract_dir)
    if not main_tex:
        result = PaperExtraction(paper_id=paper_id)
        result.extraction_warnings.append("No .tex file found")
        return result

    latex = Path(main_tex).read_text(errors="replace")

    # Handle \input{} includes
    def resolve_inputs(text: str, base_dir: str, depth: int = 0) -> str:
        if depth > 5:
            return text

        def replace_input(m):
            fname = m.group(1)
            if not fname.endswith(".tex"):
                fname += ".tex"
            fpath = os.path.join(base_dir, fname)
            if os.path.exists(fpath):
                included = Path(fpath).read_text(errors="replace")
                return resolve_inputs(included, os.path.dirname(fpath), depth + 1)
            return m.group(0)

        text = re.sub(r'\\input\{([^}]+)\}', replace_input, text)
        return text

    latex = resolve_inputs(latex, os.path.dirname(main_tex))

    return extract_paper(paper_id, latex)


# ---------------------------------------------------------------------------
# Batch processing
# ---------------------------------------------------------------------------

def process_pilot(papers_dir: str, output_dir: str) -> dict:
    """Process all pilot papers and output extraction results."""
    os.makedirs(output_dir, exist_ok=True)
    work_dir = os.path.join(output_dir, "_work")
    os.makedirs(work_dir, exist_ok=True)

    tar_files = sorted(Path(papers_dir).glob("*.tar.gz"))
    if not tar_files:
        print(f"No .tar.gz files found in {papers_dir}")
        return {}

    results = []
    totals = {
        "papers": 0,
        "papers_with_theorems": 0,
        "total_definitions": 0,
        "total_theorems": 0,
        "total_proofs": 0,
        "total_custom_envs": 0,
        "warnings": 0,
    }

    for tar_path in tar_files:
        paper_id = tar_path.stem.replace(".tar", "")
        print(f"  Extracting: {paper_id} ... ", end="", flush=True)

        extraction = extract_from_tarball(paper_id, str(tar_path), work_dir)

        totals["papers"] += 1
        totals["total_definitions"] += len(extraction.definitions)
        totals["total_theorems"] += len(extraction.theorems)
        totals["total_proofs"] += extraction.num_proofs_found
        totals["total_custom_envs"] += len(extraction.custom_environments)
        totals["warnings"] += len(extraction.extraction_warnings)
        if extraction.theorems:
            totals["papers_with_theorems"] += 1

        print(f"{len(extraction.definitions)} defs, {len(extraction.theorems)} thms, "
              f"{extraction.num_proofs_found} proofs"
              + (f" [{', '.join(extraction.extraction_warnings)}]"
                 if extraction.extraction_warnings else ""))

        # Save individual result
        out_path = os.path.join(output_dir, f"{paper_id}.json")
        with open(out_path, "w") as f:
            json.dump(asdict(extraction), f, indent=2)

        results.append(asdict(extraction))

    # Save summary
    summary = {
        "totals": totals,
        "per_paper": [{
            "paper_id": r["paper_id"],
            "title": r["title"][:100],
            "definitions": len(r["definitions"]),
            "theorems": len(r["theorems"]),
            "proofs": r["num_proofs_found"],
            "custom_envs": len(r["custom_environments"]),
            "warnings": len(r["extraction_warnings"]),
        } for r in results],
    }

    summary_path = os.path.join(output_dir, "_summary.json")
    with open(summary_path, "w") as f:
        json.dump(summary, f, indent=2)

    return totals


def main():
    if len(sys.argv) < 2:
        print("Usage: python3 arxiv_extract.py <papers_dir> [output_dir]")
        print("  papers_dir: directory containing .tar.gz arXiv source files")
        print("  output_dir: directory for extraction output (default: data/arxiv/extracted)")
        sys.exit(1)

    papers_dir = sys.argv[1]
    output_dir = sys.argv[2] if len(sys.argv) > 2 else "data/arxiv/extracted"

    print(f"arXiv Theorem Extractor — Mathverse Engine Pilot")
    print(f"  Input:  {papers_dir}")
    print(f"  Output: {output_dir}")
    print()

    totals = process_pilot(papers_dir, output_dir)

    print()
    print("=" * 60)
    print(f"PILOT EXTRACTION SUMMARY")
    print(f"=" * 60)
    for k, v in totals.items():
        print(f"  {k:30s}: {v}")
    if totals.get("papers", 0) > 0:
        print(f"  {'avg_theorems_per_paper':30s}: {totals['total_theorems']/totals['papers']:.1f}")
        print(f"  {'avg_definitions_per_paper':30s}: {totals['total_definitions']/totals['papers']:.1f}")
        print(f"  {'proof_coverage':30s}: {totals['total_proofs']/max(1,totals['total_theorems'])*100:.1f}%")
        print(f"  {'papers_with_theorems_pct':30s}: {totals['papers_with_theorems']/totals['papers']*100:.1f}%")


if __name__ == "__main__":
    main()
