#!/usr/bin/env python3
"""Provenance-anchor resolvability gate (audit r6 class-closer, wf_a000d04d).

THE CLASS THIS CLOSES: lanes record their worktree HEAD in a committed record,
then rebase onto main, orphaning the sha -- so the record's provenance anchor
resolves to no commit and the measurement tree is unrecoverable. Audit rounds
5 and 6 found SIX such records one instance at a time (2d023a11d, c0ea930ca,
4a39d38e0, f02de5b0f, c41d2dcf5's family, d8da4fe2); a class is closed by a
gate, not by patches.

THE INVARIANT: in the audited record set, every git-sha-shaped token either
RESOLVES to a commit in this repo or a named neighbor repo (../trust,
../trust-ir -- fetch them before believing a red: the drift class is
documented in CLAUDE.md), or carries an explicit unresolvability annotation
("resolves to no commit" / "does not resolve" within 200 chars after an
occurrence of the token, which then excuses the token file-wide), or is a
justified ALLOW entry below. A NEW dangling anchor therefore cannot land
silently.

NOT AUDITED, AND WHY (audit r7: every exclusion is named, none implied):
data/crystal_a0_a6_probe.json is a mechanical TRANSCRIPTION --
scripts/check_a0a6_probe_transcription.py re-derives it from its named
committed records and refuses disagreement, so annotating it here would
break that gate; its shas are judged at their source records. Prose docs
under docs/ are narrative, not records a gate mints from -- the materiality
bar ranks a narrative mention minor -- with two exceptions that ARE audited:
the frontend class ledger and the self-verification navigation notes, cut out
of CLAUDE.md (itself audited since r17) on 2026-09-26 with their citations.
Dropping them from the audit because they changed file would have been the
silent loss this gate forbids. The dated
reports/source-elab/srcelab-*.json are minted artifacts byte-bound by
`source_elab_gate.sh --check-artifact`; their commit anchors are judged at
data/source_elab_ratchet.json, which IS audited and carries their
annotations. The dated reports/tactic-families snapshots are superseded by
the *-latest.json each family gate re-measures at HEAD, and the binary
sha256 content pin is their durable anchor (the one round-7-adjudicated
snapshot is audited above). The wider data/crystal_*.json lane-record
archive mixes commit anchors with uncommitted-worktree BLOB fingerprints
and pins into FIVE neighbor repos (ay, ty, trust-mc, trust-vc, ny beyond
the three resolved here); auditing it needs the blob-class annotation
convention and those clones -- that widening is the enumerated next step,
not an oversight.

KNOWN LIMITS (stated, not hidden): a token needs at least one [a-f] letter
(an all-digit sha prefix is indistinguishable from a number -- ~4% of 7-char
prefixes are missed); tokens shorter than 7 hex and UPPERCASE hex spellings
are not extracted (git prints lowercase; no committed record uses either
shape -- audit r7); a sha glued to a letter (srcelab's -g<sha> filenames)
has no word boundary and is not extracted, but every such file also carries
the bare sha in armed_commit or notes, which IS checked. Tokens of 7-12 or
exactly 40 hex are extracted (audit r7 M1 -- the original {7,12} cap made a
dangling FULL 40-hex sha invisible, the most realistic shape there is);
40-hex anchors may resolve as any git object, because full-hex anchors
legitimately pin BLOBS; 64-hex sha256 content digests cannot match on word
boundaries, and the 13-39 band is excluded because in this record set it is
always a content fingerprint (cargo metadata, lean4_hash), never a commit --
a 13-39-hex COMMIT anchor would be invisible here, stated, not hidden.
"Shareable" is a PROXY, not proof of sharing (audit r10): this repo carries
566 local `origin/archive/dangling-*` bookkeeping refs under refs/remotes,
and `git tag <name> <orphan>` or a local-path remote satisfies the filter
with nothing pushed anywhere. It is a real improvement over "any ref" --
refs/lane/*, refs/claude/* and refs/stash no longer keep an orphan alive --
and it is not a guarantee; the refusal text should send an operator to `git
push`, never to the sanctioned bypass. The GLUED `-g<sha>` form IS extracted
(audit r8 M5), and the older claim that "every such file also carries the
bare sha" was measured FALSE.

A token whose LABEL sits immediately before it (`"sha256": "..."`,
`sha256:...`) is skipped as a content digest. Audit r8 made that rule
line-scoped and audit r9 measured the consequence: in records that store one
25,000-character JSON value per line, one label silenced 23 tokens on that
line, 14 of them dangling commit citations -- a suppression wearing the shape
of a fix. The window is adjacency again, and an arm pins the long-line case. A 40-hex anchor is accepted on
object EXISTENCE alone when it names a blob: finding the commit that carries
a blob is a full-history walk, so blob anchors get existence, commits get
reachability (audit r8 M6).
"""
import argparse
import os
from pathlib import Path
import re
import subprocess
import sys

AUDITED = [
    # AUDIT r17 (2026-09-14). The most-read document in the repository was the
    # one whose evidence anchors nothing re-resolved. First run: ELEVEN
    # sha-shaped citations resolving in no clone on this machine -- seven of
    # them clean-repo commits cited as the evidence for specific fixes, in a
    # non-shallow clone with 8,733 reachable commits, so squashed or rebased
    # away by whatever landed them. Every one is now annotated in this file's
    # own "Provenance of the commit citations" section, which is where a reader
    # meets them; the claims are kept and the shas are marked unrecoverable.
    "CLAUDE.md",
    # 2026-09-26: CLAUDE.md passed the 150,000-character limit Claude Code puts
    # on instruction files, and its frontend class ledger and self-verification
    # notes moved VERBATIM to these two docs -- together with the sha-shaped
    # citations this gate had been resolving in CLAUDE.md. They stay audited.
    "docs/FRONTEND_CLASS_LEDGER.md",
    "docs/SELF_VERIFICATION_NAVIGATION.md",
    "data/gate_registry.json",
    "data/source_elab_ratchet.json",
    "data/trust_verify_ratchet.json",
    "data/kernel_lint_ratchet.json",
    "data/gate_demonstrations.json",
    "data/unchecked_decl_ratchet.json",
    "data/crystal_a0_discharge.json",
    # audit r8 m3: a first-class soundness metric with its own gate leg was in
    # neither the audited set nor any named exclusion -- the exact silence this
    # gate exists to forbid
    "data/axiom_audit.json",
    # audit r7 M4: the four records round 7 adjudicated as anchor-dependent
    "data/crystal_revalidation_at_head_2026-08-27_laneREV.json",
    "data/crystal_chain_revalidation_2026-08-20_8ea683678.json",
    "reports/source-elab/universe-binder-domain-2026-08-31.json",
    "reports/tactic-families/g_simp-2026-08-28-062041.json",
]
REPOS = [".", "../trust", "../trust-ir"]


def repository_git_environment():
    """Keep user configuration, but never inherit a hook's repository identity."""
    result = subprocess.run(
        ["git", "rev-parse", "--local-env-vars"], capture_output=True,
        text=True, timeout=10)
    names = result.stdout.splitlines()
    if result.returncode != 0 or not names or any(
        re.fullmatch(r"GIT_[A-Z0-9_]+", name) is None for name in names
    ):
        raise ValueError("cannot enumerate Git repository-local environment")
    env = os.environ.copy()
    for name in names:
        env.pop(name, None)
    return env


def explicit_repository(value, option, git_env):
    """An override names an exact worktree root, not an ancestor Git discovers."""
    if not value:
        raise ValueError(f"{option} requires a nonempty Git worktree root")
    try:
        path = Path(value).resolve(strict=True)
    except (OSError, RuntimeError) as exc:
        raise ValueError(f"{option}: cannot resolve {value!r}: {exc}") from exc
    if not path.is_dir():
        raise ValueError(f"{option}: not a directory: {path}")
    result = subprocess.run(
        ["git", "-C", str(path), "rev-parse", "--show-toplevel"],
        capture_output=True, text=True, env=git_env, timeout=10)
    if result.returncode != 0 or not result.stdout.strip():
        raise ValueError(f"{option}: not a Git worktree root: {path}")
    if Path(result.stdout.strip()).resolve() != path:
        raise ValueError(f"{option}: path is inside another Git worktree: {path}")
    return str(path)


def selected_repositories(args, git_env):
    # The Clean subject, inventory, and anchor predicate are not configurable.
    # Only the locations of the two existing neighboring repositories change.
    repos = list(REPOS)
    for index, value, option in (
        (1, args.trust_repo, "--trust-repo"),
        (2, args.trust_ir_repo, "--trust-ir-repo"),
    ):
        if value is not None:
            repos[index] = explicit_repository(value, option, git_env)
    return repos


ALLOW = {
    # token: justification -- an ALLOW row is an account, not a suppression.
    "43ad0e9d2e14": "mathlib4 corpus sha (external repo; the local corpus cache is not a git clone)",
    "43ad0e9d2e144aa282f0c642a5b8427f39d23e4b": "the same mathlib4 corpus sha, full 40-hex spelling",
    # 2026-09-15: data/source_elab_ratchet.json's `corpus_measured.rev` -- the
    # mathlib4 revision `$HOME/mathlib4-pinned` sat at when the srcelab gate
    # measured it on m1-Air (f8f0a8a63). Same class as the row above: an
    # external repo's commit, not resolvable in clean, ../trust or ../trust-ir
    # by construction, and the record itself says which clone resolves it. (The
    # gate is named by role, not path: R3's loose scan reads a script path in a
    # string as an invocation.)
    "8f9d9cff6bd728b17a24e163c9402775d9e6a365":
        "mathlib4 corpus sha the srcelab gate records as corpus_measured.rev in "
        "data/source_elab_ratchet.json (external repo; resolvable only in the "
        "$HOME/mathlib4-pinned checkout that record names)",
    "383681b4b666": "file CONTENT hash quoted in registry prose ('the file there hashes ...'), not a commit anchor",
    "ad49cf1dbdcd": "file CONTENT hash quoted in registry prose, not a commit anchor",
    # AUDIT r17 (2026-09-14). A demonstration arm's mutation PAYLOAD is a string
    # written into a file to prove a gate refuses it, then restored -- never a
    # provenance claim. This one belongs to check_help_surfaces' arm "a
    # `drift_swept` sweep bound is pointed at a commit this repository does not
    # have", whose SUBJECT is exactly a dangling sha: it cannot be spelled any
    # other way and still test anything. It is accounted here rather than
    # exempted structurally, because a rule that skipped whole FIELDS of an
    # audited record is the suppression-wearing-the-shape-of-a-fix this file's
    # r8/r9 history already paid for once. Rot-checked like every ALLOW row: if
    # that arm is deleted or respelled, this row's token occurs nowhere and the
    # gate refuses it. The sibling case is the counter-example -- verdict_set's
    # "a closure member's pinned sha256 is typed over" arm had a free choice of
    # payload and now uses a non-hex one, so it needs no row at all.
    "deadbeefdeadbeefdeadbeefdeadbeefdeadbeef":
        "check_help_surfaces demonstration payload: the deliberately-dangling `drift_swept` sweep "
        "bound whose refusal that arm exists to prove (data/gate_demonstrations.json)",
    # 2026-09-30: the same class as the row above, but the payload is a REAL
    # commit in a repository this gate does not search. The dep-boundary arm
    # "an AY move lands without its consumer qualification" writes the AY
    # revision the tree pinned BEFORE the f28345ff -> 630842a8 move (8db0f0e61)
    # into data/ay_consumer_qualification.json's `ay_rev`, to prove the leg
    # refuses a qualification record that names the old AY. It resolves in the
    # sibling ../ay clone (`git -C ../ay cat-file -t` says commit), not in
    # clean, ../trust or ../trust-ir. Rot-checked like every ALLOW row.
    "f28345ff184e33551e9b9d9f509f831461dd8b24":
        "dep-boundary demonstration payload: the pre-move AY revision the "
        "consumer-qualification arm writes into ay_rev (data/gate_demonstrations.json); "
        "an AY commit, resolvable in ../ay, which this gate does not search",
}
# 7-12 hex (git's abbreviated-anchor convention in this record set) or
# exactly 40 (a full object name). Both boundaries, so a 64-hex sha256
# content digest can never match; the 13-39 band is EXCLUDED deliberately --
# in this record set that band is cargo metadata (16 hex), lean4_hash
# fingerprints (16 hex) and digest prefixes, never a commit anchor, and a
# git abbreviation only grows past 12 when a repo is far larger than these
# (KNOWN LIMITS below states this).
TOKEN = re.compile(r"\b(?:[0-9a-f]{7,12}|[0-9a-f]{40})\b")
# AUDIT r8 M5: the `-g<sha>` filename form has no left word boundary, so TOKEN
# never saw it -- and the KNOWN LIMITS claim that "every such file also carries
# the bare sha" was FALSE inside an audited record (two glued anchors with no
# bare occurrence, neither resolving). Extract the glued form as well.
GLUED = re.compile(r"-g([0-9a-f]{7,40})\b")
# The sha256 label must be ADJACENT (audit r9 M-1): a JSON key, a `sha256:`
# prefix, or `sha256 = `, within a couple of dozen characters -- never merely
# "somewhere on this line", which in these single-line JSON records is the
# whole file.
# Separators between the label and its digest: quotes, colons, equals,
# whitespace, and the ESCAPED newline+indent that these single-line JSON
# records use (`sha256\\n            <digest>`). Bounded by the 32-character
# window the caller slices, so "adjacent" stays adjacent.
SHA256_LABEL = re.compile(r"sha256(?:[\"'\s:=]|\\n)*$")


def _all_tokens(text):
    """Every sha-shaped occurrence: bare, and glued behind `-g`."""
    for m in TOKEN.finditer(text):
        yield m
    for m in GLUED.finditer(text):
        yield m
# Audit r7 M2: the excusal window must not contain ANOTHER sha-shaped token --
# without that, an annotation about sha A excused a different dangling sha B
# sitting up to 200 chars before the phrase (two standing umbrella windows
# existed in the registry itself). The tempered dot forbids it.
EXCUSE = (r"[^0-9a-f](?:(?!\b[0-9a-f]{7,64}\b)[\s\S]){0,200}?"
          r"(?:resolves? to no commit|does not resolve|resolve to no commit"
          r"|blob fingerprint of an uncommitted worktree file|not a git object)")


def _resolves(repo, tok, git_env):
    r = subprocess.run(
        ["git", "-C", repo, "rev-parse", "--verify", "--quiet", tok + "^{commit}"],
        capture_output=True, text=True, env=git_env)
    if r.returncode == 0:
        # AUDIT r8 M6: object existence is NOT resolvability. The class this
        # gate closes is a lane recording its pre-rebase HEAD; that commit
        # stays in the local object database until gc, so `rev-parse` says
        # yes on the very machine where the record was written -- the gate
        # was green at the exact moment the defect was created and went red
        # only later, elsewhere. Require reachability from a REF, which is
        # what "someone else can check this out" actually means.
        sha = r.stdout.strip()
        # AUDIT r10 M10-6: this filter landed in source_elab_gate.sh's copy of
        # the predicate and NOT here, though the r9 commit message said "in
        # BOTH" -- so the gate that owns the class still accepted a commit kept
        # alive only by refs/lane/*, refs/claude/* or refs/stash. Measured cost
        # of the filter: nil (2.08 s vs 2.11 s over the 12-file set).
        ref = subprocess.run(
            ["git", "-C", repo, "for-each-ref", "--contains", sha,
             "--count", "1", "--format", "%(refname)",
             "refs/remotes/", "refs/tags/"],
            capture_output=True, text=True, env=git_env)
        return ref.returncode == 0 and bool(ref.stdout.strip())
    if len(tok) >= 40:
        # audit r7 M1: a full 40-hex anchor may name a BLOB (a content
        # fingerprint the crystal records pin); any object type resolves it.
        # Blob REACHABILITY is not checked -- finding the commit that carries
        # a blob is a full-history walk -- so a blob anchor is accepted on
        # existence alone; stated in KNOWN LIMITS.
        r = subprocess.run(["git", "-C", repo, "cat-file", "-e", tok],
                           capture_output=True, env=git_env)
        return r.returncode == 0
    return False


def check(files, repos, allow, root=".", git_env=None, stats=None):
    """Returns a list of (token, file, context) violations; empty == green.

    `stats`, when a dict is passed, is filled with
    `{"annotated": {file: n}}` -- the number of DISTINCT sha-shaped tokens in
    each file carrying an unresolvability annotation. That set is computed
    here anyway (it is what `excused` is) and used to be discarded, which left
    the only record of its size a number typed into prose. CLAUDE.md's
    provenance section said "eleven" while enumerating thirteen, and a
    sub-heading said "Four" above six bullets; the rule this file states about
    its own arms -- "DERIVED, never a literal" -- applies to the documents it
    judges too. Returning the count makes the figure quotable from a run
    instead of from a sentence.
    """
    if git_env is None:
        git_env = repository_git_environment()
    bad = []
    cache = {}
    seen_tokens = set()
    for f in files:
        path = os.path.join(root, f)
        try:
            s = open(path, encoding="utf-8").read()
        except FileNotFoundError:
            bad.append(("<missing>", f, "audited record file does not exist"))
            continue
        excused = set()
        for m in _all_tokens(s):
            t = m.group(1) if m.re.groups else m.group(0)
            if re.search(t + EXCUSE, s, re.IGNORECASE | re.DOTALL):
                excused.add(t)
        annotated_here = set()
        for m in _all_tokens(s):
            t = m.group(1) if m.re.groups else m.group(0)
            seen_tokens.add(t)
            if not re.search(r"[a-f]", t):
                continue
            if SHA256_LABEL.search(s[max(0, m.start() - 32):m.start()]):
                # AUDIT r9 M-1: this skip must be ADJACENT to the token, not
                # anywhere on its line. The r8 widening ("anywhere earlier on
                # this line") looked like a fix and was a SUPPRESSION: these
                # records store one 25,000-character JSON value per line, so a
                # single `sha256` label 2,600 characters to the left silenced
                # 23 tokens on that line -- including 14 dangling commit
                # citations, two of them the very records this gate's own
                # docstring names as the class it exists to close. The gate
                # went red -> green by suppression and no arm noticed, because
                # every arm was a one-line fixture. The label must now sit
                # immediately before the token (a JSON key, a `sha256:`
                # prefix), and the arm below pins the long-line case.
                continue
            if t in excused:
                # Counted where the token is FILTERED, not where it is
                # matched: an all-digit id and a sha256-labelled digest are
                # not citations, and counting them would inflate the figure
                # the prose is meant to stop typing.
                annotated_here.add(t)
            if t in allow or t in excused:
                continue
            if t not in cache:
                cache[t] = any(_resolves(os.path.join(root, r) if r != "." else root, t, git_env)
                               for r in repos)
            if not cache[t]:
                ctx = s[max(0, m.start() - 40):m.start() + 50].replace("\n", " ")
                bad.append((t, f, ctx))
        if stats is not None:
            stats.setdefault("annotated", {})[f] = len(annotated_here)
    # audit r7 minor: an ALLOW row whose token no longer occurs anywhere in
    # the audited set is ROT -- a suppression outliving its subject is refused
    # so the list can only shrink with the records it excuses
    for t in allow:
        if t not in seen_tokens:
            bad.append((t, "<ALLOW>", "ALLOW row's token occurs in no audited file -- remove the stale row"))
    return bad


def selftest(git_env=None):
    """Every refusal demonstrated on every invocation (selftest-inline)."""
    import tempfile
    if git_env is None:
        git_env = repository_git_environment()
    ok = True
    n_arms = 0  # DERIVED, never a literal: a hand-written arm count is the
    # staleness class audits r7-r10 kept finding in notes and docstrings
    with tempfile.TemporaryDirectory() as d:
        def arm(tag, content, allow, expect_bad):
            nonlocal ok, n_arms
            n_arms += 1
            p = os.path.join(d, "rec.json")
            with open(p, "w", encoding="utf-8") as fh:
                fh.write(content)
            got = bool(check([os.path.relpath(p, ".")], ["."], allow))
            if got != expect_bad:
                print(f"  [RED] provenance-anchors arm {tag}: "
                      f"expected {'refusal' if expect_bad else 'green'}, got the opposite")
                ok = False
        arm("dangling-unannotated", '{"n": "measured at deadbeef1"}', {}, True)
        arm("dangling-annotated",
            '{"n": "measured at deadbeef1 [this sha resolves to no commit here]"}', {}, False)
        arm("annotated-excuses-file-wide",
            '{"a": "deadbeef1 resolves to no commit", "b": "again deadbeef1"}', {}, False)
        arm("sha256-prefix-skipped", '{"n": "pin sha256:deadbeef1234"}', {}, False)
        arm("all-digit-skipped", '{"n": "id 20260830123"}', {}, False)
        arm("allow-entry", '{"n": "corpus at deadbeef1"}',
            {"deadbeef1": "external"}, False)
        # audit r7 M1: a FULL 40-hex dangling sha must be extracted and refused
        arm("dangling-40hex", '{"n": "tree at %s"}' % ("deadbeef" * 5), {}, True)
        # audit r7 M2: an annotation about sha A must NOT excuse a DIFFERENT
        # dangling sha B sitting inside the 200-char window before the phrase
        arm("cross-token-excusal",
            '{"a": "cafebabe1 is here", "b": "deadbeef1 resolves to no commit"}',
            {"deadbeef1": "control"}, True)
        # ...while the SAME token annotated once stays excused file-wide
        arm("same-token-still-filewide",
            '{"a": "cafebabe1 resolves to no commit", "b": "again cafebabe1"}',
            {}, False)
        # audit r7 minor: an ALLOW row whose token occurs nowhere is rot
        arm("allow-rot", '{"n": "nothing here"}', {"deadbeef1": "stale"}, True)
        # audit r8 M5: the glued `-g<sha>` filename form is extracted too
        arm("glued-dangling", '{"n": "see srcelab-2026-01-01-gdeadbeef1.json"}',
            {}, True)
        # audit r8 m2: a token LABELLED sha256 anywhere earlier on its line is
        # a content digest, skipped -- and a same-shaped token on a line with
        # no such label is NOT skipped
        arm("sha256-label-adjacent", '{"pin": "sha256 deadbeef1 of the artifact"}', {}, False)
        # audit r9 M-1: the arm that was missing. A dangling commit anchor
        # FURTHER ALONG a line that also carries a sha256 label must still
        # refuse -- this is the exact shape of the real records (one huge
        # single-line JSON value), and the r8 line-scoped rule passed it.
        arm("sha256-label-does-not-cover-the-line",
            '{"a": "sha256": "' + "ab" * 32 + '", "b": "landed at cafebabe1"}', {}, True)

        # 2026-09-15: the ANNOTATED COUNT is derived and reported, so a
        # document's prose no longer has to type it -- the defect that
        # prompted this was CLAUDE.md's provenance section saying "eleven"
        # above thirteen bullets and "Four" above six, in the one section
        # written to make its own citations checkable.
        #
        # Two-way, because a counter that counts every token and one that
        # counts none both pass a single-direction arm. An ANNOTATED token
        # counts 1; an ALLOW-covered one -- dangling and excused, but by a
        # LIST rather than by a sentence in the document -- counts 0, which
        # is the distinction the reported figure claims to make.
        def _annotated_count(content, allow):
            path = os.path.join(d, "rec.json")
            rel = os.path.relpath(path, ".")
            with open(path, "w", encoding="utf-8") as fh:
                fh.write(content)
            st = {}
            check([rel], ["."], allow, stats=st)
            return st["annotated"][rel]

        n_arms += 2
        if _annotated_count('{"n": "deadbeef1 resolves to no commit"}', {}) != 1:
            print("  [RED] provenance-anchors arm annotated-count-counts-an-annotation: "
                  "an annotated token was not counted")
            ok = False
        if _annotated_count('{"n": "corpus at deadbeef1"}', {"deadbeef1": "external"}) != 0:
            print("  [RED] provenance-anchors arm annotated-count-is-not-the-allow-list: "
                  "an ALLOW row was counted as an in-document annotation")
            ok = False
    # audit r8 M6: a commit that EXISTS in the object database but is
    # reachable from no ref -- exactly what a pre-rebase lane HEAD becomes --
    # must REFUSE, and a reachable one must pass. Needs a real repo, so this
    # arm builds one (~40 ms).
    with tempfile.TemporaryDirectory() as d:
        repo = os.path.join(d, "r")
        os.makedirs(os.path.join(repo, "data"))
        # A short all-digit SHA is deliberately ignored. Fix the object inputs so
        # both real nine-character fixture anchors exercise reachability every run.
        date = "1700000001 +0000"
        env = {**git_env, "GIT_AUTHOR_NAME": "t", "GIT_AUTHOR_EMAIL": "t@t.invalid",
               "GIT_COMMITTER_NAME": "t", "GIT_COMMITTER_EMAIL": "t@t.invalid",
               "GIT_AUTHOR_DATE": date, "GIT_COMMITTER_DATE": date}
        def g(*a):
            return subprocess.run(["git", "-C", repo, "-c", "commit.gpgSign=false",
                                   "-c", "tag.gpgSign=false", *a], capture_output=True,
                                  text=True, env=env, check=True)
        g("init", "-q", "-b", "main", "--object-format=sha1")
        with open(os.path.join(repo, "data", "rec.json"), "w") as fh:
            fh.write('{"n": "placeholder"}')
        g("add", "-A"); g("commit", "-qm", "base")
        base = g("rev-parse", "HEAD").stdout.strip()
        with open(os.path.join(repo, "data", "rec.json"), "w") as fh:
            fh.write('{"n": "second"}')
        g("add", "-A"); g("commit", "-qm", "second")
        orphan = g("rev-parse", "HEAD").stdout.strip()
        if any(len(sha) != 40 or not re.search(r"[a-f]", sha[:9]) for sha in (base, orphan)):
            raise ValueError("reachability selftest needs two extractable abbreviated commit IDs")
        g("reset", "--hard", "-q", base)          # orphan stays in the ODB
        # audit r9 M-2: the POSITIVE arms live HERE now. They used to be minted
        # from the ambient HEAD, which false-reds in every detached worktree
        # holding an unpushed commit -- 67 of this repo's 68 worktrees -- so
        # the gate's verdict depended on the caller's checkout rather than on
        # the record. This repo owns a real branch AND a tag, so `base` is
        # genuinely reachable through a shareable namespace and the arms mean
        # what they say.
        g("tag", "v-selftest", base)
        cases = [
            ("reachable-ref", '{"armed_commit": "%s"}' % base[:9], False),
            ("orphan-in-odb", '{"armed_commit": "%s"}' % orphan[:9], True),
            ("resolving-sha", '{"n": "measured at %s"}' % base[:9], False),
            ("resolving-40hex", '{"n": "tree at %s"}' % base, False),
            ("glued-resolving",
             '{"n": "see srcelab-2026-01-01-g%s.json"}' % base[:9], False),
        ]
        def repo_arm(tag, body, expect_bad):
            nonlocal ok, n_arms
            n_arms += 1
            with open(os.path.join(repo, "data", "rec.json"), "w") as fh:
                fh.write(body)
            if bool(check(["data/rec.json"], ["."], {}, root=repo)) != expect_bad:
                print(f"  [RED] provenance-anchors arm {tag}: expected "
                      f"{'refusal' if expect_bad else 'green'}, got the opposite")
                ok = False

        for case in cases:
            repo_arm(*case)
        # Run the orphan arm before introducing a ref. A local-only ref exercises
        # a different rejection from an object unreachable from every ref.
        g("update-ref", "refs/lane/keepalive", orphan)
        repo_arm("lane-ref-only-is-not-shareable", '{"armed_commit": "%s"}' % orphan[:9], True)
    # a missing audited file is a refusal
    if not check(["data/does_not_exist_xyz.json"], ["."], {}):
        print("  [RED] provenance-anchors arm missing-file: absence was not refused")
        ok = False
    if not ok:
        raise SystemExit("check_provenance_anchors selftest: arms misbehave")
    print(f"check_provenance_anchors selftest: {n_arms}/{n_arms} arms behave")


def main(argv):
    parser = argparse.ArgumentParser(
        description="Check the fixed Clean provenance inventory against Clean and its two neighbors.",
        allow_abbrev=False)
    parser.add_argument("--selftest", action="store_true")
    parser.add_argument("--trust-repo", metavar="PATH",
                        help="exact Trust Git worktree root (default: ../trust)")
    parser.add_argument("--trust-ir-repo", metavar="PATH",
                        help="exact TrustIR Git worktree root (default: ../trust-ir)")
    args = parser.parse_args(argv[1:])
    try:
        git_env = repository_git_environment()
        repos = selected_repositories(args, git_env)
    except (ValueError, OSError, subprocess.TimeoutExpired) as exc:
        parser.error(str(exc))
    if args.selftest:
        selftest(git_env)
        return 0
    print(f"PROVENANCE_REPOSITORIES clean={repos[0]} trust={repos[1]} trust-ir={repos[2]}")
    selftest(git_env)
    stats = {}
    bad = check(AUDITED, repos, ALLOW, git_env=git_env, stats=stats)
    if bad:
        print("PROVENANCE ANCHORS: FAIL -- sha-shaped anchors that resolve to no commit "
              "in the repositories printed above and carry no unresolvability "
              "annotation:", file=sys.stderr)
        for t, f, ctx in bad:
            print(f"  {t}  {f}\n    ...{ctx}...", file=sys.stderr)
        print("  Fetch the selected Trust and TrustIR repositories before believing this red (documented "
              "drift class); then either re-anchor the record at a committed sha or "
              "annotate the token '<sha> resolves to no commit' with the re-anchor "
              "path, or add a justified ALLOW row.", file=sys.stderr)
        return 1
    annotated = stats.get("annotated", {})
    carried = [(f, n) for f, n in annotated.items() if n]
    if carried:
        named = ", ".join(f"{f} {n}" for f, n in sorted(carried, key=lambda kv: (-kv[1], kv[0])))
        print(f"PROVENANCE_ANCHORS annotated (sha-shaped citations carrying an "
              f"unresolvability annotation): {named}")
    print(f"PROVENANCE_ANCHORS=ok files={len(AUDITED)} repos={len(repos)} "
          f"allow={len(ALLOW)} annotated={sum(annotated.values())}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
