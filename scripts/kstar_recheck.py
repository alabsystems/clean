#!/usr/bin/env python3
# Copyright 2026 The Clean contributors
# SPDX-License-Identifier: Apache-2.0
"""Q4 engineering gate: every member reads one immutable snapshot per subject.

A subject is the Ax0 restriction of the export named by --subject
(`kstar_subjects.restrict`): every declaration whose axiom closure leaves Ax0
is removed and reported by name with its axioms; the rest is byte-identical.
Exit 0 requires all subjects accepted, equal member-owned Ax0 inventories,
qualified pinned Lean4Lean and all three fixed controls refused for their
pinned reasons. Missing tools, incomplete reports, crashes, panics and
timeouts never vote; a panic is recorded as a panic, not a refusal. Fenced
Clean's refusals are classified (`kstar_subjects.classify_clean`), never
filtered. --members is a local build receipt, not a claim of compiler
verification. Each Rust member is built through --build-member, which stamps the
build's start (as cargo stamps a unit's dep-info) and the git state before and
after it. The replay records each Rust member's build read set (`build_reads`,
from cargo's dep-info and that stamp). --check-record calls the standing dated
result fresh only while it carries that set for both Rust members and every
listed file keeps its digest, and while the files `kstar_inputs` names (a
coarse lexical conjunct that no longer decides freshness alone) keep theirs; it
never promotes a red result. Binary availability is required for replay.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
import signal
from pathlib import Path
import subprocess
import sys
import tempfile
import time

import kstar_inputs
import kstar_subjects as subj
import lean4lean_recheck as l4l
import nanoda_recheck as nano

ROOT = Path(__file__).resolve().parents[1]
AX0 = sorted(nano.AX0)
ANSWERS_PINNED_INPUTS = True
MEMBERS = ('lean', 'clean-reference', 'ck0-stock', 'lean4lean')
RUST_MEMBERS = ('clean-reference', 'ck0-stock')
CONTROL_NAMES = ('extra-axiom', 'ill-typed-body', 'forged-recursor')
# The pinned exports (CIC_L, Lean v4.30.0-rc2 Init) and their Ax0 restrictions.
SOURCE_PINS = {
    '6c6c68a02a925b183747f2a4f8969ea281285b0b07d23a9f1f287241d4e69499',
    '2d6910ddbb751d79c7b5688878e5e9ffcadee9299f60ec80f738d567454742f4',
}
SUBJECT_PINS = {
    '6c6c68a02a925b183747f2a4f8969ea281285b0b07d23a9f1f287241d4e69499',
    'f7e9f661e137da8b9b3d71a8487d9b2ef7f96a0fc953f219e5f50d5fe9bd2d3f',
}
# Lean4Lean's pinned refusal of each control (its kernel's, or the runner's
# Ax0 policy). A panic matches none: it is recorded as a panic, with its
# decision class (`l4l.DECISIONS`). The pinned build ends ill-typed-body as
# `kernel-raised-then-panicked` (its `Kernel.Exception.mapEnvM` leaves a
# `declTypeMismatch`'s environment unmapped, so the renderer reads a stale
# extension), and no invocation of it or later commit reports it cleanly
# (docs/DECISIONS.md, Q4 residuals): that control stays red with that cause.
LEAN4LEAN_CONTROLS = {
    'extra-axiom': dict(kind='runner', reason='axiom outside Ax0: q3_extra_axiom'),
    'ill-typed-body': dict(kind='error', reason="at forged_bad: (kernel) declaration type mismatch, 'forged_bad' has type"),
    'forged-recursor': dict(kind='error', reason='at forged_rec_false: (kernel) application type mismatch'),
}


def digest(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def pinned_inputs():
    return ['scripts/kstar_recheck.sh', 'scripts/kstar_recheck.py',
            'scripts/kstar_selftest.py', 'scripts/kstar_inputs.py',
            'scripts/check_add_decl_ratchet.py', 'scripts/kstar_subjects.py',
            'scripts/kstar_subjects_selftest.py',
            'scripts/lean4lean_recheck.py', 'scripts/lean4lean_selftest.py',
            'scripts/nanoda_recheck.py',
            'scripts/lean_export_replay.sh', 'scripts/lean_export_replay/Upstream.lean',
            l4l.PIN, l4l.REASONS, l4l.REFERENCE_OBSERVATION, *l4l.patch_files(),
            *[nano.CONTROLS[n]['path'] for n in CONTROL_NAMES]]


# The fixed source inputs: the manifests, the runner (the input rule and the
# reference lexer it reads Rust through included), the theory and the controls.
FIXED_INPUTS = ('Cargo.toml', 'Cargo.lock', 'rust-toolchain.toml', '.cargo/config.toml',
                'scripts/kstar_recheck.sh', 'scripts/kstar_recheck.py', 'scripts/kstar_selftest.py',
                'scripts/kstar_inputs.py', 'scripts/check_add_decl_ratchet.py', 'data/kstar_build_reads.json',
                'scripts/kstar_subjects.py', 'scripts/lean4lean_recheck.py',
                'scripts/lean4lean_selftest.py', 'scripts/nanoda_recheck.py',
                'scripts/lean_export_replay.sh', 'scripts/lean_export_mint.sh', 'scripts/heavy_gate.sh',
                'scripts/lean_export_replay/Upstream.lean', l4l.PIN, l4l.REASONS, l4l.REFERENCE_OBSERVATION, *l4l.patch_files(),
                'theories/cic_l/lean-toolchain', 'theories/cic_l/ORDER',
                *[nano.CONTROLS[n]['path'] for n in CONTROL_NAMES])


def source_inputs():
    """Digest of each input `kstar_inputs` names; ValueError for a form it refuses."""
    return {p: digest(ROOT / p) for p in kstar_inputs.inputs(ROOT, FIXED_INPUTS)}


def invoke(argv, seconds=600):
    started = time.monotonic()
    try:
        p = subprocess.Popen(argv, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                             text=True, cwd=ROOT, start_new_session=True)
        try:
            stdout, stderr = p.communicate(timeout=seconds)
            code = p.returncode
        except subprocess.TimeoutExpired:
            os.killpg(p.pid, signal.SIGKILL)
            stdout, stderr = p.communicate()
            stderr += '\nquorum member timed out; its owned process group was stopped'
            code = None
        return dict(command=list(map(str, argv)), exit_code=code,
                    stdout=stdout, stderr=stderr, seconds=time.monotonic() - started)
    except OSError as e:
        return dict(command=list(map(str, argv)), exit_code=None, stdout='',
                    stderr=str(e), seconds=time.monotonic() - started)


def last_json(out):
    for line in reversed(out.splitlines()):
        try:
            obj = json.loads(line)
            if isinstance(obj, dict):
                return obj
        except ValueError:
            pass
    return {}


def component_name(parts):
    # ck0 emits tagged string/number components. Numeric Ax0 aliases cannot vote.
    if not all(isinstance(p, dict) and set(p) == {'str'} for p in parts):
        raise ValueError('non-string axiom component')
    return '.'.join(p['str'] for p in parts)


def evaluate(member, raw, expected_count, expected_axioms):
    """A zero exit alone is insufficient, including for an empty report."""
    obj = last_json(raw['stdout'])
    axioms, count, accepted = None, None, False
    try:
        if member == 'lean':
            axioms = sorted(obj['axioms'])
            count = obj['declarations']
            accepted = obj['verdict'] == 'accepted'
        elif member == 'clean-reference':
            axioms = sorted(obj['axioms'])
            count = obj['admitted']
            accepted = (obj['accepted'] is True and count == obj['declarations']
                        and not obj['refusals'] and not obj['unpermitted_axioms']
                        and obj['reader_error'] is None)
        elif member == 'ck0-stock':
            if obj['kind'] != 'coverage':
                raise ValueError('no completed coverage')
            axioms = sorted(component_name(a) for a in obj['axioms'])
            count = obj['accepted']
            accepted = count == obj['total'] and obj['refused'] == {}
        else:
            raise ValueError('unknown member')
        accepted = (accepted and raw['exit_code'] == 0 and count > 0
                    and count == expected_count and axioms == expected_axioms
                    and set(axioms) <= set(AX0))
    except (KeyError, TypeError, ValueError):
        accepted = False
    return dict(**raw, accepted=accepted, axioms=axioms, checked_count=count,
                verdict='accepted' if accepted else 'not knowable here' if raw['exit_code'] is None else 'refused')


def agreed(rows):
    return (set(rows) == set(MEMBERS) and all(r['accepted'] for r in rows.values())
            and len({tuple(r['axioms']) for r in rows.values()}) == 1)


def control_refused(member, name, row):
    if member == 'lean4lean':
        # The runner's Ax0 refusal follows a zero exit; a panic matches nothing.
        return not row['accepted'] and row.get('failure') == LEAN4LEAN_CONTROLS[name]
    if row['accepted'] or row.get('exit_code') in (None, 0):
        return False
    # Nonzero is not enough: require a control-specific kernel/policy diagnostic.
    text = row.get('stdout', '') + row.get('stderr', '')
    if name == 'extra-axiom':
        return 'q3_extra_axiom' in text and any(s in text.lower() for s in ('axiom', 'foundation'))
    if name == 'ill-typed-body':
        return any(s in text.lower() for s in ('type mismatch', 'typemismatch', 'not defeq', 'type-mismatch'))
    if member == 'lean':
        # Replay checks the forged use before comparing postponed recursors.
        # Pin that observed target; this is no isolated recursor-validation claim.
        return ("while replaying declaration 'forged_rec_false'" in text
                and 'application type mismatch' in text and '@FRT.rec' in text)
    if member == 'clean-reference':
        return ('FRT.rec: the structural tier refused it' in text
                and 'file (0, 0, 1, 0), kernel generates (0, 0, 1, 2)' in text)
    return 'malformed: recursor numMinors' in text


def identity(path):
    p = Path(path).resolve(strict=True)
    if not os.access(p, os.X_OK):
        raise ValueError(f'not executable: {p}')
    return dict(path=str(p), sha256=digest(p))


def parse_dep_info(text, target):
    """The paths cargo's dep-info for `target` names, read as cargo writes them (measured):
    one line, `<target>: <path> <path> ...`, a space in a path written `\\ ` and nothing
    else escaped (`:`, `\\`, `#` and `$` stand for themselves). Another line, another
    target or a relative path (`build.dep-info-basedir`) refuses."""
    heads = [str(t).replace(' ', '\\ ') + ':' for t in (target, os.path.realpath(target))]
    head = next((h for h in heads if text.startswith(h)), None)
    if head is None or not text.endswith('\n') or '\n' in text[:-1]:
        raise ValueError(f'dep-info is not one rule for {target}')
    rest, paths, i = text[len(head):-1], [], 0
    while i < len(rest):
        if rest[i] != ' ' or i + 1 == len(rest) or rest[i + 1] == ' ':
            raise ValueError(f'dep-info for {target} is malformed at column {len(head) + i}')
        i, path = i + 1, []
        while i < len(rest) and rest[i] != ' ':
            step = 2 if rest.startswith('\\ ', i) else 1
            path.append(' ' if step == 2 else rest[i])
            i += step
        paths.append(''.join(path))
    if any(not os.path.isabs(p) for p in paths):
        raise ValueError(f'dep-info for {target} names a relative path')
    return paths


def watched_packages(root, listed):
    """Each repository package whose build script the dep-info lists, by name."""
    roots = {d for p in listed for d in (root / p).parents if d == root or root in d.parents}
    for d in sorted(roots):
        table = kstar_inputs.read_toml(d / 'Cargo.toml', d) if (d / 'Cargo.toml').is_file() else {}
        package = table.get('package', table.get('project'))  # cargo still reads `[project]`
        build = package.get('build', True) if isinstance(package, dict) else False
        script = 'build.rs' if build is True else build
        if isinstance(script, str) and os.path.relpath((d / script).resolve(), root) in listed:
            yield package['name']


BUILD_RECORD = '.kstar-build.json'  # beside the member binary: the build-start stamp and git state
SHA256_HEX = frozenset('0123456789abcdef')


def git(root, *argv, stdin=None):
    """A git command's stdout in `root`, the caller's GIT_* variables dropped; ValueError when it fails."""
    env = {key: value for key, value in os.environ.items() if not key.startswith('GIT_')}
    done = subprocess.run(['git', '--no-optional-locks', '-C', str(root), *argv], input=stdin,
                          capture_output=True, text=True, env=env)
    if done.returncode:
        raise ValueError(f'git {argv[0]} in {root} exited {done.returncode}: {done.stderr.strip()[:200]}')
    return done.stdout


def tree_state(root):
    """(HEAD, every tracked path that differs from HEAD in the index or the work tree, renames' sources included)."""
    fields = git(root, 'status', '--porcelain=v1', '-z', '--untracked-files=no').split('\0')
    dirty, i = [], 0
    while i < len(fields) and fields[i]:
        dirty.append(fields[i][3:])
        if set(fields[i][:2]) & set('RC'):  # the source path follows
            i += 1
            dirty.append(fields[i])
        i += 1
    return git(root, 'rev-parse', 'HEAD').strip(), sorted(dirty)


def build_member(name, built, argv, root=None, env=None):
    """Run a Rust member's build command `argv`, stamped the way cargo stamps a unit's dep-info.

    Before the command runs it creates `<built>.kstar-build.json`, whose mtime is the build-start
    stamp, and reads HEAD and the tracked paths that differ from it; after the command it reads
    them again and writes them, the stamp, the exit status and the binary's sha256 into that file.
    `build_reads` refuses a member built any other way. Returns the command's exit status."""
    root, built = (root or ROOT).resolve(), Path(built)
    record = built.with_name(built.name + BUILD_RECORD)
    record.parent.mkdir(parents=True, exist_ok=True)
    record.unlink(missing_ok=True)
    record.write_text('')  # its mtime is the stamp, on the file system's clock as cargo reads its own
    started = record.stat().st_mtime_ns
    head, dirty = tree_state(root)
    code = subprocess.run(list(map(str, argv)), cwd=root, env=env).returncode
    head_after, dirty_after = tree_state(root)
    record.write_text(json.dumps(dict(
        schema='clean.kstar-build.v1', member=name, command=list(map(str, argv)), started_ns=started,
        head_before=head, head_after=head_after, dirty_before=dirty, dirty_after=dirty_after, exit_code=code,
        binary_sha256=digest(built) if built.is_file() else None), indent=2) + '\n')
    return code


def build_stamp(name, built, sha):
    """The build-start record beside `built`, validated: of this binary, a completed build, HEAD unmoved."""
    path = built.with_name(built.name + BUILD_RECORD)
    try:
        b = json.loads(path.read_text())
    except (OSError, ValueError):
        raise ValueError(f'{name}: no build-start record beside {built} (build it through --build-member)') from None
    shape = dict(member=str, started_ns=int, head_before=str, head_after=str, dirty_before=list,
                 dirty_after=list, exit_code=int, binary_sha256=str)
    if (not isinstance(b, dict) or any(type(b.get(key)) is not t for key, t in shape.items())
            or not all(isinstance(p, str) for p in b['dirty_before'] + b['dirty_after'])):
        raise ValueError(f'{name}: malformed build-start record {path}')
    if b['member'] != name or b['binary_sha256'] != sha:
        raise ValueError(f'{name}: the build-start record {path} is of another build')
    if b['exit_code'] != 0:
        raise ValueError(f"{name}: the stamped build exited {b['exit_code']}")
    if b['head_before'] != b['head_after']:
        raise ValueError(f"{name}: HEAD moved during the build ({b['head_before']} to {b['head_after']})")
    return b


def blob_ids(root, head, paths):
    """{path: its blob's object id at `head`, or None when `head` holds no blob there}."""
    if any('\n' in p for p in paths):
        raise ValueError('a build read path holds a newline')
    out = git(root, 'cat-file', '--batch-check=%(objectname) %(objecttype)',
              stdin=''.join(f'{head}:{p}\n' for p in paths)).splitlines()
    if len(out) != len(paths):
        raise ValueError(f'git cat-file answered {len(out)} of {len(paths)} paths at {head}')
    return {p: line.split(' ')[0] if line.endswith(' blob') else None for p, line in zip(paths, out)}


def first_link(listed, root):
    """The first symbolic link the listed path passes through inside the repository, else None."""
    step = ''
    for part in Path(listed).parts:
        step = os.path.join(step, part)
        here = Path(os.path.normpath(step))
        if (here == root or root in here.parents) and os.path.islink(step):
            return step
    return None


def build_reads(name, entry, root=None, head=None):
    """{repository path: sha256} of each repository file a Rust member's build depends on.

    The source is the dep-info cargo writes beside the binary (`<target>/<profile>/<bin>.d`,
    at `built_at`): what rustc read for each local package and every rerun-if-changed path,
    keyed as the dep-info lists it, normalized lexically and never resolved. The time of the
    reads is the build's START, which `build_member` stamps before the command runs, as cargo
    stamps a unit's dep-info; the dep-info's own mtime, written at the end, is not used.
    Refused (ValueError), beyond a dep-info of another shape:
    - no dep-info, one older than the binary (stock cargo keeps an unchanged one on a relink:
      remove it first) or beside other bytes;
    - no build-start record of this binary, a build that exited nonzero, HEAD moving during it;
    - any tracked path not clean before or after the build, listed or not: a dirty manifest,
      Cargo.lock, Cargo configuration, rust-toolchain.toml or unlisted build-script input changes
      what is built while the dep-info lists none of them, so members are built in a clean checkout;
    - a listed repository file that cannot be read as a file, whose mtime is at or after the
      stamp, that HEAD does not track, or whose bytes differ from its blob at the build's HEAD
      or at the record's (`head`);
    - a listed path that is a symbolic link, passes through one inside the repository, or
      reaches the repository through one;
    - a path outside the repository, the target directory, Cargo's home and the toolchain, no
      repository file, and a repository build script that printed no rerun-if-changed (cargo
      then watches package files the dep-info omits).
    Inside the repository the set omits manifests, Cargo.lock and Cargo configuration (the
    `kstar_inputs` conjunct hashes them at receipt and check). Uncovered residuals, not claimed
    (docs/DECISIONS.md, 2026-11-19, "Q4 freshness rests on the members' build read sets", and its
    corrections):
    - a listed file edited and reverted with its mtime restored before these checks: the mtime
      test and git's stat cache both miss it, and benign tools do it (`cp -p` or shutil.copy2
      restores: scripts/bump-trust-ir-pin.sh's rollback, scripts/crystal_perturb_meta_tag_shl.sh);
    - an untracked file the build reads without the dep-info listing it (the dirty set holds
      tracked paths only);
    - native link inputs, and what a proc macro or build script reads unnamed;
    - outside the repository, where nothing is hashed here: the bytes under Cargo's home
      (Cargo.lock pins registry archive checksums and git revisions, not the extracted sources,
      which cargo does not re-verify); Cargo configuration outside the repository
      ($CARGO_HOME/config.toml, and .cargo/config.toml in the repository's parent directories);
      the build environment (RUSTFLAGS and other variables: the build-start record keeps none);
      the linker and system libraries; a registry build script's reads beyond its sources; and
      clean-olean's build script, in clean-reference's graph, which reads the installed Lean
      toolchain's .olean parts with no rerun-if-changed and compiles their BLAKE3 manifest into
      the binary (data/kstar_build_reads.json, `outside`).
    The Rust toolchain is pinned by identity only (the receipt's compiler path, that executable's
    sha256 and its `-Vv` line; the replay hashes the stock member's compiler again, --check-record
    neither, and no sysroot library is hashed); target-directory files follow from their inputs."""
    root = (root or ROOT).resolve()
    built = Path(entry.get('built_at') or entry['binary']['path'])
    dep = built.with_name(built.name + '.d')
    if not dep.is_file():
        raise ValueError(f'{name}: no dep-info beside {built}')
    if not built.is_file() or digest(built) != entry['binary']['sha256']:
        raise ValueError(f'{name}: {built} is not the member binary, so its dep-info is of another build')
    if dep.stat().st_mtime_ns < built.stat().st_mtime_ns:
        raise ValueError(f'{name}: dep-info {dep} is older than the binary')
    stamp = build_stamp(name, built, entry['binary']['sha256'])
    outside = {built.parent.parent, Path(os.environ.get('CARGO_HOME') or Path.home() / '.cargo')}
    if 'compiler_path' in entry:  # the toolchain: its directory and the sysroot it prints
        sysroot = invoke([entry['compiler_path'], '--print', 'sysroot'], 60)
        outside |= {Path(entry['compiler_path']).parent.parent, Path(sysroot['stdout'].strip() or '/nonexistent')}
    outside |= {o.resolve() for o in outside}
    reads, blobs = {}, {}
    hasher = git(root, 'rev-parse', '--show-object-format').strip()
    def under(x):
        return any(x == o or o in x.parents for o in outside)
    def inside(x):
        return x == root or root in x.parents
    for p in parse_dep_info(dep.read_bytes().decode(), built):
        lexical, real = Path(os.path.normpath(p)), Path(os.path.realpath(p))
        if under(lexical):
            if inside(real) and not under(real):
                raise ValueError(f'{name}: dep-info lists {p}, which reaches the repository through a symbolic link')
            continue  # not hashed, even for a target directory inside the repository
        if not inside(lexical):
            if inside(real):
                raise ValueError(f'{name}: dep-info lists {p}, which reaches the repository through a symbolic link')
            if under(real):
                continue
            raise ValueError(f"{name}: dep-info names {p}, outside the repository, the target directory, Cargo's home and the toolchain")
        link = first_link(p, root)
        if link or real != lexical:
            what = 'is' if link and Path(os.path.normpath(link)) == lexical else 'passes through'
            raise ValueError(f'{name}: dep-info lists {p}, which {what} a symbolic link ({link or real})')
        rel = lexical.relative_to(root).as_posix()
        if not lexical.is_file():
            raise ValueError(f'{name}: dep-info lists {p}, which cannot be read as a file')
        if lexical.stat().st_mtime_ns >= stamp['started_ns']:
            raise ValueError(f'{name}: dep-info lists {rel}, which changed at or after the start of the build')
        data = lexical.read_bytes()
        reads[rel] = hashlib.sha256(data).hexdigest()
        blobs[rel] = hashlib.new(hasher, b'blob %d\0' % len(data) + data).hexdigest()
    # Any dirty tracked path refuses, listed or not: the dep-info lists no manifest or configuration.
    dirty = sorted(set(stamp['dirty_before']) | set(stamp['dirty_after']))
    if dirty:
        raise ValueError(f"{name}: tracked paths were not clean before or after the build ({', '.join(dirty[:5])}"
                         f"{', ...' if len(dirty) > 5 else ''}); build the member in a clean checkout")
    if not reads:
        raise ValueError(f'{name}: dep-info names no repository file')
    for commit in dict.fromkeys(h for h in (stamp['head_before'], head) if h):
        for rel, oid in blob_ids(root, commit, list(blobs)).items():
            if oid is None:
                raise ValueError(f'{name}: dep-info lists {rel}, which {commit} does not track')
            if oid != blobs[rel]:
                raise ValueError(f'{name}: dep-info lists {rel}, whose bytes differ from its blob at {commit}')
    for package in watched_packages(root, reads):
        # Build-script output: `build/<package>-<hash>/output`, or `build/<package>/<hash>/run/stdout`
        # in the build-dir layout Trust's targo writes.
        found = [d / 'output' for d in (built.parent / 'build').glob(package + '-*') if d.name[len(package) + 1:].isalnum()]
        outputs = sorted(o for o in found + list((built.parent / 'build' / package).glob('*/run/stdout')) if o.is_file())
        if not outputs:
            raise ValueError(f'{name}: no build-script output of {package} beside {built}')
        for out in outputs:
            if not any(line.startswith(('cargo:rerun-if-changed=', 'cargo::rerun-if-changed='))
                       for line in out.read_text(errors='replace').splitlines()):
                raise ValueError(f'{name}: the build script of {package} printed no rerun-if-changed ({out}): '
                                 'cargo then watches its whole package (or, with rerun-if-env-changed, no file), '
                                 'and the dep-info lists none of what it reads')
    return reads


def moved_build_reads(reads):
    """Each listed file whose bytes moved; ValueError for a build read set of any other shape."""
    if not isinstance(reads, dict):
        raise ValueError('record carries no build read set')
    for member in RUST_MEMBERS:
        if not isinstance(reads.get(member), dict) or not reads[member]:
            raise ValueError(f'record carries no build read set for {member}')
    if set(reads) != set(RUST_MEMBERS):
        raise ValueError('build read set names a member other than ' + ' and '.join(RUST_MEMBERS))
    for member, files in reads.items():
        for p, h in files.items():
            if not isinstance(h, str) or len(h) != 64 or not set(h) <= SHA256_HEX:
                raise ValueError(f'build read set of {member} holds no sha256 for {p}')
            if Path(p).is_absolute() or '..' in Path(p).parts or os.path.normpath(p) != p:
                raise ValueError(f'build read set of {member} names {p}, not a normalized path inside the repository')
    return sorted({p for files in reads.values() for p, h in files.items()
                   if not (ROOT / p).is_file() or digest(ROOT / p) != h})


def prepare(args):
    receipt = json.loads(args.members.read_text())
    if receipt['source_inputs'] != source_inputs():
        raise ValueError('build receipt inputs differ from the current source')
    identities = {}
    for name in ('clean-reference', 'ck0-stock'):
        entry = receipt[name]
        if entry['build_exit_code'] != 0:
            raise ValueError(f'{name}: build did not complete')
        actual = identity(entry['binary']['path'])
        if actual != entry['binary']:
            raise ValueError(f'{name}: binary identity changed')
        identities[name] = entry
        print(f"kstar member {name}: {entry['lane']}; {entry['compiler_version'].splitlines()[0]}", flush=True)
    stock = receipt['ck0-stock']
    if stock['lane'] != 'STOCK EXCEPTION' or 'trust' in stock['compiler_version'].lower():
        raise ValueError('ck0 has no stock compiler build receipt')
    if digest(stock['compiler_path']) != stock['compiler_sha256']:
        raise ValueError('stock compiler identity changed')
    lean = Path.home() / '.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean'
    gh = invoke([str(lean), '--githash'])
    if gh['exit_code'] != 0 or gh['stdout'].strip() != '3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc':
        raise ValueError('pinned Lean unavailable or wrong commit')
    identities['lean'] = dict(binary=identity(lean), commit=gh['stdout'].strip(),
                              toolchain='leanprover/lean4:v4.30.0-rc2',
                              reader='lean4export Export.parseStream at 12581a6b680d8478175596338eb2d53383a323e3',
                              runtime={p.name: digest(p) for p in sorted((lean.parent.parent / 'lib/lean').glob('*.dylib'))})
    pin = json.loads((ROOT / l4l.PIN).read_text())
    binary = args.lean4lean or Path.home() / '.cache/clean-lean4lean/sha256' / pin['binary_sha256'] / 'lean4lean'
    actual = identity(binary)
    if actual['sha256'] != pin['binary_sha256']:
        raise ValueError('lean4lean binary differs from its pin')
    identities['lean4lean'] = dict(binary=actual, commit=pin['commit'], toolchain=pin['lean_toolchain'],
                                   lean_githash=pin['lean_githash'], repository=pin['repository'])
    return identities


def replay(data, ids, timeout, graph, excluded=()):
    inv = nano.inventory(data)
    expected_axioms = inv['axioms']
    count = len(inv['declarations'])
    with tempfile.TemporaryDirectory(prefix='kstar-') as td:
        path = Path(td) / 'subject.ndjson'
        path.write_bytes(data)
        permits = sum((['--permit', a] for a in AX0), [])
        commands = {
            'lean': [str(ROOT / 'scripts/lean_export_replay.sh'), '--reader', 'upstream', str(path), *permits],
            'clean-reference': [ids['clean-reference']['binary']['path'], '--reference', '--json', str(path), *permits],
            'ck0-stock': [ids['ck0-stock']['binary']['path'], str(path)],
        }
        rows = {name: evaluate(name, invoke(cmd, timeout), count, expected_axioms)
                for name, cmd in commands.items()}
        pin = ids['lean4lean']['binary']
        r = l4l.recheck(Path(pin['path']), data, timeout, pin['sha256'])
        r['accepted'] = (r['accepted'] and r['axioms'] == expected_axioms
                         and r['checked_count'] == r['model']['expected_checked'])
        r.pop('model')
        if not r['accepted'] and r['verdict'] == 'accepted':
            r['verdict'] = 'refused'
        rows['lean4lean'] = dict(r, exit_code=r['exit_status'], seconds=r['wall_seconds'])
        if path.read_bytes() != data:
            raise ValueError('member modified the subject snapshot')
    clean = rows['clean-reference']
    if not clean['accepted']:
        report = last_json(clean['stdout'])
        if isinstance(report.get('refusals'), list):
            c = subj.classify_clean(report['refusals'], graph, excluded)
            c['consistent'] = (c['refused'] == c['left_out'] == report['declarations'] - report['admitted']
                               and not c['unresolved'])
            clean['classification'] = c
    ck0 = rows['ck0-stock']
    if not ck0['accepted']:
        ck0['refusal'] = last_json(ck0['stdout'])
    for name, entry in ids.items():
        if digest(entry['binary']['path']) != entry['binary']['sha256']:
            raise ValueError(f'{name}: binary changed during replay')
    return dict(sha256=hashlib.sha256(data).hexdigest(), bytes=len(data), declarations=count,
                input_axioms=expected_axioms, members=rows, accepted=agreed(rows))


def check_record(path):
    try:
        r = json.loads(path.read_text())
        if not isinstance(r, dict):
            raise ValueError('record is not a JSON object')
        moved = moved_build_reads(r.get('build_reads'))
        if moved:
            raise ValueError('stale build reads: ' + ', '.join(moved[:5]))
        if r['source_inputs'] != source_inputs():
            raise ValueError('stale source inputs')
        if not r['success'] or not r['subjects'] or not r['qualified_lean4lean']:
            raise ValueError('record is red or incomplete')
        if (len(r['subjects']) != len(SUBJECT_PINS)
                or {s['sha256'] for s in r['subjects']} != SUBJECT_PINS
                or {s['source_sha256'] for s in r['subjects']} != SOURCE_PINS):
            raise ValueError('standing record does not cover the two pinned subjects')
        if set(r['identities']) != set(MEMBERS):
            raise ValueError('standing record lacks a member identity')
        if not all(agreed(s['members']) for s in r['subjects']):
            raise ValueError('a subject lacks every member acceptance')
        if set(r['controls']) != set(CONTROL_NAMES) or not all(
            control_refused(m, n, c['members'][m]) for n, c in r['controls'].items() for m in MEMBERS):
            raise ValueError('a control lacks a member refusal')
        if any(c['sha256'] != nano.CONTROLS[n]['sha256'] for n, c in r['controls'].items()):
            raise ValueError('standing control bytes differ from the committed pins')
        for name, entry in r['identities'].items():
            if identity(entry['binary']['path']) != entry['binary']:
                raise ValueError(f'{name}: binary unavailable or changed')
        print('KSTAR_RECHECK=accepted'); return 0
    except (OSError, ValueError, KeyError, TypeError) as e:
        print(f'KSTAR_RECHECK=not knowable here: {e}'); return 1


def main():
    argv = sys.argv[1:]
    # --build-member's command follows `--`; nothing after it is read as an option here.
    argv, command = (argv[:argv.index('--')], argv[argv.index('--') + 1:]) if '--' in argv else (argv, [])
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--selftest', action='store_true')
    ap.add_argument('--build-member', choices=RUST_MEMBERS,
                    help='run the member build command given after --, stamped (build_member)')
    ap.add_argument('--built-at', type=Path, help='with --build-member: the binary the command builds')
    ap.add_argument('--pinned-inputs', action='store_true')
    ap.add_argument('--check-record', type=Path)
    ap.add_argument('--members', type=Path)
    ap.add_argument('--lean4lean', type=Path)
    ap.add_argument('--subject', type=Path, action='append')
    ap.add_argument('--out', type=Path)
    ap.add_argument('--timeout', type=int, default=600)
    args = ap.parse_args(argv)
    if args.build_member:
        if not args.built_at or not command:
            print('KSTAR_BUILD=not knowable here: --built-at and a command after -- required'); return 2
        try:
            return build_member(args.build_member, args.built_at, command)
        except (OSError, ValueError) as e:  # git unreadable: the record stays empty, which refuses
            print(f'KSTAR_BUILD=not knowable here: {e}'); return 2
    if args.selftest:
        from kstar_selftest import selftest
        return selftest()
    if args.pinned_inputs:
        print('\n'.join(pinned_inputs())); return 0
    if args.check_record:
        return check_record(args.check_record)
    if not args.members or not args.subject or not args.out:
        print('KSTAR_RECHECK=not knowable here: --members, --subject and --out required')
        return 1
    try:
        inputs = source_inputs()
    except (OSError, ValueError) as e:
        print(f'KSTAR_RECHECK=not knowable here: {e}'); return 1
    record = dict(source_commit=invoke(['git', 'rev-parse', 'HEAD'])['stdout'].strip(),
                  dirty_status=invoke(['git', 'status', '--porcelain'])['stdout'],
                  schema='clean.kstar-recheck.v1', utc=datetime.now(timezone.utc).isoformat(),
                  success=False, qualified_lean4lean=False, subjects=[], controls={}, source_inputs=inputs,
                  limits='Implementation agreement, not semantic soundness. Per-bound claims only; no generation exceeds its base; independent quorum required.')
    args.out.mkdir(parents=True, exist_ok=False)
    def save():
        (args.out / 'replay.json').write_text(json.dumps(record, indent=2) + '\n')
    save()
    try:
        ids = prepare(args)
        record['identities'] = ids; save()
        record['build_reads'] = {n: build_reads(n, ids[n], head=record['source_commit']) for n in RUST_MEMBERS}; save()
        # Arena qualification is executed afresh; no historical JSON can confer a vote.
        binary = ids['lean4lean']['binary']['path']
        rc = l4l.main(['--binary', binary, '--out', str(args.out / 'lean4lean-qualification')])
        record['qualified_lean4lean'] = rc == 0
        record['lean4lean_qualification_exit'] = rc; save()
        # Run every member even after a finding; never filter the subject
        # beyond its Ax0 restriction, whose removals are named.
        for path in args.subject:
            source = path.read_bytes()
            data, excluded, graph = subj.restrict(source)
            row = replay(data, ids, args.timeout, graph, [n for e in excluded for n in e['names']])
            row.update(path=str(path.resolve()), source_sha256=hashlib.sha256(source).hexdigest(),
                       source_bytes=len(source), excluded=excluded,
                       restriction='kstar_subjects.restrict: declarations whose axiom closure leaves Ax0, removed by name')
            record['subjects'].append(row); save()
        for name in CONTROL_NAMES:
            control = nano.CONTROLS[name]
            path = ROOT / control['path']
            if digest(path) != control['sha256']:
                raise ValueError(f'{name}: committed control changed')
            data = path.read_bytes()
            # A control is replayed as committed, never restricted.
            row = replay(data, ids, args.timeout, subj.restrict(data)[2])
            row['all_refused_for_reason'] = all(control_refused(m, name, row['members'][m]) for m in MEMBERS)
            row['refused_for_reason'] = {m: control_refused(m, name, row['members'][m]) for m in MEMBERS}
            row['panicked'] = sorted(m for m, r in row['members'].items() if r.get('verdict') == 'panic')
            record['controls'][name] = row; save()
        if source_inputs() != record['source_inputs'] or moved_build_reads(record['build_reads']):
            raise ValueError('source inputs or build reads changed during replay')
        record['success'] = (record['qualified_lean4lean'] and all(s['accepted'] for s in record['subjects'])
                             and all(c['all_refused_for_reason'] for c in record['controls'].values()))
        save()
        print('KSTAR_RECHECK=' + ('accepted' if record['success'] else 'refused: see replay.json'))
        return 0 if record['success'] else 1
    except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as e:
        record['error'] = str(e); save()
        print(f'KSTAR_RECHECK=not knowable here: {e}'); return 1


if __name__ == '__main__':
    sys.exit(main())
