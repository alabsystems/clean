#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""E7: build all twelve pinned Lean packages under theories/; census ALL constants by origin module.

Run under build-slot / heavy_gate.sh. No source text patterns determine a
verdict: module names come from source paths, declarations and closures from
Lean's compiled environment and #print axioms. Hash raw source bytes only.

Default: fresh mint in memory, compare exactly to data/lean_axiom_census.json.
--mint: update inventory/source identities, refusing any existing closure growth.
--self-test: real pinned-Lean mutations in an isolated temporary package.
Exit 0 measured agreement, 1 failure, 2 usage, 3 not knowable here (no pin).
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time
from unittest.mock import patch

ANSWERS_PINNED_INPUTS = True
ROOT = Path(__file__).resolve().parent.parent
ARTIFACT = ROOT / 'data/lean_axiom_census.json'
HELPER = ROOT / 'scripts/lean_axiom_census.lean'
PACKAGES = (
    'cic_l',
    'cic_l_base_bridge',
    'cic_l_model',
    'cic_l_nat_model',
    'cic_l_universe_zero',
    'kcheck',
    'kcheck_spec',
    'kcheck_labelled',
    'kcheck_soundness',
    'kcheck_sort_bounds',
    'binding_not_review',
    'chk_lia',
)
AX0 = frozenset(('propext', 'Quot.sound', 'Classical.choice'))


class Unknown(RuntimeError):
    pass


class Failed(RuntimeError):
    pass


def run(args: list[str], cwd: Path, env: dict) -> str:
    started = time.monotonic()
    if args[:2] == ['lake', 'build']:
        print(f'E7_BUILD package={cwd.name} command={args!r}', flush=True)
    p = subprocess.run(args, cwd=cwd, env=env, text=True,
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if p.returncode:
        raise Failed(f'command {args!r} in {cwd} exited {p.returncode}:\n{p.stdout}')
    if args[:2] == ['lake', 'build']:
        print(f'E7_BUILD package={cwd.name} exit=0 seconds={time.monotonic() - started:.2f}', flush=True)
    return p.stdout


def toolchain(package: Path, *, pin_source: bytes | None = None) -> tuple[str, dict, str]:
    pin_source = (package / 'lean-toolchain').read_bytes() if pin_source is None else pin_source
    pin = pin_source.decode().strip()
    # Never invoke an auto-installing proxy or a PATH lean routed to Clean.
    home = Path(os.environ.get('ELAN_HOME', str(Path.home() / '.elan')))
    bindir = home / 'toolchains' / pin.replace('/', '--').replace(':', '---') / 'bin'
    if not all((bindir / b).is_file() for b in ('lean', 'lake')):
        raise Unknown(f'{package.name}: pinned toolchain {pin} is not installed')
    env = {**os.environ, 'PATH': str(bindir) + os.pathsep + os.environ.get('PATH', ''),
           'ELAN_TOOLCHAIN': pin}
    # Discard inherited search paths: they could select stale foreign oleans.
    env.pop('LEAN_PATH', None)
    env.pop('LEAN_SRC_PATH', None)
    githash = run([str(bindir / 'lean'), '--githash'], package, env).strip()
    if not re.fullmatch('[0-9a-f]{40}', githash):
        raise Failed(f'{pin}: malformed Lean githash {githash!r}')
    return pin, env, githash


def sources(package: Path) -> tuple[list[str], dict[str, str]]:
    files = sorted(p for p in package.rglob('*.lean')
                   if not any(x.startswith('.') for x in p.relative_to(package).parts)
                   and p.name != 'lakefile.lean')
    modules = [p.relative_to(package).with_suffix('').as_posix().replace('/', '.') for p in files]
    if not modules:
        raise Failed(f'{package}: empty module inventory')
    inputs = files + [package / n for n in
                     ('lean-toolchain', 'lakefile.toml', 'lakefile.lean', 'lake-manifest.json', 'ORDER')
                     if (package / n).exists()]
    return modules, {p.relative_to(package).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
                     for p in sorted(inputs)}


def digest(inputs: dict) -> str:
    return hashlib.sha256(json.dumps(inputs, sort_keys=True).encode()).hexdigest()


def census(package: Path, output_filter=None, *, helper_source: bytes | None = None) -> dict:
    helper_source = HELPER.read_bytes() if helper_source is None else helper_source
    # Resolve the compiler from the same pin bytes the source record names.
    # Re-reading the live file in toolchain() could select a transient replacement
    # and then accept a record whose pin hash describes the restored file.
    pin_source = (package / 'lean-toolchain').read_bytes()
    modules, before = sources(package)
    if before.get('lean-toolchain') != hashlib.sha256(pin_source).hexdigest():
        raise Failed(f'PIN_CHANGED {package.name}: pin changed before source capture')
    pin, env, githash = toolchain(package, pin_source=pin_source)
    run(['lake', 'build'], package, env)
    # Build even modules outside defaultTargets (e.g. executable roots). A new
    # file not in lakefile roots must compile too, or this fails closed.
    run(['lake', 'build', *('+' + m for m in modules)], package, env)
    with tempfile.TemporaryDirectory(prefix='clean-e7-') as tmp:
        driver = Path(tmp) / 'Census.lean'
        driver.write_text(''.join(f'import {m}\n' for m in modules) + 'import Lean\n' +
                          'def e7Modules : List String := ' +
                          '[' + ', '.join(json.dumps(m) for m in modules) + ']\n' + helper_source.decode())
        output = run(['lake', 'env', 'lean', str(driver)], package, env)
    if output_filter is not None:
        output = output_filter(output)
    rows = []
    totals = []
    for line in output.splitlines():
        if line.startswith('E7_ROW '):
            row = json.loads(line.removeprefix('E7_ROW '))
            row['package'] = package.name
            row['axiom_closure'] = sorted(row['axiom_closure'])
            rows.append(row)
        elif line.startswith('E7_COUNT '):
            totals.append(int(line.removeprefix('E7_COUNT ')))
    if totals != [len(rows)]:
        raise Failed(f'CENSUS_COUNT {package.name}: Lean reported {totals}, parsed {len(rows)} declarations')
    if not rows or len({r['declaration'] for r in rows}) != len(rows):
        raise Failed(f'{package.name}: empty or duplicate census')
    if not {r['module'] for r in rows} <= set(modules):
        raise Failed(f'{package.name}: foreign module in census')
    _, after = sources(package)
    if before != after:
        raise Failed(f'{package.name}: sources changed during census')
    axiom_users = Counter(ax for row in rows for ax in row['axiom_closure'])
    summary = dict(declarations=len(rows),
                   private_declarations=sum(r['declaration'].startswith('_private.') for r in rows),
                   by_kind=dict(sorted(Counter(r['kind'] for r in rows).items())),
                   axiom_users={ax: axiom_users[ax] for ax in sorted(AX0)})
    return dict(package=package.name, lean_toolchain=pin, lean_githash=githash,
                source_sha256=digest(before), source_files=before, modules=modules,
                summary=summary,
                declarations=sorted(rows, key=lambda r: (r['module'], r['declaration'])))


def policy(fresh: dict, committed: dict | None, mint: bool = False) -> list[str]:
    problems = []
    def indexed(doc):
        return {(p['package'], r['declaration']): r
                for p in doc['packages'] for r in p['declarations']}
    new = indexed(fresh)
    for key, row in new.items():
        forbidden = set(row['axiom_closure']) - AX0
        if forbidden:
            problems.append(f'FORBIDDEN {key}: {sorted(forbidden)}')
    if committed is not None:
        old = indexed(committed)
        for key in new.keys() & old.keys():
            if set(new[key]['axiom_closure']) - set(old[key]['axiom_closure']):
                problems.append(f'GROWN {key}: {old[key]["axiom_closure"]} -> {new[key]["axiom_closure"]}')
        if not mint:
            for key in old.keys() - new.keys():
                problems.append(f'DROPPED {key}')
            for key in new.keys() - old.keys():
                problems.append(f'ADDED {key}')
            if fresh != committed:
                problems.append('STALE committed artifact disagrees with fresh mint')
    elif not mint:
        problems.append('MISSING committed artifact; run --mint')
    return problems


def measure_packages(packages: list[Path], helper: Path) -> dict:
    # One untrusted producer snapshot supplies every driver. A transient file
    # replacement cannot mix helper implementations across package results.
    helper_source = helper.read_bytes()
    # Preflight every pin before any build. Missing any pin is unknown, never
    # a partial green; a present compiler's build failure is always failure.
    for package in packages:
        toolchain(package)
    result = {'schema': 1, 'allowed_axioms': sorted(AX0),
              'census_helper_sha256': hashlib.sha256(helper_source).hexdigest(),
              'packages': [census(p, helper_source=helper_source) for p in packages]}
    for package, pkg in zip(packages, result['packages']):
        if sources(package)[1] != pkg['source_files']:
            raise Failed(f"{pkg['package']}: sources changed while another package was measured")
    if helper.read_bytes() != helper_source:
        raise Failed('HELPER_CHANGED: census helper changed during measurement')
    return result


def measure() -> dict:
    return measure_packages([ROOT / 'theories' / n for n in PACKAGES], HELPER)


def selftest_pin(pin: str) -> int:
    with tempfile.TemporaryDirectory(prefix='clean-e7-test-') as tmp:
        pkg = Path(tmp)
        (pkg / 'lean-toolchain').write_text(pin + '\n')
        (pkg / 'lakefile.toml').write_text('name = "e7_fixture"\ndefaultTargets = ["Fixture"]\n[[lean_lib]]\nname = "Fixture"\n')
        _, env, _ = toolchain(pkg)
        run(['lake', 'update'], pkg, env)
        src = pkg / 'Fixture.lean'
        base = ('namespace Unrelated\nprivate def unusedValue : Nat := 7\n'
                'private theorem unusedProof : True := True.intro\n'
                'private theorem hidden : True := True.intro\n'
                'def useHidden : True := hidden\ntheorem target : True = True := rfl\n'
                'end Unrelated\n')
        def mint(text):
            src.write_text(text)
            return {'packages': [census(pkg)]}
        old = mint(base)
        if policy(old, old):
            raise Failed('SELFTEST baseline was not green')
        rows = old['packages'][0]['declarations']
        for name, kind in (('unusedValue', 'definition'), ('unusedProof', 'theorem')):
            if not any(r['declaration'].startswith('_private.') and
                       r['declaration'].endswith('.' + name) and r['kind'] == kind for r in rows):
                raise Failed(f'SELFTEST unreachable private {kind} {name} omitted')
        print('SELFTEST private-module-selection=ok')
        # Same declaration names in another package must remain separate keys.
        other = dict(old['packages'][0], package='adopted_fixture',
                     declarations=[dict(r, package='adopted_fixture') for r in rows])
        expanded = {'packages': old['packages'] + [other]}
        if not any(e.startswith('ADDED') for e in policy(expanded, old)):
            raise Failed('SELFTEST added package was not detected')
        if policy(expanded, old, mint=True):
            raise Failed('SELFTEST legitimate package addition refused by --mint')
        print('SELFTEST added-package=ok (ADDED without mint)')
        if not any(e.startswith('DROPPED') for e in policy(old, expanded)):
            raise Failed('SELFTEST dropped package was not detected')
        print('SELFTEST dropped-package=ok (DROPPED)')
        forged_rows = [dict(r, axiom_closure=['adoptedFixtureAxiom']) for r in other['declarations']]
        forged = {'packages': old['packages'] + [dict(other, declarations=forged_rows)]}
        if not any(e.startswith('FORBIDDEN') for e in policy(forged, old, mint=True)):
            raise Failed('SELFTEST added package laundered a forbidden axiom')
        print('SELFTEST added-package-axiom=ok (FORBIDDEN even with mint)')
        for name, text, reason in (
            ('planted-axiom', base + 'axiom planted : False\n', 'FORBIDDEN'),
            ('planted-sorry', base + 'theorem unfinished : False := by sorry\n', 'FORBIDDEN'),
            ('dropped-declaration', base.replace('theorem target : True = True := rfl\n', ''), 'DROPPED'),
            ('grown-closure', base.replace(':= rfl', ':= propext ⟨id, id⟩'), 'GROWN'),
            ('added-declaration', base + 'def added : Nat := 1\n', 'ADDED'),
            ('stale-source', base + '-- source identity changed\n', 'STALE'),
        ):
            fresh = mint(text)
            errors = policy(fresh, old)
            if not any(e.startswith(reason) for e in errors):
                raise Failed(f'SELFTEST {name} did not trigger {reason}: {errors}')
            if name == 'planted-sorry' and not any('sorryAx' in e for e in errors):
                raise Failed('SELFTEST sorry was not diagnosed as sorryAx')
            if name == 'planted-axiom' and not any('planted' in e and e.startswith('FORBIDDEN') for e in errors):
                raise Failed('SELFTEST planted axiom not identified')
            if reason == 'GROWN' and not any(e.startswith('GROWN') for e in policy(fresh, old, mint=True)):
                raise Failed('SELFTEST --mint laundered closure growth')
            print(f'SELFTEST {name}=ok ({reason})')
        def drop_emitted_row(output):
            lines = output.splitlines(keepends=True)
            index = next(i for i, line in enumerate(lines) if line.startswith('E7_ROW '))
            return ''.join(lines[:index] + lines[index + 1:])
        src.write_text(base)
        try:
            census(pkg, output_filter=drop_emitted_row)
        except Failed as exc:
            if not str(exc).startswith('CENSUS_COUNT'):
                raise
            print('SELFTEST dropped-output-record=ok (CENSUS_COUNT)')
        else:
            raise Failed('SELFTEST a lost census record was accepted')
        with tempfile.TemporaryDirectory(prefix='clean-e7-helper-') as helper_dir:
            helper = Path(helper_dir) / 'helper.lean'
            helper_source = HELPER.read_bytes()
            helper.write_bytes(helper_source)
            real_census = census

            def changed_helper(*args, **kwargs):
                result = real_census(*args, **kwargs)
                helper.write_bytes(helper_source + b'\n-- changed during measurement\n')
                return result

            with patch(__name__ + '.census', side_effect=changed_helper):
                try:
                    measure_packages([pkg], helper)
                except Failed as exc:
                    if not str(exc).startswith('HELPER_CHANGED'):
                        raise
                else:
                    raise Failed('SELFTEST a changed helper was accepted')
            print('SELFTEST changed-helper=ok (HELPER_CHANGED)')
            helper.write_bytes(helper_source)

            def replaced_helper(*args, **kwargs):
                helper.write_text('this is deliberately invalid Lean\n')
                try:
                    return real_census(*args, **kwargs)
                finally:
                    helper.write_bytes(helper_source)

            with patch(__name__ + '.census', side_effect=replaced_helper):
                captured = measure_packages([pkg], helper)
            if captured['census_helper_sha256'] != hashlib.sha256(helper_source).hexdigest():
                raise Failed('SELFTEST helper digest does not name the executed snapshot')
            print('SELFTEST helper-snapshot=ok (transient replacement not executed)')
            helper.write_bytes(helper_source + b'\n-- new producer identity\n')
            changed = measure_packages([pkg], helper)
            if changed['packages'] != captured['packages']:
                raise Failed('SELFTEST helper comment changed the package evidence')
            if not any(e.startswith('STALE') for e in policy(changed, captured)):
                raise Failed('SELFTEST a changed helper identity was not detected')
            print('SELFTEST helper-identity=ok (STALE with identical package rows)')
        with tempfile.TemporaryDirectory(prefix='clean-e7-pin-') as pin_dir:
            # Both temporary names resolve to one real installed toolchain. This
            # tests the recorded identity, not a claim of compiler independence.
            pin_home = Path(pin_dir)
            toolchains = pin_home / 'toolchains'
            toolchains.mkdir()
            installed = Path(env['PATH'].split(os.pathsep)[0]).parent
            alias = 'leanprover/lean4:e7-transient-pin'
            for name in (pin, alias):
                (toolchains / name.replace('/', '--').replace(':', '---')).symlink_to(
                    installed, target_is_directory=True)
            pin_path = pkg / 'lean-toolchain'
            pin_bytes = pin_path.read_bytes()
            real_toolchain = toolchain

            def transient_pin(*args, **kwargs):
                pin_path.write_text(alias + '\n')
                try:
                    return real_toolchain(*args, **kwargs)
                finally:
                    pin_path.write_bytes(pin_bytes)

            with patch.dict(os.environ, {'ELAN_HOME': str(pin_home)}):
                with patch(__name__ + '.toolchain', side_effect=transient_pin):
                    captured = census(pkg)
                if captured['lean_toolchain'] != pin:
                    raise Failed('SELFTEST transient pin selected an unrecorded toolchain')
            print('SELFTEST pin-snapshot=ok (transient replacement not selected)')

            real_sources = sources
            def inconsistent_pin(*args, **kwargs):
                pin_path.write_text(alias + '\n')
                try:
                    return real_sources(*args, **kwargs)
                finally:
                    pin_path.write_bytes(pin_bytes)

            with patch(__name__ + '.sources', side_effect=inconsistent_pin):
                try:
                    census(pkg)
                except Failed as exc:
                    if not str(exc).startswith('PIN_CHANGED'):
                        raise
                else:
                    raise Failed('SELFTEST inconsistent pin/source observations accepted')
            print('SELFTEST pin-observation-mismatch=ok (PIN_CHANGED)')
        try:
            mint(base + 'def invalid := unknownE7Name\n')
        except Failed as exc:
            if "['lake', 'build']" not in str(exc):
                raise
            print('SELFTEST build-failure=ok (lake build refused)')
        else:
            raise Failed('SELFTEST invalid build accepted')
        (pkg / 'lean-toolchain').write_text('leanprover/lean4:e7-absent-toolchain\n')
        try:
            toolchain(pkg)
        except Unknown:
            print('SELFTEST absent-pin=ok (not knowable here, exit 3)')
        else:
            raise Failed('SELFTEST absent toolchain accepted')
    return 18


def selftest() -> None:
    pins = sorted({(ROOT / 'theories' / name / 'lean-toolchain').read_text().strip()
                   for name in PACKAGES})
    arms = sum(selftest_pin(pin) for pin in pins)
    print(f'LEAN_AXIOM_CENSUS_SELFTEST=ok arms={arms} toolchains={len(pins)}')


def main() -> int:
    if sys.argv[1:] == ['--pinned-inputs']:
        print('scripts/lean_axiom_census.lean')
        for name in PACKAGES:
            print(f'theories/{name}/lean-toolchain')
        return 0
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--mint', action='store_true')
    ap.add_argument('--self-test', action='store_true')
    args = ap.parse_args()
    try:
        if args.self_test:
            selftest()
            return 0
        fresh = measure()
        old = json.loads(ARTIFACT.read_text()) if ARTIFACT.exists() else None
        problems = policy(fresh, old, args.mint)
        if problems:
            raise Failed('\n'.join(problems))
        if args.mint:
            ARTIFACT.write_text(json.dumps(fresh, indent=2, ensure_ascii=False) + '\n')
        for pkg in fresh['packages']:
            counts = Counter(ax for r in pkg['declarations'] for ax in r['axiom_closure'])
            print(f'{pkg["package"]}: declarations={len(pkg["declarations"])} ' +
                  ' '.join(f'{ax}={counts[ax]}' for ax in sorted(AX0)))
        print('LEAN_AXIOM_CENSUS=ok' + (' minted' if args.mint else ''))
        return 0
    except Unknown as exc:
        print(f'LEAN_AXIOM_CENSUS=unknown not knowable here: {exc}')
        return 3
    except (Failed, OSError, ValueError, KeyError) as exc:
        print(f'LEAN_AXIOM_CENSUS=fail {exc}', file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.exit(main())
