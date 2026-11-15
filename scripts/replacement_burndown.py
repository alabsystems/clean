#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Render measured remaining work; reads existing evidence, never runs a gate.

Run from any directory. Historical inputs keep their recorded scope and date.
No sum or completion percentage is meaningful across these different units.
"""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def read(path):
    return json.loads((ROOT / path).read_text())


def main():
    conformance = read('data/lean_suite_conformance.json')
    totals = conformance['totals']
    native = read('reports/native-exec-battery.json')['programs']
    # Lean-rejected negative controls must not inflate the runtime denominator.
    accepted = [p for p in native if p['lean_rc'] == 0]
    equal = sum(p['verdict'] == 'BYTE_EQUAL' for p in accepted)
    census = read('reports/trust-ir-semantics-probe/census.json')['summary']
    slice_data = read('data/source_elab_ratchet.json')
    files = slice_data['files'].values()
    slice_ok = sum(f['success_baseline'] for f in files)
    slice_total = sum(f['decl_count'] for f in files)
    breadth = read('reports/source-elab/breadth-2026-09-23.json')['pooled']
    rows = [
        ('Lean accepted files', totals['elab_clean_accept'], totals['elab_oracle_files'],
         conformance['generated'], 'data/lean_suite_conformance.json'),
        ('Lean rejected files', totals['elab_fail_clean_reject'], totals['elab_fail_oracle_files'],
         conformance['generated'], 'data/lean_suite_conformance.json'),
        ('Native programs Lean accepts: exact output', equal, len(accepted),
         'date not recorded', 'reports/native-exec-battery.json'),
        ('First-party source files (not package build)', census['elaborated'], census['files'],
         'date not recorded; clean_args=[]', 'reports/trust-ir-semantics-probe/census.json'),
        ('Mathlib slice declarations (allow-sorry counting)', slice_ok, slice_total,
         slice_data['last_updated'], 'data/source_elab_ratchet.json'),
        ('Mathlib breadth sample declarations', breadth['pooled_success'], breadth['pooled_decls'],
         '2026-09-23', 'reports/source-elab/breadth-2026-09-23.json'),
    ]
    print('| Measured unit | Passing | Total | Remaining | Evidence date / limitation | Source |')
    print('|---|---:|---:|---:|---|---|')
    for label, passed, total, date, source in rows:
        if not 0 <= passed <= total:
            raise ValueError(f'invalid counts for {label}')
        print(f'| {label} | {passed} | {total} | {total-passed} | {date} | `{source}` |')
    print('\nHistorical evidence only; not a fresh run or a whole-project parity percentage.')
    for cohort_path, label in [
        ('reports/false-accept-refresh-2026-11-12/measurement-source.json',
         'Before class validation'),
        ('reports/false-accept-refresh-2026-11-12/measurement-class-attributes.json',
         'After class validation'),
        ('reports/false-accept-refresh-2026-11-12/measurement-csimp-source.json',
         'After compiler replacement validation'),
        ('reports/false-accept-refresh-2026-11-12/merged-header-cli-historical.json',
         'After header and arity validation (qualified source measurement)'),
        ('reports/false-accept-refresh-2026-11-12/landing-header-cli-historical.json',
         'Landing refresh after late test/ck0 integration'),
        ('reports/false-accept-refresh-2026-11-12/constructor-implicit-historical.json',
         'After constructor parameter inference boundary repair'),
        ('reports/false-accept-refresh-2026-11-12/mutable-shadowing-historical.json',
         'After scoped mutable-variable shadowing repair'),
        ('reports/false-accept-refresh-2026-11-12/landing-mutable-shadowing-historical.json',
         'Landing refresh after custody and documentation intake'),
        ('reports/false-accept-refresh-2026-11-12/do-expected-type-historical.json',
         'After monadic expected-type validation'),
        ('reports/false-accept-refresh-2026-11-12/landing-do-expected-type-historical.json',
         'Canonical landing refresh after provenance-cache recovery'),
        ('reports/false-accept-refresh-2026-11-12/merged-do-expected-type-historical.json',
         'Merged CLI refresh after main798 cutoff and checker intake'),
        ('reports/false-accept-refresh-2026-11-12/main768-do-expected-type-historical.json',
         'Merged CLI refresh after main768 source qualification'),
        ('reports/false-accept-refresh-2026-11-12/main70-do-expected-type-historical.json',
         'Merged CLI refresh after AY0.28 and mutual-universe qualification'),
        ('reports/false-accept-refresh-2026-11-12/compiler-eligibility-d844-historical.json',
         'After runtime code-availability repair (affected qualification/publication pending)'),
        ('reports/false-accept-refresh-2026-11-12/compiler-eligibility-fixed-f5de-historical.json',
         'Fixed binder-identity/main-intake refresh (source scopes checked; compiler baseline failures retained; follow-up/publication pending)'),
        ('reports/false-accept-refresh-2026-11-12/compiler-eligibility-main-b7c4-historical.json',
         'Latest kernel/pattern/CLI intake refresh (final checks/publication pending)'),
        ('reports/false-accept-refresh-2026-11-12/compiler-eligibility-main-7f7b-historical.json',
         'Current compiler eligibility replay after export-writer intake'),
    ]:
        if not (ROOT / cohort_path).exists():
            continue
        cohort = read(cohort_path)
        counts = cohort['counts']
        total = len(cohort['files'])
        if sum(counts.values()) != total:
            raise ValueError('cohort outcome counts disagree with measured cases')
        agreed = counts.get('agree-reject', 0)
        print('\nRecorded source measurement ' + cohort['generated_at'][:10]
              + ', selected historical failures only (Lean v4.35.0):')
        print('\n| Cohort | Correct rejection | Total | Remaining |')
        print('|---|---:|---:|---:|')
        print(f'| Historical false-accept cohort: {label} | {agreed} | {total} | {total-agreed} |')
        print('Outcomes: ' + json.dumps(counts, sort_keys=True))
        print('This does not remeasure previously passing files or replace the full historical ledger.')
    classification_path = ROOT / 'reports/header-inference-2026-11-12/historical-root-causes.json'
    for directory, prefix in (
        ('header-inference-2026-11-12', 'merged-header-cli'),
        ('header-inference-2026-11-12', 'landing-header-cli'),
        ('constructor-implicit-2026-11-13', 'constructor-implicit'),
        ('mutable-shadowing-2026-11-13', 'mutable-shadowing'),
        ('mutable-shadowing-2026-11-13', 'landing-mutable-shadowing'),
        ('do-expected-type-2026-11-13', 'do-expected-type'),
        ('do-expected-type-2026-11-13', 'landing-do-expected-type'),
        ('do-expected-type-2026-11-13', 'merged-do-expected-type'),
        ('do-expected-type-2026-11-13', 'main768-do-expected-type'),
        ('do-expected-type-2026-11-13', 'main70-do-expected-type'),
        ('compiler-eligibility-2026-11-13', 'source-d844'),
        ('compiler-eligibility-2026-11-13', 'fixed-f5de'),
        ('compiler-eligibility-2026-11-13', 'main-b7c4'),
    ):
        current_classification = ROOT / f'reports/{directory}/{prefix}-root-causes.json'
        current_measurement = current_classification.parent / f'{prefix}-checkpoint.json'
        if current_classification.exists():
            checkpoint = json.loads(current_measurement.read_text())
            artifact = ROOT / checkpoint['historical_report']
            selected = json.loads(current_classification.read_text())
            if (current_classification.parent / selected['source_measurement']).resolve() != artifact.resolve():
                raise ValueError('classification does not identify its qualified measurement')
            if hashlib.sha256(artifact.read_bytes()).hexdigest() != checkpoint['historical_report_sha256']:
                raise ValueError('qualified cohort measurement changed')
            classification_path = current_classification
    if classification_path.exists():
        classification = json.loads(classification_path.read_text())
        measurement_path = classification_path.parent / classification['source_measurement']
        measured = json.loads(measurement_path.read_text())
        remaining = {row['path'] for row in measured['files'] if row['outcome'] == 'false-accept'}
        cases = classification['cases']
        if len(cases) != len({row['path'] for row in cases}) or {row['path'] for row in cases} != remaining:
            raise ValueError('root-cause classification must cover each remaining case exactly once')
        print('\nRemaining cases in the selected source measurement; broad rejection parity remains open.')
        print('\n| Case | Root cause | State |')
        print('|---|---|---|')
        for row in cases:
            source = measurement_path.parent / 'fixtures' / row['path']
            if hashlib.sha256(source.read_bytes()).hexdigest() != row['source_sha256']:
                raise ValueError('classified source changed: ' + row['path'])
            print(f"| `{row['path']}` | {row['root_cause']} | {row['state']} |")
        print(f'{len(cases)} classified; {len(remaining) - len(cases)} unclassified. '
              'See the paired measurement and qualification for its exact source and publication scope.')
    class_path = 'reports/class-attribute-2026-11-12/source.json'
    if (ROOT / class_path).exists():
        cohort = read(class_path)
        if cohort['total'] != len(cohort['rows']) or cohort['agreed'] != sum(
                row['agrees'] for row in cohort['rows']):
            raise ValueError('class agreement count disagrees with measured cases')
        print('\nSeparate class-registration cohort: '
              f"{cohort['agreed']}/{cohort['total']} acceptance/rejection agreements "
              'through the production CLI. Full class parity remains open.')
    qualification_path = 'reports/unknown-attribute-rejection-2026-11-12/qualification.json'
    if (ROOT / qualification_path).exists():
        qualification = read(qualification_path)
        print('\nSeparate attribute cohort: '
              f"{qualification['negative_controls_resolved']}/{len(qualification['negative_controls'])} negative controls resolved; "
              f"{len(qualification['positive_controls'])} positive controls preserved "
              'through the production CLI at ' + qualification['qualification_source_commit'][:9]
              + '. Full attribute parity remains open.')
    protocol_path = 'reports/replacement-inventory-2026-11-12/protocol/methods.json'
    if (ROOT / protocol_path).exists():
        protocol = read(protocol_path)
        methods = protocol['methods']
        if (protocol['total'] != len(methods)
                or len({row['id'] for row in methods}) != len(methods)
                or sum(protocol['counts'].values()) != len(methods)
                or protocol['qualified'] != 0
                or any(row['qualification'] != 'not-measured' for row in methods)):
            raise ValueError('protocol inventory counts or unqualified states disagree')
        print('\nLatest-release builtin protocol overview: '
              f"{protocol['total']} named records; "
              f"{protocol['counts']['request']} requests, "
              f"{protocol['counts']['notification']} notifications and "
              f"{protocol['counts']['rpcRequest']} widget RPC methods. "
              'All await wire-contract qualification; broad protocol parity remains open.')
    inventory_path = 'reports/replacement-inventory-2026-11-12/summary.json'
    if (ROOT / inventory_path).exists():
        release = read(inventory_path)
        print('\nLatest-release file scope (not semantic case completion):')
        print('\n| Area | Target files | Added | Changed | Removed |')
        print('|---|---:|---:|---:|---:|')
        for name, counts in release['areas'].items():
            added, changed = counts.get('added', 0), counts.get('changed', 0)
            target = added + changed + counts.get('unchanged', 0)
            print(f"| {name} | {target} | {added} | {changed} | {counts.get('removed', 0)} |")
        print('\nAll target files await semantic qualification; unchanged files receive no parity credit.')



if __name__ == '__main__':
    main()
