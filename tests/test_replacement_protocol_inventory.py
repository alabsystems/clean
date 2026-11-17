# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
import hashlib
import importlib.util
import copy
import gzip
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('protocol_inventory', ROOT / 'scripts/replacement_protocol_inventory.py')
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
SOURCE = ROOT / 'reports/replacement-inventory-2026-11-12/protocol/ProtocolOverview.lean'
BASE_TREE = ROOT / 'reports/replacement-inventory-2026-11-12/v4.35.0-tree.json.gz'
TARGET = ROOT / 'reports/replacement-inventory-2026-11-16/protocol'
TARGET_TREE = TARGET.parent / 'v4.36.0-tree.json.gz'
SCRIPT = ROOT / 'scripts/replacement_protocol_inventory.py'
PYTHON = [sys.executable, *(['-O'] if sys.flags.optimize else [])]


def blob(source):
    return hashlib.sha1(b'blob ' + str(len(source)).encode() + b'\0' + source).hexdigest()


class ProtocolInventoryTests(unittest.TestCase):
    def test_real_overview_retains_all_records_and_exact_locations(self):
        source = SOURCE.read_bytes()
        report = m.inventory(source, 'ddd3587f89804c5c05e49b9b7432514066266322')
        self.assertEqual(report['total'], 59)
        self.assertEqual(report['counts'], {'notification': 12, 'request': 37, 'rpcRequest': 10})
        self.assertEqual(report['qualified'], 0)
        lines = source.decode().splitlines()
        for row in report['methods']:
            self.assertEqual(row['qualification'], 'not-measured')
            self.assertEqual(lines[row['source_line'] - 1], '  .' + row['kind'] + ' {')
        identities = {r['id'] for r in report['methods']}
        self.assertIn('lsp:textDocument/publishDiagnostics', identities)
        self.assertIn('lsp:$/lean/waitForILeans', identities)
        self.assertIn('rpc:Lean.Widget.InteractiveDiagnostics.msgToInteractive', identities)

    def test_wrong_blob_and_truncation_refuse(self):
        source = SOURCE.read_bytes()
        with self.assertRaisesRegex(ValueError, 'frozen release blob'):
            m.inventory(source, '0' * 40)
        truncated = source[:-3]
        with self.assertRaisesRegex(ValueError, 'ending'):
            m.inventory(truncated, blob(truncated))

    def test_unknown_records_duplicate_identities_and_missing_fields_refuse(self):
        source = SOURCE.read_bytes()
        for bad in [source.replace(b'  .notification {', b'  .unknown {', 1),
                    source.replace(b'method := "initialized"', b'method := "exit"', 1),
                    source.replace(b'    parameterType := CancelParams\n', b'', 1)]:
            with self.assertRaises(ValueError):
                m.inventory(bad, blob(bad))

    def test_default_and_explicit_historical_profile_preserve_exact_frozen_bytes(self):
        frozen = (SOURCE.parent / 'methods.json').read_bytes()
        with tempfile.TemporaryDirectory() as tmp:
            for flags in ([], ['--profile', 'v4.35.0']):
                output = Path(tmp) / 'methods.json'
                command = [*PYTHON, str(SCRIPT), '--source', str(SOURCE),
                           '--tree', str(BASE_TREE), '--output', str(output), *flags]
                result = subprocess.run(command, capture_output=True, text=True)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(output.read_bytes(), frozen)

    def test_latest_profile_matches_the_actual_overview_and_stays_unqualified(self):
        report, _ = m.from_paths(TARGET / 'ProtocolOverview.lean', TARGET_TREE, 'v4.36.0')
        self.assertEqual(report['upstream_revision'], '611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9')
        self.assertEqual(report['source_git_blob'], 'ddd3587f89804c5c05e49b9b7432514066266322')
        self.assertEqual(report['total'], 59)
        self.assertEqual(report['counts'], {'notification': 12, 'request': 37, 'rpcRequest': 10})
        self.assertEqual(report['qualified'], 0)
        self.assertEqual(report['methods'], json.loads((SOURCE.parent / 'methods.json').read_text())['methods'])
        self.assertTrue(all(row['qualification'] == 'not-measured' for row in report['methods']))
        lines = (TARGET / 'ProtocolOverview.lean').read_text().splitlines()
        for row in report['methods']:
            self.assertEqual(lines[row['source_line'] - 1], '  .' + row['kind'] + ' {')
        self.assertEqual((json.dumps(report, indent=2) + '\n').encode(), (TARGET / 'methods.json').read_bytes())

    def test_tree_and_profile_mismatches_refuse(self):
        with self.assertRaisesRegex(ValueError, 'unreviewed protocol profile'):
            m.inventory(SOURCE.read_bytes(), blob(SOURCE.read_bytes()), 'v4.37.0')
        with self.assertRaisesRegex(ValueError, 'wrong or incomplete'):
            m.from_paths(SOURCE, BASE_TREE, 'v4.36.0')
        tree = json.loads(gzip.decompress(TARGET_TREE.read_bytes()))
        cases = []
        for change in ('truncated', 'missing', 'duplicate', 'wrong-blob', 'wrong-type'):
            bad = copy.deepcopy(tree)
            selected = next(row for row in bad['tree'] if row['path'] == m.UPSTREAM_PATH)
            if change == 'truncated':
                bad['truncated'] = True
            elif change == 'missing':
                bad['tree'].remove(selected)
            elif change == 'duplicate':
                bad['tree'].append(copy.deepcopy(selected))
            elif change == 'wrong-blob':
                selected['sha'] = '0' * 40
            else:
                selected['type'] = 'tree'
            cases.append((change, bad))
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'tree.json'
            source = Path(tmp) / 'ProtocolOverview.lean'
            source.write_bytes((TARGET / 'ProtocolOverview.lean').read_bytes())
            for name, bad in cases:
                with self.subTest(name=name):
                    path.write_text(json.dumps(bad))
                    with self.assertRaises(ValueError):
                        m.from_paths(source, path, 'v4.36.0')
            path.write_text(json.dumps(tree))
            source.write_bytes(source.read_bytes() + b'-- changed\n')
            with self.assertRaisesRegex(ValueError, 'frozen release blob'):
                m.from_paths(source, path, 'v4.36.0')

    def real_pair(self):
        old, old_tree = m.from_paths(SOURCE, BASE_TREE)
        new, new_tree = m.from_paths(TARGET / 'ProtocolOverview.lean', TARGET_TREE, 'v4.36.0')
        return old, new, old_tree, new_tree

    def test_current_method_and_wire_source_delta_is_exact_and_unqualified(self):
        report = m.delta(*self.real_pair())
        self.assertEqual(report['method_changes'], {'unchanged': 59})
        self.assertEqual(report['wire_source_changes'], {'changed': 2, 'unchanged': 73})
        self.assertEqual([row['path'] for row in report['wire_sources'] if row['change'] == 'changed'], [
            'src/Lean/Server/FileWorker/SemanticHighlighting.lean',
            'src/Lean/Server/FileWorker/Utils.lean',
        ])
        self.assertEqual(report['semantic_cases_measured'], 0)
        self.assertEqual(report['qualified'], 0)
        self.assertTrue(all(row['qualification'] == 'not-measured'
                            for row in report['methods'] + report['wire_sources']))
        self.assertEqual((json.dumps(report, indent=2) + '\n').encode(), (TARGET / 'delta.json').read_bytes())

    def test_method_and_file_deltas_do_not_lose_added_removed_or_changed_rows(self):
        old, new, old_tree, new_tree = self.real_pair()
        new['methods'][0]['parameter_type'] = 'ChangedParameter'
        new['methods'].pop()
        added = copy.deepcopy(new['methods'][-1])
        added.update(id='rpc:Synthetic.added', method='Synthetic.added')
        new['methods'].append(added)
        new['counts'] = dict(m.Counter(row['kind'] for row in new['methods']))
        removed = next(row for row in new_tree['tree'] if row['path'] ==
                       'src/Lean/Widget/InteractiveDiagnostic.lean')
        new_tree['tree'].remove(removed)
        new_tree['tree'].append(dict(path='src/Lean/Widget/Synthetic.lean',
                                     type='blob', mode='100644', sha='1' * 40))
        report = m.delta(old, new, old_tree, new_tree)
        self.assertEqual(report['method_changes'], {'added': 1, 'changed': 1, 'removed': 1, 'unchanged': 57})
        changed = next(row for row in report['methods'] if row['change'] == 'changed')
        self.assertEqual(changed['changed_fields'], ['parameter_type'])
        self.assertEqual(report['wire_source_changes'], {'added': 1, 'changed': 2, 'removed': 1, 'unchanged': 72})
        self.assertEqual(report['qualified'], 0)

    def test_qualified_malformed_and_duplicate_method_ledgers_refuse(self):
        old, new, old_tree, new_tree = self.real_pair()
        for mutation in ('qualified', 'row-qualified', 'duplicate', 'count', 'schema', 'misbound'):
            bad = copy.deepcopy(new)
            if mutation == 'qualified':
                bad['qualified'] = 1
            elif mutation == 'row-qualified':
                bad['methods'][0]['qualification'] = 'passed'
            elif mutation == 'duplicate':
                bad['methods'].append(copy.deepcopy(bad['methods'][0]))
            elif mutation == 'count':
                bad['total'] -= 1
            elif mutation == 'schema':
                bad['schema'] = 'arbitrary'
            else:
                bad['methods'][0]['id'] = 'lsp:wrong'
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                m.delta(old, bad, old_tree, new_tree)
        with self.assertRaisesRegex(ValueError, 'unreviewed protocol comparison pair'):
            m.delta(old, new, old_tree, new_tree, target_profile='v4.35.0')

    def test_wire_source_scope_refuses_malformed_entries_and_missing_roots(self):
        tree = self.real_pair()[3]
        for mutation in ('duplicate', 'path', 'hash', 'type', 'mode', 'missing-root', 'truncated'):
            bad = copy.deepcopy(tree)
            entry = next(row for row in bad['tree'] if row['path'] == 'src/Lean/Data/Lsp.lean')
            if mutation == 'duplicate':
                bad['tree'].append(copy.deepcopy(entry))
            elif mutation == 'path':
                entry['path'] = 'src/Lean/Data/Lsp/../wrong.lean'
            elif mutation == 'hash':
                entry['sha'] = 'wrong'
            elif mutation == 'type':
                entry['type'] = 'commit'
            elif mutation == 'mode':
                entry['mode'] = '120000'
            elif mutation == 'truncated':
                bad['truncated'] = True
            else:
                bad['tree'].remove(entry)
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                m.wire_sources(bad, 'v4.36.0')

    def test_cli_comparison_regenerates_both_artifacts_and_rejects_partial_actions(self):
        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp) / 'methods.json'
            changes = Path(tmp) / 'delta.json'
            base = [*PYTHON, str(SCRIPT), '--profile', 'v4.36.0',
                    '--source', str(TARGET / 'ProtocolOverview.lean'), '--tree', str(TARGET_TREE),
                    '--output', str(output)]
            compare = ['--baseline-source', str(SOURCE), '--baseline-tree', str(BASE_TREE),
                       '--delta-output', str(changes)]
            result = subprocess.run(base + compare, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(output.read_bytes(), (TARGET / 'methods.json').read_bytes())
            self.assertEqual(changes.read_bytes(), (TARGET / 'delta.json').read_bytes())
            for flags in ([compare[0], compare[1]], compare[2:4], compare[4:],
                          compare[:4] + ['--delta-output', str(output)],
                          ['--profile', 'v4.37.0'],
                          ['--profile', 'v4.35.0'] + compare):
                output.write_bytes(b'inventory sentinel')
                changes.write_bytes(b'delta sentinel')
                result = subprocess.run(base + flags, capture_output=True, text=True)
                self.assertNotEqual(result.returncode, 0, flags)
                self.assertEqual(output.read_bytes(), b'inventory sentinel')
                self.assertEqual(changes.read_bytes(), b'delta sentinel')

    def test_explicit_empty_comparison_values_cannot_skip_the_requested_action(self):
        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp) / 'methods.json'
            changes = Path(tmp) / 'delta.json'
            base = [*PYTHON, str(SCRIPT), '--source', str(SOURCE), '--tree', str(BASE_TREE),
                    '--output', str(output)]
            complete = ['--baseline-source', str(SOURCE), '--baseline-tree', str(BASE_TREE),
                        '--delta-output', str(changes)]
            cases = []
            for value in ('', '   '):
                for index in (0, 2, 4):
                    cases.append([complete[index], value])
                    flags = complete.copy()
                    flags[index + 1] = value
                    cases.append(flags)
                cases.append(['--baseline-source', value, '--baseline-tree', value,
                              '--delta-output', value])
            for flags in cases:
                with self.subTest(flags=flags):
                    output.write_bytes(b'inventory sentinel')
                    changes.write_bytes(b'delta sentinel')
                    result = subprocess.run(base + flags, capture_output=True, text=True)
                    self.assertEqual(result.returncode, 2, result.stderr)
                    self.assertEqual(result.stdout, '')
                    self.assertEqual(output.read_bytes(), b'inventory sentinel')
                    self.assertEqual(changes.read_bytes(), b'delta sentinel')

    def test_invalid_comparison_paths_refuse_before_either_output_is_written(self):
        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp) / 'methods.json'
            changes = Path(tmp) / 'delta.json'
            base = [*PYTHON, str(SCRIPT), '--profile', 'v4.36.0',
                    '--source', str(TARGET / 'ProtocolOverview.lean'), '--tree', str(TARGET_TREE),
                    '--output', str(output)]
            complete = ['--baseline-source', str(SOURCE), '--baseline-tree', str(BASE_TREE),
                        '--delta-output', str(changes)]
            for index, value in [(1, str(Path(tmp) / 'missing.lean')), (1, tmp),
                                 (3, str(Path(tmp) / 'missing-tree.json')), (3, tmp),
                                 (5, tmp), (5, str(Path(tmp) / 'missing-dir/delta.json'))]:
                with self.subTest(index=index, value=value):
                    flags = complete.copy()
                    flags[index] = value
                    output.write_bytes(b'inventory sentinel')
                    changes.write_bytes(b'delta sentinel')
                    result = subprocess.run(base + flags, capture_output=True, text=True)
                    self.assertEqual(result.returncode, 2, result.stderr)
                    self.assertEqual(result.stdout, '')
                    self.assertEqual(output.read_bytes(), b'inventory sentinel')
                    self.assertEqual(changes.read_bytes(), b'delta sentinel')


if __name__ == '__main__':
    unittest.main()
