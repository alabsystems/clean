# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
import hashlib
import importlib.util
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('protocol_inventory', ROOT / 'scripts/replacement_protocol_inventory.py')
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
SOURCE = ROOT / 'reports/replacement-inventory-2026-11-12/protocol/ProtocolOverview.lean'


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


if __name__ == '__main__':
    unittest.main()
