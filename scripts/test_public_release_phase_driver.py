#!/usr/bin/env python3
"""Inert build/runtime phase routing; no Rust compilation or semantic grade."""
from pathlib import Path
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]

class PhaseDriverTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(); self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name) / 'owned fixture with spaces'
        scripts = self.root / 'scripts'; scripts.mkdir(parents=True)
        shutil.copy2(ROOT / 'scripts/check_public_release_libraries.sh', scripts)
        self.log = self.root / 'actual.jsonl'
        self.phases = self.root / 'phases.jsonl'
        self.env = dict(os.environ, PATH=os.pathsep.join([str(Path(sys.executable).parent), '/usr/bin', '/bin']),
                        FAKE_ACTUAL_LOG=str(self.log), FAKE_PHASE_LOG=str(self.phases),
                        CARGO_TARGET_DIR=str(self.root / 'target'))
        self.env.pop('CLEAN_PUBLIC_RELEASE_PHASE_DRIVER', None)
        self.env.pop('FAKE_FAIL', None)
        common = """import json,os,subprocess,sys
from pathlib import Path
def log(name,argv):
 with Path(os.environ[name]).open('a') as stream: stream.write(json.dumps(argv)+'\\n')
"""
        self.targo = self.executable(self.root / 'fake-targo', common + """
args=sys.argv[1:];log('FAKE_ACTUAL_LOG',['targo',*args])
if args[0]=='pkgid': print('fixture::'+args[-1])
else:
 if os.environ.get('FAKE_FAIL')=='build': sys.exit(23)
 for name in ['clean_kernel','clean_olean','clean_auto','clean_mathverse']:
  target=Path(os.environ['CARGO_TARGET_DIR'])/name;target.parent.mkdir(exist_ok=True)
  target.write_text("#!/bin/sh\\nprintf '%s\\\\n' '"+json.dumps(['runtime',name])+"' >> \\"$FAKE_ACTUAL_LOG\\"\\n")
  target.chmod(0o700)
  print(json.dumps({'reason':'compiler-artifact','target':{'name':name,'kind':['lib']},'profile':{'test':True},'executable':str(target)}))
""")
        self.driver = self.executable(self.root / 'phase-driver', common + """
kind,sep,*command=sys.argv[1:]
assert sep=='--' and kind in ['targo','runtime'] and command
log('FAKE_PHASE_LOG',[kind,*command])
if os.environ.get('FAKE_FAIL')=='driver':sys.exit(18)
if os.environ.get('FAKE_FAIL')=='runtime' and kind=='runtime':sys.exit(17)
sys.exit(subprocess.run(command).returncode)
""")
        self.executable(scripts / 'run_public_release_test_shards.py', common + "log('FAKE_ACTUAL_LOG',['shards',*sys.argv[1:]])\n")
        self.env['TARGO'] = str(self.targo)

    def executable(self, path, text):
        path.write_text('#!/usr/bin/env python3\n'+text);path.chmod(0o700);return path

    def run_helper(self, driver=None):
        env = dict(self.env)
        if driver is not None: env['CLEAN_PUBLIC_RELEASE_PHASE_DRIVER'] = str(driver)
        return subprocess.run(['/bin/sh', 'scripts/check_public_release_libraries.sh'], cwd=self.root,
                              env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=20)

    def rows(self, path):
        return [json.loads(line) for line in path.read_text().splitlines()] if path.exists() else []

    def test_default_and_phase_driver_keep_all_underlying_argv_and_order(self):
        direct = self.run_helper(); self.assertEqual(direct.returncode, 0, direct.stderr)
        before = self.rows(self.log); self.assertFalse(self.phases.exists())
        self.log.unlink()
        routed = self.run_helper(self.driver); self.assertEqual(routed.returncode, 0, routed.stderr)
        self.assertEqual(before, self.rows(self.log))
        phases = self.rows(self.phases)
        self.assertEqual([row[0] for row in phases], ['targo']*5+['runtime']*4)
        self.assertEqual(phases[4][2:6], ['--unverified','test','--locked','--lib'])
        self.assertEqual(phases[-1][-1], '--test-threads=4')

    def test_build_failure_stops_before_any_runtime(self):
        self.env['FAKE_FAIL'] = 'build'
        result = self.run_helper(self.driver)
        self.assertEqual(result.returncode, 23)
        self.assertEqual([row[0] for row in self.rows(self.phases)], ['targo']*5)

    def test_runtime_failure_stops_later_runtime_phases(self):
        self.env['FAKE_FAIL'] = 'runtime'
        result = self.run_helper(self.driver)
        self.assertEqual(result.returncode, 17)
        self.assertEqual([row[0] for row in self.rows(self.phases)], ['targo']*5+['runtime'])

    def test_driver_refusal_is_not_retried_without_driver(self):
        self.env['FAKE_FAIL'] = 'driver'
        result = self.run_helper(self.driver)
        self.assertEqual(result.returncode, 18)
        self.assertEqual(self.rows(self.log), [])
        self.assertEqual(len(self.rows(self.phases)), 1)

    def test_malformed_explicit_driver_refuses_before_build(self):
        link = self.root / 'driver-link'; link.symlink_to(self.driver)
        not_executable = self.root / 'plain';not_executable.write_text('no')
        for driver in ['', 'relative-driver', self.root / 'missing', self.root, link, not_executable]:
            with self.subTest(driver=str(driver)):
                result = self.run_helper(driver)
                self.assertEqual(result.returncode, 2, result.stderr)
                self.assertFalse(self.log.exists())
                self.assertFalse(self.phases.exists())

if __name__ == '__main__':
    unittest.main()
