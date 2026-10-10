"""Check exact stable Lean versions, including Lake's embedded Lean version."""
from pathlib import Path
import json
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from check_environment import check_executable_version, stable_lean_version
import check_environment
from report_verification import TOOLCHAIN, MATHLIB


class EnvironmentTests(unittest.TestCase):
    def test_expected_version_comes_from_stable_toolchain(self):
        self.assertEqual(stable_lean_version(TOOLCHAIN), '4.34.1')
        self.assertEqual(stable_lean_version('leanprover/lean4:v4.35.0'), '4.35.0')
        for toolchain in ('leanprover/lean4:nightly', 'leanprover/lean4:v4.34.1-rc1',
                          'leanprover/lean4:v4.34', 'other/lean4:v4.34.1'):
            with self.subTest(toolchain=toolchain), self.assertRaises(AssertionError):
                stable_lean_version(toolchain)

    def test_actual_lean_and_lake_version_formats(self):
        outputs = {
            'lean': 'Lean (version 4.34.1, x86_64-unknown-linux-gnu, Release)',
            'lake': 'Lake version 5.0.0-src+5045d00 (Lean version 4.34.1)',
        }
        for executable, output in outputs.items():
            with self.subTest(executable=executable):
                check_executable_version(executable, output, stable_lean_version(TOOLCHAIN))
        check_executable_version('lake', 'Lake version 5.0.0 (lean version 4.34.1)', '4.34.1')

    def test_wrong_old_and_extended_versions_are_rejected(self):
        for version in ('4.24.0', '4.34.0', '4.34.10', '4.34.1-rc1', '4.34.1+custom'):
            for executable, output in (
                    ('lean', f'Lean (version {version}, Release)'),
                    ('lake', f'Lake version 5.0.0 (Lean version {version})')):
                with self.subTest(executable=executable, version=version), self.assertRaises(AssertionError):
                    check_executable_version(executable, output, '4.34.1')

    def test_missing_or_conflicting_lean_version_is_rejected(self):
        for output in ('', 'Lake version 4.34.1', 'version 4.34.1',
                       'Lake version 4.34.1 (Lean version 4.24.0)',
                       'Lake version 5.0.0 (Lean version 4.24.0)\nLean version 4.34.1'):
            with self.subTest(output=output), self.assertRaises(AssertionError):
                check_executable_version('lake', output, '4.34.1')

    def test_wrong_executable_kind_is_rejected(self):
        for executable, output in (
                ('lean', 'Lake version 5.0.0 (Lean version 4.34.1)'),
                ('lake', 'Lean (version 4.34.1, Release)')):
            with self.subTest(executable=executable), self.assertRaises(AssertionError):
                check_executable_version(executable, output, '4.34.1')


class LockedEnvironmentTests(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name)
        self.output = self.root / 'run'
        self.output.mkdir()
        (self.root / 'lean-toolchain').write_text(TOOLCHAIN + '\n')
        self.packages = [{'name': 'mathlib', 'rev': MATHLIB},
                         {'name': 'batteries', 'rev': 'a' * 40}]
        self.write_manifest()
        self.versions = {'lean': 'Lean (version 4.34.1, Release)',
                         'lake': 'Lake version 5.0.0-src+5045d00 (Lean version 4.34.1)'}
        self.revisions = {p['name']: p['rev'] for p in self.packages}
        self.statuses = {p['name']: '' for p in self.packages}

    def write_manifest(self):
        (self.root / 'lake-manifest.json').write_text(json.dumps(
            {'packagesDir': '.lake/packages', 'packages': self.packages}))

    def command_output(self, command, **kwargs):
        if command[0] == 'bash' and command[-1] == '--version':
            return self.versions[command[-2]] + '\n'
        package = Path(command[2]).name
        if command[3:] == ['rev-parse', 'HEAD']:
            return self.revisions[package] + '\n'
        self.assertEqual(command[3:], ['status', '--porcelain', '--untracked-files=no'])
        return self.statuses[package]

    def run_environment(self):
        with patch.object(check_environment, 'ROOT', self.root), \
                patch.object(sys, 'argv', ['check_environment.py', '--output-dir', str(self.output)]), \
                patch.object(check_environment.subprocess, 'check_output', side_effect=self.command_output), \
                patch('builtins.print'):
            check_environment.main()

    def test_actual_versions_and_all_locked_revisions_are_recorded(self):
        self.run_environment()
        result = json.loads((self.output / 'environment.json').read_text())
        self.assertEqual(result['lean_toolchain'], TOOLCHAIN)
        self.assertEqual(result['mathlib_revision'], MATHLIB)
        self.assertEqual(result['executable_versions'], self.versions)
        self.assertEqual(result['dependency_revisions'], self.revisions)

    def test_old_toolchain_and_wrong_mathlib_lock_are_rejected(self):
        (self.root / 'lean-toolchain').write_text('leanprover/lean4:v4.24.0\n')
        with self.assertRaisesRegex(AssertionError, 'Unexpected toolchain'):
            self.run_environment()
        (self.root / 'lean-toolchain').write_text(TOOLCHAIN + '\n')
        self.packages[0]['rev'] = '0' * 40
        self.write_manifest()
        with self.assertRaisesRegex(AssertionError, 'Unexpected mathlib lock'):
            self.run_environment()
        self.assertFalse((self.output / 'environment.json').exists())

    def test_unlocked_and_modified_transitive_dependencies_are_rejected(self):
        self.revisions['batteries'] = 'b' * 40
        with self.assertRaisesRegex(AssertionError, 'Unlocked checkout: batteries'):
            self.run_environment()
        self.revisions['batteries'] = 'a' * 40
        self.statuses['batteries'] = ' M lakefile.lean\n'
        with self.assertRaisesRegex(AssertionError, 'Modified dependency: batteries'):
            self.run_environment()
        self.assertFalse((self.output / 'environment.json').exists())


if __name__ == '__main__':
    unittest.main()
