"""Regression checks for missing names, duplicates, unsafe axioms and stale success."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from audit_sources import ROOT, inventory, mask_comments
from report_verification import check_coverage, certify


class AuditTests(unittest.TestCase):
    def project(self, code, aggregate=''):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        root = Path(temp.name)
        (root / 'ASGinzburg').mkdir()
        (root / 'ASGinzburg.lean').write_text(aggregate)
        (root / 'ASGinzburg/Test.lean').write_text(code)
        return root

    def test_dotted_name_comments_scopes_and_future_addition(self):
        root = self.project('/- theorem ignored /- nested -/ -/\nnamespace ASGinzburg.ZAlgebra\n'
                            'section\ndef InWindow := True\ntheorem InWindow.mono := True.intro\n'
                            'end\ntheorem added_later := True.intro\nend ASGinzburg.ZAlgebra\n')
        entries = inventory(root)
        self.assertEqual([e['name'] for e in entries], ['ASGinzburg.ZAlgebra.InWindow',
                         'ASGinzburg.ZAlgebra.InWindow.mono', 'ASGinzburg.ZAlgebra.added_later'])
        self.assertEqual(entries[1]['line'], 5)

    def test_duplicate_sources_rejected(self):
        with self.assertRaisesRegex(ValueError, 'Duplicate'):
            inventory(self.project('theorem N.x := True.intro\ntheorem N.x := True.intro\n'))

    def test_unsupported_theorem_rejected(self):
        with self.assertRaisesRegex(ValueError, 'Unsupported declaration'):
            inventory(self.project('private theorem hidden := True.intro\n'))

    def test_aggregate_placeholder_rejected(self):
        with self.assertRaisesRegex(ValueError, 'Unchecked'):
            inventory(self.project('def x := 0\n', 'example : True := by sorry\n'))

    def test_nested_comments_strings_and_placeholders(self):
        self.assertNotIn('sorry', mask_comments('/- /- sorry -/ admit -/\n"axiom" -- sorry\n'))
        for keyword in ('sorry', 'admit', 'axiom'):
            with self.subTest(keyword=keyword), self.assertRaisesRegex(ValueError, 'Unchecked'):
                inventory(self.project(f'def x := {keyword}\n'))

    def test_duplicate_inventory_and_logs_rejected(self):
        entries = [{'name': 'N.a'}, {'name': 'N.b'}]
        a = "'N.a' does not depend on any axioms\n"
        b = "'N.b' depends on axioms: [propext]\n"
        for targets, log in (([entries[0], entries[0]], a+a), (entries, a+a), (entries, a+b+b)):
            with self.subTest(log=log), self.assertRaisesRegex(ValueError, 'Duplicate'):
                check_coverage(targets, log)

    def test_missing_extra_and_malformed_log_rejected(self):
        for log in ('', "'N.b' does not depend on any axioms\n", 'unexpected output\n'):
            with self.subTest(log=log), self.assertRaises(ValueError):
                check_coverage([{'name': 'N.a'}], log)

    def test_allowed_and_forbidden_axioms(self):
        _, axioms = check_coverage([{'name': 'N.a'}],
            "'N.a' depends on axioms: [propext, Classical.choice, Quot.sound]\n")
        self.assertEqual(len(axioms), 3)
        names, _ = check_coverage([{'name': "N.a'"}], "'N.a'' does not depend on any axioms\n")
        self.assertEqual(names, ["N.a'"])
        for axiom in ('sorryAx', 'Lean.ofReduceBool', 'Lean.trustCompiler', 'customAxiom'):
            with self.subTest(axiom=axiom), self.assertRaisesRegex(ValueError, 'Unaccepted'):
                check_coverage([{'name': 'N.a'}], f"'N.a' depends on axioms: [{axiom}]\n")

    def test_completed_run_cannot_be_reused(self):
        root = self.project('def x := 0\n')
        run_dir = root / 'previous-run'
        run_dir.mkdir()
        (run_dir / 'run.json').write_text(json.dumps({'run_id': run_dir.name, 'status': 'success'}))
        with self.assertRaisesRegex(ValueError, 'active run'):
            certify(run_dir, root)

    def test_failed_build_exit_propagates_despite_success_text(self):
        root = self.project('def x := 0\n')
        shutil.copytree(ROOT / 'scripts', root / 'scripts', ignore=shutil.ignore_patterns('__pycache__'))
        # Isolate the runner's exit plumbing from actual Lean and dependency setup.
        (root / 'scripts/check_environment.py').write_text('import os\nassert "GITHUB_OUTPUT" not in os.environ\nprint("test environment stub")\n')
        (root / 'scripts/with_lean.sh').write_text('echo "Build completed successfully (old text)"\nexit 7\n')
        (root / 'tests').mkdir()
        (root / 'tests/test_fixture.py').write_text('import unittest\nclass Fixture(unittest.TestCase):\n    def test_fixture(self):\n        pass\n')
        subprocess.run(['git', 'init', '-q', str(root)], check=True)
        subprocess.run(['git', '-C', str(root), 'add', '.'], check=True)
        subprocess.run(['git', '-C', str(root), '-c', 'user.name=Audit test', '-c', 'user.email=audit@example.invalid',
                        'commit', '-qm', 'fixture'], check=True)
        (root / 'verification').mkdir()
        (root / 'verification/results.json').write_text('{"build_success": true}\n')
        output = root / 'github-output'
        process = subprocess.run(['bash', 'scripts/check.sh'], cwd=root, capture_output=True, text=True,
                                 env={**os.environ, 'GITHUB_OUTPUT': str(output)})
        self.assertEqual(process.returncode, 7, process.stdout + process.stderr)
        result = json.loads((root / 'verification/results.json').read_text())
        self.assertFalse(result['verification_success'])
        self.assertEqual(result['stage_exit_codes']['build'], 7)
        self.assertNotIn('axioms', result['stage_exit_codes'])
        self.assertIn('Not executed', (root / 'verification/axioms.log').read_text())
        latest = json.loads((root / 'verification/latest.json').read_text())
        self.assertEqual(output.read_text(), f"run_dir={latest['path']}\n")


if __name__ == '__main__':
    unittest.main()
