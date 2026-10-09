"""Shard coverage and genuine exit codes must remain authoritative."""
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from run_axiom_audit import shard_entries, run_shard
from report_verification import check_coverage


class AxiomShardTests(unittest.TestCase):
    def test_shards_cover_each_command_once_even_with_excess_jobs(self):
        entries = [{'name': 'N.a'}, {'name': 'N.b'}, {'name': 'N.c'}]
        for jobs in (1, 2, 8):
            groups = shard_entries(entries, ['N.c', 'N.a', 'N.b'], jobs)
            self.assertCountEqual([e['name'] for g in groups for e in g], ['N.a', 'N.b', 'N.c'])
            self.assertTrue(all(groups))

    def test_invalid_plan_is_rejected(self):
        entries = [{'name': 'N.a'}, {'name': 'N.b'}]
        for commands in (['N.a'], ['N.a', 'N.a'], ['N.a', 'N.extra']):
            with self.subTest(commands=commands), self.assertRaises(ValueError):
                shard_entries(entries, commands, 2)
        with self.assertRaises(ValueError):
            shard_entries(entries, ['N.a', 'N.b'], 0)

    def shard(self, output, code):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        directory = Path(temp.name)
        runner = (sys.executable, '-c', f'print({output!r}); raise SystemExit({code})')
        result = run_shard(directory, 1, [{'name': 'N.a'}], runner)
        self.assertEqual(result, json.loads((directory / 'Shard01.json').read_text()))
        return result

    def test_success_text_cannot_hide_failed_process(self):
        result = self.shard("'N.a' does not depend on any axioms", 7)
        self.assertEqual(result['exit_code'], 7)
        self.assertFalse(result['strict_coverage'])

    def test_missing_extra_and_forbidden_dependencies_fail_the_shard(self):
        for output in ('', "'N.extra' does not depend on any axioms",
                       "'N.a' depends on axioms: [sorryAx]"):
            with self.subTest(output=output):
                result = self.shard(output, 0)
                self.assertEqual(result['exit_code'], 1)
                self.assertFalse(result['strict_coverage'])

    def test_allowed_dependencies_are_certified(self):
        result = self.shard("'N.a' depends on axioms: [propext, Classical.choice, Quot.sound]", 0)
        self.assertEqual(result['exit_code'], 0)
        self.assertTrue(result['strict_coverage'])
        self.assertEqual(len(result['axioms']), 3)


if __name__ == '__main__':
    unittest.main()
