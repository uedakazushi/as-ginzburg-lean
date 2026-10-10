#!/usr/bin/env python3
"""Check the actual Lean executable and each checked-out locked dependency."""
import argparse
import json
from pathlib import Path
import re
import subprocess
from audit_sources import ROOT
from report_verification import TOOLCHAIN, MATHLIB


def stable_lean_version(toolchain):
    match = re.fullmatch(r'leanprover/lean4:v(\d+\.\d+\.\d+)', toolchain)
    assert match, f'Expected a pinned stable Lean toolchain: {toolchain}'
    return match[1]


def check_executable_version(executable, output, expected):
    # Lake has its own version; its embedded Lean version must match the toolchain.
    assert re.match(rf'{re.escape(executable)}\b', output, re.I), \
        f'Unexpected {executable} executable: {output}'
    versions = re.findall(r'\bLean\s+(?:\(\s*)?version\s+([^\s,)]+)', output, re.I)
    assert versions == [expected], f'Unexpected {executable} executable: {output}'


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output-dir', type=Path, required=True)
    args = parser.parse_args()
    toolchain = (ROOT / 'lean-toolchain').read_text().strip()
    assert toolchain == TOOLCHAIN, f'Unexpected toolchain: {toolchain}'
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    mathlib = next(p for p in manifest['packages'] if p['name'] == 'mathlib')
    assert mathlib['rev'] == MATHLIB, 'Unexpected mathlib lock'
    expected_version = stable_lean_version(toolchain)
    wrapper = ['bash', str(ROOT / 'scripts/with_lean.sh')]
    versions = {}
    for exe in ('lean', 'lake'):
        version = subprocess.check_output([*wrapper, exe, '--version'], text=True).strip()
        check_executable_version(exe, version, expected_version)
        versions[exe] = version
    revisions = {}
    for package in manifest['packages']:
        path = ROOT / manifest['packagesDir'] / package['name']
        revision = subprocess.check_output(['git', '-C', str(path), 'rev-parse', 'HEAD'], text=True).strip()
        assert revision == package['rev'], f'Unlocked checkout: {package["name"]}'
        assert not subprocess.check_output(['git', '-C', str(path), 'status', '--porcelain', '--untracked-files=no'], text=True).strip(), f'Modified dependency: {package["name"]}'
        revisions[package['name']] = revision
    result = {'lean_toolchain': toolchain, 'mathlib_revision': mathlib['rev'],
              'executable_versions': versions, 'dependency_revisions': revisions}
    (args.output_dir / 'environment.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
