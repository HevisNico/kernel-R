#!/usr/bin/env python3
"""Record exact CI measurements after the complete regression sequence.

The artifact pins the PR head and the tested merge commit separately. A Git
commit cannot contain its own SHA in a checked-in ledger; this generated
record supplies that final-commit reference without a self-referential edit.
The checked-in ledger links the generated record and its fixed code snapshot.
"""
import argparse
import json
from pathlib import Path
import re
import subprocess

import check_trusted_base_negative as base_controls
import check_trusted_headline_negative as headline_controls

ROOT = Path(__file__).resolve().parents[1]


def run_log(command, target):
    with target.open('w') as output:
        result = subprocess.run(command, cwd=ROOT, stdout=output, stderr=subprocess.STDOUT)
    if result.returncode:
        raise SystemExit(target.read_text())
    return target.read_text()


def checked_pairs(path, expected):
    results = json.loads(path.read_text())
    if len(results) != expected or any(row.get('positive') != 'accepted' or
                                       row.get('mutation') != 'rejected' for row in results):
        raise SystemExit('Incomplete or failed paired-control report: ' + str(path))
    return len(results)


def measurements(build, audit):
    jobs = re.findall(r'Build completed successfully \((\d+) jobs\)', build)
    theorems = re.findall(r'Axiom audit passed: (\d+) project theorems', audit)
    headline_axioms = re.findall(
        r"'KernelR\.Hybrid\.TrustedHeadline\.every_finite_chain' depends on axioms: \[([^\]]*)\]", build)
    if not jobs or not theorems or not headline_axioms:
        raise SystemExit('Missing actual build/audit/headline measurements in captured logs.')
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    used = {name.strip() for name in headline_axioms[-1].split(',') if name.strip()}
    if not used <= allowed:
        raise SystemExit('Unexpected headline axiom in captured build log.')
    return int(jobs[-1]), int(theorems[-1]), sorted(used)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--head-commit', required=True)
    parser.add_argument('--build-commit', required=True)
    parser.add_argument('--output-directory', type=Path, required=True)
    parser.add_argument('--headline-report', type=Path, required=True)
    parser.add_argument('--base-report', type=Path, required=True)
    args = parser.parse_args()
    for value in [args.head_commit, args.build_commit]:
        if not re.fullmatch(r'[0-9a-f]{40}', value):
            raise SystemExit('Validation references must be full commit SHAs.')
    actual = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    if actual != args.build_commit:
        raise SystemExit('The reported build commit is not the checked-out commit.')
    subprocess.run(['git', 'merge-base', '--is-ancestor', args.head_commit, actual], cwd=ROOT, check=True)
    out = args.output_directory
    out.mkdir(parents=True, exist_ok=True)
    run_log(['python', 'scripts/check_trusted_source_boundary.py'], out / 'source-boundary.log')
    # All targets already passed earlier in this workflow. Cached replays give
    # reproducible job/theorem totals without inferring them from file counts.
    build = run_log(['lake', 'build'], out / 'build.log')
    audit = run_log(['lake', 'build', 'Audit'], out / 'audit.log')
    jobs, theorems, used = measurements(build, audit)
    headline_count = checked_pairs(args.headline_report, len(headline_controls.controls()))
    base_count = checked_pairs(args.base_report, len(base_controls.controls()))
    files = sorted(ROOT.glob('*.lean')) + sorted((ROOT / 'KernelR').rglob('*.lean'))
    report = dict(
        scope='CI, after the full workflow regression sequence',
        head_commit=args.head_commit, build_commit=args.build_commit,
        build_jobs=dict(count=jobs, scope='CI cached replay of all default targets, including dependency jobs'),
        audited_theorems=dict(count=theorems, scope='CI global KernelR/A22 theorem audit'),
        lean_files=dict(count=len(files), scope='CI project Lean files; external packages excluded'),
        paired_controls=dict(count=headline_count + base_count,
                             scope='CI new trusted-headline/base suites only',
                             headline=headline_count, trusted_base=base_count),
        trusted_declarations=len(json.loads((ROOT / 'evidence/trusted_base.json').read_text())['trusted']),
        headline_axioms=sorted(used))
    (out / 'validation.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2), flush=True)


if __name__ == '__main__':
    main()
