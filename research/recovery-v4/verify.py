#!/usr/bin/env python3
"""Proof/synthetic preparation and immutable evidence checks; never a trial."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parent.parent
R1 = ROOT.parent/'refusal-recovery'
from schema import DEPENDENCY, PROTOCOL

MUTATIONS = [
    ('root_ceiling_unjustified', 'def leakage (time : Nat) : Nat := if time < 661 then 10 else 140',
     'def leakage (time : Nat) : Nat := if time < 661 then 10 else 151'),
    ('understate_measurement_error', 'postDelivery pre delivered - 4 ≤ freshLower pre error delivered',
     'postDelivery pre delivered - 3 ≤ freshLower pre error delivered'),
    ('wrong_actual_policy_threshold', 'if 400 ≤ lower then post - 140 else min 660 (post - 140 + 220)',
     'if 399 ≤ lower then post - 140 else min 660 (post - 140 + 220)'),
    ('weaken_write_count_invariant', '(range : 260 ≤ finalPost ∧ finalPost ≤ 483)',
     '(range : 100 ≤ finalPost ∧ finalPost ≤ 483)'),
    ('spend_predelivery_reserve', '(ready : 260 ≤ post) : 100 ≤ post - 140',
     '(ready : 100 ≤ post) : 100 ≤ post - 140'),
]
SEMANTIC = re.compile(r'Type mismatch|unsolved goals|omega could not prove|Tactic `decide` proved', re.I)
BROKEN = re.compile(r'unexpected token|Unknown identifier|Unknown constant|unknown module|unknown package|object file .* does not exist|unknown tactic|failed to synthesize', re.I)


def run(args, cwd=ROOT):
    return subprocess.run(args, cwd=cwd, text=True, stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT, timeout=180)


def success(args, cwd=ROOT):
    r = run(args, cwd)
    if r.returncode or re.search(r'declaration uses.*sorry', r.stdout):
        raise RuntimeError(f'Positive check failed: {args}\n{r.stdout}')
    return r.stdout


def sources():
    return {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(ROOT.iterdir()) if p.is_file()
            and (p.suffix in ('.py', '.lean') or p.name == 'PREDICTION.md')}


def check_saved():
    from score_v4 import evaluate
    out = ROOT/'run-v4'
    if not out.is_dir():
        raise RuntimeError('Registered v4 evidence missing; only --preflight permits preparation checks')
    if (out/'exit-status.txt').read_text().strip() != '0':
        raise RuntimeError('Registered attempt failed; preserve and report it, never rerun')
    for name in ('stderr.txt', 'lean-stderr.txt'):
        if (out/name).read_bytes():
            raise RuntimeError('Nonempty registered error log: ' + name)
    import shutil
    with tempfile.TemporaryDirectory(prefix='v4-evidence-') as temp:
        dest = Path(temp)
        for p in out.iterdir():
            if p.name not in ('summary.json', 'REPORT.md'):
                shutil.copyfile(p, dest/p.name)
        summary = evaluate(dest)
        if summary['audit_issues'] or not all(summary['predictions'].values()):
            raise RuntimeError('Recorded evidence fails audit/predictions: ' + json.dumps(summary))
        for name in ('summary.json', 'REPORT.md'):
            if (out/name).read_bytes() != (dest/name).read_bytes():
                raise RuntimeError('Saved report was changed: ' + name)
    from score_v4 import load_rows
    from test_saved_controls import run_saved_controls
    controls = run_saved_controls(load_rows(out/'adaptive.csv'))
    print('PASS: saved v4 trace, authority, source hashes, predictions and unedited report')
    print('PASS: six saved-evidence semantic controls with valid replacement hash chains: ' + ', '.join(controls))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--preflight', action='store_true')
    parser.add_argument('--report', type=Path)
    args = parser.parse_args()
    if args.preflight and (ROOT/'run-v4').exists():
        raise RuntimeError('Preflight cannot bypass a registered attempt')
    frozen = ['self-certifying-learning', 'discrete-refresh-experiment', 'adaptive-refresh-experiment',
              'refresh-contract-rupture', 'refusal-recovery']
    if success(['git', 'diff', DEPENDENCY, '--', *['research/'+p for p in frozen]], REPO):
        raise RuntimeError('Frozen prerequisite changed')
    published = subprocess.check_output(['git', 'show', PROTOCOL+':research/recovery-v4/PREDICTION.md'], cwd=REPO)
    if published != (ROOT/'PREDICTION.md').read_bytes():
        raise RuntimeError('Published protocol changed')
    source = (ROOT/'Model.lean').read_text()
    if re.search(r'\b(sorry|admit|native_decide)\b|^\s*(?:private\s+)?(?:axiom|unsafe)\s', source, re.M):
        raise RuntimeError('Forbidden proof shortcut')
    success(['lake', 'build'], R1)
    audit = success(['lake', 'env', 'lean', str(ROOT/'Model.lean')], R1).strip()
    success(['lake', 'env', 'lean', str(ROOT.parent/'adaptive-refresh-experiment/Bridge.lean')],
            ROOT.parent/'self-certifying-learning')
    success(['python3', '-B', '-m', 'unittest', '-v', 'test_synthetic'])
    (ROOT/'.lake').mkdir(exist_ok=True)
    passed = []
    with tempfile.TemporaryDirectory(prefix='controls-', dir=ROOT/'.lake') as temp:
        path = Path(temp)/'Control.lean'
        for name, old, new in MUTATIONS:
            if source.count(old) != 1:
                raise RuntimeError('Nonunique mutation anchor: ' + name)
            path.write_text(source)
            success(['lake', 'env', 'lean', str(path)], R1)
            path.write_text(source.replace(old, new))
            r = run(['lake', 'env', 'lean', str(path)], R1)
            if r.returncode == 0 or BROKEN.search(r.stdout) or not SEMANTIC.search(r.stdout):
                raise RuntimeError('Mutation not rejected semantically: ' + name + '\n' + r.stdout)
            passed.append(name)
    if not args.preflight:
        check_saved()
    else:
        print('PREPARATION ONLY: registered trajectory has not been invoked')
    report = dict(protocol_commit=PROTOCOL, dependency_commit=DEPENDENCY, audit=audit,
                  synthetic_tests=9, semantic_controls=passed, sha256=sources())
    if args.report:
        args.report.write_text(json.dumps(report, indent=2)+'\n')
    print(audit)
    print(f'PASS: 9 isolated synthetic tests; {len(passed)} paired model mutations; frozen sources unchanged')


if __name__ == '__main__':
    main()
