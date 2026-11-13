#!/usr/bin/env python3
"""Compile, audit and reject paired semantic mutations; no campaign runner."""
from pathlib import Path
import argparse
import hashlib
import json
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
MUTATIONS = [
    ('dishonest_sample', 'Machine', '(honest : before h r ≤ pre)\n    (claimed',
     '(honest : before h r ≤ pre + 1)\n    (claimed'),
    ('stale_probe', 'Machine', 'r.time = s.now ∧ r.delivered = s.pending',
     'True ∧ r.delivered = s.pending'),
    ('negative_entry', 'Machine', '0 ≤ after h r ∧ (config h p).Valid',
     'True ∧ (config h p).Valid'),
    ('expired_phase', 'Machine', 's.now + phaseSpan h r p ≤ p.expires',
     's.now ≤ p.expires'),
    ('unfunded_repair', 'Machine', '| 0 => .exhausted', '| 0 => .repair'),
    ('missing_probe_tick', 'Machine', '⟨s.generation, s.now + 1, true⟩',
     '⟨s.generation, s.now + 2, true⟩'),
    ('clipped_signed_entry', 'Restoration', 'signedPulses capacity gain n lower ≤ state n := by',
     'signedPulses capacity gain n (max 0 lower) ≤ state n := by'),
    ('undersized_capacity', 'Restoration', '(nonnegative : 0 ≤ gain) (room : target ≤ capacity) (n : Nat) (lower : Int) :',
     '(nonnegative : 0 ≤ gain) (room : True) (n : Nat) (lower : Int) :'),
    ('zero_progress', 'Restoration', '(gain target lower : Int) (positive : 0 < gain) :',
     '(gain target lower : Int) (positive : 0 ≤ gain) :'),
    ('missing_dose', 'Restoration', '(delivered : min capacity (initial - loss + dose) ≤ final)',
     '(delivered : min capacity (initial - loss) ≤ final)'),
    ('ignore_new_violation', 'Runtime', 'rateLower ≤ p.bound\n', 'True\n'),
    ('active_expiry_at_dispatch_only', 'Runtime',
     's.now + ClosedLoop.duration (config h p) a ≤ p.expires then a else .refuse',
     's.now ≤ p.expires then a else .refuse'),
]
SEMANTIC = re.compile(r'Type mismatch|unsolved goals|omega could not prove|Tactic `decide` proved', re.I)
BROKEN = re.compile(r'unexpected token|Unknown identifier|Unknown constant|unknown module|unknown package|object file .* does not exist|unknown tactic|failed to synthesize', re.I)


def run(args):
    return subprocess.run(args, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT, timeout=180)


def success(args):
    result = run(args)
    if result.returncode or re.search(r'declaration uses.*sorry', result.stdout):
        raise RuntimeError(f'Positive check failed: {args}\n{result.stdout}')
    return result.stdout


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--report', type=Path)
    args = parser.parse_args()
    proof_files = sorted((ROOT / 'RefusalRecovery').glob('*.lean'))
    imports = {f'import RefusalRecovery.{p.stem}' for p in proof_files}
    if set((ROOT / 'RefusalRecovery.lean').read_text().splitlines()) != imports or len(imports) != 4:
        raise RuntimeError('Root module must cover exactly every maintained module')
    for path in [*proof_files, ROOT / 'Audit.lean', ROOT / 'Bridge.lean']:
        if re.search(r'\b(sorry|admit|native_decide)\b|^\s*(?:private\s+)?(?:axiom|unsafe)\s', path.read_text(), re.M):
            raise RuntimeError('Forbidden shortcut: ' + path.name)
    frozen = ['research/self-certifying-learning', 'research/discrete-refresh-experiment',
              'research/adaptive-refresh-experiment', 'research/refresh-contract-rupture']
    changed = success(['git', 'diff', 'a9e7280d403893b2ccc58b37132c2bd5302857eb', '--',
                       *['../../' + p for p in frozen]])
    if changed:
        raise RuntimeError('Frozen dependencies/evidence changed')
    success(['lake', 'build'])
    audit = success(['lake', 'env', 'lean', 'Audit.lean']).strip()
    success(['python3', '-B', '-m', 'unittest', '-v', 'test_synthetic'])
    passed = []
    with tempfile.TemporaryDirectory(prefix='semantic-', dir=ROOT / '.lake') as temp:
        path = Path(temp) / 'Control.lean'
        for label, module, old, new in MUTATIONS:
            source = (ROOT / 'RefusalRecovery' / (module + '.lean')).read_text()
            if source.count(old) != 1:
                raise RuntimeError('Mutation anchor is not unique: ' + label)
            path.write_text(source)
            success(['lake', 'env', 'lean', str(path)])
            path.write_text(source.replace(old, new))
            result = run(['lake', 'env', 'lean', str(path)])
            if result.returncode == 0 or BROKEN.search(result.stdout) or not SEMANTIC.search(result.stdout):
                raise RuntimeError('Mutation did not fail semantically: ' + label + '\n' + result.stdout)
            passed.append(label)
    sources = sorted(p for p in ROOT.rglob('*') if p.is_file()
                     and '.lake' not in p.parts and '__pycache__' not in p.parts
                     and p.name != 'validation.json')
    report = {'toolchain': (ROOT / 'lean-toolchain').read_text().strip(),
              'audit': audit, 'synthetic_tests': 9, 'semantic_controls': passed,
              'scope': 'Local Lean kernels and tested Python orchestration; no empirical campaign.',
              'sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sources}}
    if args.report:
        args.report.write_text(json.dumps(report, indent=2) + '\n')
    print(audit)
    print(f'PASS: 9 synthetic tests; {len(passed)} paired semantic mutations; frozen sources unchanged')


if __name__ == '__main__':
    main()
