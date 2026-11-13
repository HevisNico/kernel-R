#!/usr/bin/env python3
"""Check the isolated learner; never run a plant or statistical campaign."""
from pathlib import Path
import argparse
import hashlib
import json
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
MUTATIONS = [
    ('fit_lower_instead_of_upper', ['Envelope'], 'next.interval.hi - old.interval.lo',
     'next.interval.lo - old.interval.lo'),
    ('forget_older_observations', ['Envelope'], '(demand horizon rest next)\n', '0\n'),
    ('false_demonstrated_refutation', ['Envelope'],
     'decide (old.interval.hi + bound < next.interval.lo)',
     'decide (old.interval.hi + bound < next.interval.hi)'),
    ('clamp_instead_of_exhaust', ['Envelope'],
     'if widen bound needed ≤ cap then some (widen bound needed) else none',
     'some (min cap (widen bound needed))'),
    ('free_observation_attempt', ['Learner'],
     'attempts := s.attempts + 1 }', 'attempts := s.attempts }'),
    ('uncounted_refinement', ['Learner', 'Window'],
     'refinements := s.refinements + 1, annotations', 'refinements := s.refinements, annotations'),
    ('training_sample_counted_as_validation', ['Learner', 'Window'],
     'remaining := p.window, windowStart := sample.time, refinements',
     'remaining := p.window - 1, windowStart := sample.time, refinements'),
    ('skip_validation_tick', ['Learner', 'Window'],
     'mode := .validating, nextTime := sample.time + 1,',
     'mode := .validating, nextTime := sample.time + 2,'),
    ('accept_wrong_observation_time', ['Learner', 'Window'],
     'if p.Valid ∧ sample.time = s.nextTime then', 'if p.Valid ∧ True then'),
    ('erase_old_annotation', ['Learner'],
     'refinements := s.refinements + 1, annotations := record :: s.annotations',
     'refinements := s.refinements + 1, annotations := [record]'),
    ('claim_future_guarantee', ['Learner'],
     'def futureGuarantee (_ : EmpiricalProposal) : Bool := false',
     'def futureGuarantee (_ : EmpiricalProposal) : Bool := true'),
]
SEMANTIC = re.compile(r'Type mismatch|unsolved goals|omega could not prove|Tactic `decide` proved', re.I)
BROKEN = re.compile(r'unexpected token|Unknown identifier|Unknown constant|unknown module|unknown package|object file .* does not exist|unknown tactic|failed to synthesize', re.I)


def run(args):
    return subprocess.run(args, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT, timeout=180)


def success(args):
    r = run(args)
    if r.returncode or re.search(r'declaration uses.*sorry', r.stdout):
        raise RuntimeError(f'Positive check failed: {args}\n{r.stdout}')
    return r.stdout


def combined(modules):
    imports, bodies = [], []
    internal = {'LearnedVariation.' + module for module in modules}
    for module in modules:
        source = (ROOT / 'LearnedVariation' / (module + '.lean')).read_text()
        for dep in re.findall(r'^import (\S+)$', source, re.M):
            if dep not in internal and dep not in imports:
                imports.append(dep)
        bodies.append(re.sub(r'^import \S+\n', '', source, flags=re.M))
    return '\n'.join('import ' + dep for dep in imports) + '\n' + '\n'.join(bodies)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--report', type=Path)
    args = parser.parse_args()
    modules = sorted((ROOT / 'LearnedVariation').glob('*.lean'))
    expected = {'import LearnedVariation.' + p.stem for p in modules}
    if set((ROOT / 'LearnedVariation.lean').read_text().splitlines()) != expected or len(modules) != 6:
        raise RuntimeError('Incomplete root-module audit coverage')
    for path in [*modules, ROOT / 'Audit.lean', ROOT / 'Bridge.lean']:
        if re.search(r'\b(sorry|admit|native_decide)\b|^\s*(?:private\s+)?(?:axiom|unsafe)\s', path.read_text(), re.M):
            raise RuntimeError('Forbidden proof shortcut: ' + path.name)
    frozen = ['self-certifying-learning', 'discrete-refresh-experiment', 'adaptive-refresh-experiment',
              'refresh-contract-rupture', 'refusal-recovery']
    if success(['git', 'diff', 'c6684f796d092b2324489cb9920f78a9fcca7a5a', '--',
                *['../' + name for name in frozen]]):
        raise RuntimeError('Frozen prerequisite sources or evidence changed')
    success(['lake', 'build'])
    audit = success(['lake', 'env', 'lean', 'Audit.lean']).strip()
    success(['python3', '-B', '-m', 'unittest', '-v', 'test_synthetic'])
    passed = []
    with tempfile.TemporaryDirectory(prefix='semantic-', dir=ROOT / '.lake') as temp:
        path = Path(temp) / 'Control.lean'
        for label, modules, old, new in MUTATIONS:
            source = combined(modules)
            if source.count(old) != 1:
                raise RuntimeError('Nonunique mutation anchor: ' + label)
            path.write_text(source)
            success(['lake', 'env', 'lean', str(path)])
            path.write_text(source.replace(old, new))
            r = run(['lake', 'env', 'lean', str(path)])
            if r.returncode == 0 or BROKEN.search(r.stdout) or not SEMANTIC.search(r.stdout):
                raise RuntimeError('Mutation not rejected semantically: ' + label + '\n' + r.stdout)
            passed.append(label)
    sources = sorted(p for p in ROOT.rglob('*') if p.is_file()
                     and '.lake' not in p.parts and '__pycache__' not in p.parts
                     and p.name != 'validation.json')
    report = {'toolchain': (ROOT / 'lean-toolchain').read_text().strip(), 'audit': audit,
              'synthetic_tests': 9, 'semantic_controls': passed,
              'scope': 'Sampled envelope learner and prospective validation; no physical future guarantee.',
              'sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sources}}
    if args.report:
        args.report.write_text(json.dumps(report, indent=2) + '\n')
    print(audit)
    print(f'PASS: 9 stream tests; {len(passed)} paired semantic mutations; prerequisites unchanged')


if __name__ == '__main__':
    main()
