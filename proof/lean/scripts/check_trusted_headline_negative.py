#!/usr/bin/env python3
"""Paired semantic controls for the closed-form router and trusted headline.

Every public contract in the two new modules is covered. The original
statements compile together; each altered statement must then produce its own
semantic error. Wrong port, contact window and delay index also have explicit
pointwise counterexamples in the accepted batch. Compiler rejection alone is
not treated as a proof of a negated proposition.
"""
import argparse
import json
from pathlib import Path
import re
import subprocess
import tempfile

from lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[1]
MODULE = 'KernelR.TrustedHeadline'
PREFIX = f'''import {MODULE}
open KernelR.Hybrid
attribute [local instance] Classical.propDecidable
'''


def altered_router(name, *, port='2', window='160 ≤ time ∧ time < T + 1', index='n - i.val'):
    return f'''noncomputable def {name} (n : ℕ) (delay : ℕ → ℝ → ℝ)
    (T : ℝ) : Router (n + 1) := fun i time =>
  if i.val = 0 then [] else
    if {window} then
      [⟨⟨i.val - 1, by omega⟩, {port}, time + delay ({index}) time⟩] else []
'''


def controls():
    cases = []

    def add(name, good, bad, covers):
        assert good != bad, name
        cases.append(dict(name=name, good=good, bad=bad, covers=covers))

    root = '''example (n : ℕ) (delay : ℕ → ℝ → ℝ) (T time : ℝ) :
    explicitFiniteChainRouter n delay T 0 time = TOKENS := by
  exact explicitFiniteChainRouter_root n delay T time
'''
    add('root issues no token', root.replace('TOKENS', '[]'),
        root.replace('TOKENS', '[⟨0, 2, time⟩]'), ['explicitFiniteChainRouter_root'])
    parent = '''example (n : ℕ) (delay : ℕ → ℝ → ℝ)
    (T time : ℝ) (i : Fin (n + 1)) :
    explicitFiniteChainRouter (n + 1) delay T i.succ time =
      if WINDOW then [⟨i.castSucc, PORT, time + delay (INDEX) time⟩] else [] := by
  exact explicitFiniteChainRouter_parent n delay T time i
'''
    correct = parent.replace('WINDOW', '160 ≤ time ∧ time < T + 1').replace('PORT', '2').replace('INDEX', 'n - i.val')
    add('parent port two', correct, correct.replace('i.castSucc, 2,', 'i.castSucc, 1,'),
        ['explicitFiniteChainRouter_parent'])
    add('inclusive lower and exclusive upper contact bounds', correct,
        correct.replace('160 ≤ time ∧ time < T + 1', '160 < time ∧ time ≤ T + 1'),
        ['explicitFiniteChainRouter_parent'])
    add('leaf-indexed delivery delay', correct,
        correct.replace('delay (n - i.val)', 'delay (n + 1 - i.val)'),
        ['explicitFiniteChainRouter_parent'])
    eq = '''example (n : ℕ) (delay : ℕ → ℝ → ℝ) (T : ℝ) :
    canonicalFiniteChainRouter n delay T = ROUTER n delay T := by
  exact canonicalFiniteChainRouter_eq_explicit n delay T
'''
    for label, wrong in [('wrong port breaks router equality', 'wrongPortRouter'),
                         ('wrong contact window breaks router equality', 'wrongWindowRouter'),
                         ('wrong delay index breaks router equality', 'wrongDelayRouter')]:
        counterexample = f'''example :
    canonicalFiniteChainRouter 1 (fun j _ => (j : ℝ)) 200 (0 : Fin 1).succ 160 ≠
      {wrong} 1 (fun j _ => (j : ℝ)) 200 (0 : Fin 1).succ 160 := by
  rw [canonicalFiniteChainRouter_parent 0 (fun j _ => (j : ℝ)) 200 160 (0 : Fin 1)]
  norm_num [{wrong}]
'''
        add(label, eq.replace('ROUTER', 'explicitFiniteChainRouter') + counterexample,
            eq.replace('ROUTER', wrong), ['canonicalFiniteChainRouter_eq_explicit'])

    # Keep the expected contract anchored to the unchanged earlier theorem,
    # rather than regenerating it from the new headline being checked.
    source = (ROOT / 'KernelR/FixedDelayChainHeadline.lean').read_text()
    start = re.search(r'^theorem every_finite_chain_fixed_delay\b', source, re.M).end()
    end = re.search(r':=\s*by\b', source[start:]).start() + start
    signature = source[start:end].replace('canonicalFiniteChainRouter', 'explicitFiniteChainRouter')
    signature = signature.replace('(delay : ℕ → ℝ → ℝ)',
                                  '(delay otherDelay : ℕ → ℝ → ℝ)')
    proof = ''' := by
  exact TrustedHeadline.every_finite_chain
    hborn hb ha hqueue sigma centre delay hK hsigma hbudget hcentre herror
'''
    good = 'example' + signature + proof
    route = 'explicitFiniteChainRouter n delay (cadenceChainTerminal n K)'
    other = 'explicitFiniteChainRouter n otherDelay (cadenceChainTerminal n K)'
    assert signature.count(route) == 4
    add('both witnesses retain the supplied delay', good,
        'example' + signature.replace(route, other, 2) + proof, ['every_finite_chain'])
    chunks = signature.split(route)
    universal = route.join(chunks[:3]) + other + other.join(chunks[3:])
    assert universal.count(route) == 2 and universal.count(other) == 2
    add('both universal conclusions retain the supplied delay', good,
        'example' + universal + proof, ['every_finite_chain'])
    return cases


def check_inventory(cases):
    for module, expected in [('ExplicitFiniteChainRouter', {
            'canonicalFiniteChainRouter_eq_explicit', 'explicitFiniteChainRouter_root',
            'explicitFiniteChainRouter_parent'}), ('TrustedHeadline', {'every_finite_chain'})]:
        source = (ROOT / f'KernelR/{module}.lean').read_text()
        declared = set(re.findall(r'^(?:@\[[^\n]*\]\s*)?(?:protected\s+)?theorem\s+([\w.]+)',
                                  source, re.M))
        if declared != expected:
            raise SystemExit(f'{module}: public-contract inventory changed: {sorted(declared ^ expected)}')
    covered = {name for case in cases for name in case['covers']}
    expected = {'canonicalFiniteChainRouter_eq_explicit', 'explicitFiniteChainRouter_root',
                'explicitFiniteChainRouter_parent', 'every_finite_chain'}
    if covered != expected:
        raise SystemExit('Paired control coverage differs from the public contracts.')


def run(cases, timeout):
    prefix = PREFIX
    prefix += altered_router('wrongPortRouter', port='1')
    prefix += altered_router('wrongWindowRouter', window='160 < time ∧ time ≤ T + 1')
    prefix += altered_router('wrongDelayRouter', index='n + 1 - i.val')
    prefix += 'set_option maxErrors 0\n'
    with tempfile.TemporaryDirectory(prefix='trusted-headline-negative-', dir=ROOT) as tmp:
        path = Path(tmp) / 'Check.lean'
        command = lean_check_command(tmp, root_module=MODULE)
        for key in ['good', 'bad']:
            source = prefix
            blocks = []
            for case in cases:
                first = source.count('\n') + 1
                source += case[key].rstrip() + '\n\n'
                blocks.append((first, source.count('\n'), case['name']))
            path.write_text(source)
            result = subprocess.run([*command, str(path)], cwd=ROOT, text=True,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                    timeout=timeout)
            if key == 'good':
                if result.returncode:
                    raise SystemExit('Original trusted contracts failed:\n' + result.stdout)
                print(f'Accepted all {len(cases)} original controls and concrete counterexamples.', flush=True)
                continue
            if not result.returncode:
                raise SystemExit('Altered trusted contracts unexpectedly compiled.')
            if re.search(r'unknown (constant|identifier|tactic)|unexpected token|invalid syntax|'
                         r'invalid (field|dotted identifier)|failed to infer|'
                         r"don't know how to synthesize implicit|failed to synthesize|"
                         r'object file .* does not exist|unknown module prefix', result.stdout, re.I):
                raise SystemExit('Nonsemantic rejection:\n' + result.stdout)
            errors = list(re.finditer(r'^.*?:(\d+):(\d+): error(?:\([^\n]*\))?:', result.stdout, re.M))
            rejected = set()
            for error in errors:
                line = int(error.group(1))
                owners = [name for first, last, name in blocks if first <= line <= last]
                if len(owners) != 1:
                    raise SystemExit('Error outside an altered contract:\n' + result.stdout)
                rejected.add(owners[0])
            missing = {case['name'] for case in cases} - rejected
            if missing:
                raise SystemExit('Missing individual semantic rejection for: ' + ', '.join(sorted(missing)) +
                                 '\n' + result.stdout)
            for case in cases:
                print(f'{case["name"]}: original accepted; own mutation rejected.', flush=True)
    return [dict(case=case['name'], covers=case['covers'], positive='accepted', mutation='rejected')
            for case in cases]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--case', action='append', help='exact case label (repeatable)')
    parser.add_argument('--inventory', action='store_true')
    parser.add_argument('--report', type=Path)
    parser.add_argument('--timeout', type=int, default=240)
    args = parser.parse_args()
    cases = controls()
    check_inventory(cases)
    if args.inventory:
        print(json.dumps([{k: case[k] for k in ['name', 'covers']} for case in cases], indent=2))
        return
    if args.case:
        known = {case['name'] for case in cases}
        if set(args.case) - known:
            parser.error('unknown cases: ' + ', '.join(sorted(set(args.case) - known)))
        cases = [case for case in cases if case['name'] in args.case]
    report = run(cases, args.timeout)
    if args.report:
        args.report.write_text(json.dumps(report, indent=2) + '\n')
    print(f'All {len(cases)} paired trusted-headline controls passed.', flush=True)


if __name__ == '__main__':
    main()
