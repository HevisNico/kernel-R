#!/usr/bin/env python3
"""Emit exact endpoint proofs; neither this emitter nor its inputs are trusted by Lean.

Integer replay checks source identities and enclosures independently. The remaining
analytic refinement and transcendental soundness obligations are documented in
ROBUST_COVERAGE.md.
"""
from pathlib import Path
from fractions import Fraction
import argparse
import hashlib
import json
import re
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parents[1]
SNAPSHOT = REPO / 'research/robust'
sys.path.insert(0, str(SNAPSHOT))
from birth.verify import verify as verify_birth
from latency.verify import verify as verify_latency


def ident(name):
    return re.sub('[^A-Za-z0-9_]', '_', name)


def rational(value):
    if type(value) is not str:
        raise ValueError('endpoint must be an exact string')
    q = Fraction(value)
    return f'({q.numerator} / {q.denominator} : ℚ)'


def generate(output):
    provenance = {}
    modules = []
    for kind, verify in [('birth', verify_birth), ('latency', verify_latency)]:
        paths = sorted((SNAPSHOT / kind / 'certificates').glob('*.json'))
        if len(paths) != 8:
            raise ValueError('expected exactly eight parameter points per layer')
        for index, path in enumerate(paths):
            verify(path, emit=False)
            data = json.loads(path.read_text())
            module = kind.title() + str(index)
            names = [ident(n) for n in data['bounds']]
            checks = [ident(o['name']) for o in data['obligations']]
            if len(set(names)) != len(names) or len(set(checks)) != len(checks):
                raise ValueError('Lean identifiers collide')
            lines = ['import KernelR.Intervals', '',
                '/-! Generated rational endpoint checks; analytic enclosure membership is separate. -/',
                f'namespace KernelR.Robust.Evidence.{module}',
                'set_option maxRecDepth 20000', 'set_option maxHeartbeats 4000000', '']
            for name, (low, high) in data['bounds'].items():
                n = ident(name)
                lines += [f'def {n} : RationalBox := ⟨{rational(low)}, {rational(high)}⟩',
                    f'theorem {n}_valid : {n}.Valid := by norm_num [RationalBox.Valid, {n}]', '']
            statements, proofs = [], []
            for ob in data['obligations']:
                if ob['relation'] != 'strict_lt':
                    raise ValueError('unexpected relation')
                name, left, right = (ident(ob[k]) for k in ('name', 'left', 'right'))
                prop = f'RationalBox.StrictBefore {left} {right}'
                statements.append(prop)
                proofs.append(name + '_verified')
                lines += [f'theorem {name}_verified : {prop} := by',
                    f'  norm_num [RationalBox.StrictBefore, {left}, {right}]', '']
            lines += ['def Obligations : Prop :=', '  ' + ' ∧\n  '.join(statements),
                'theorem obligations_verified : Obligations := by',
                '  exact ⟨' + ', '.join(proofs) + '⟩', '',
                f'end KernelR.Robust.Evidence.{module}', '']
            relative = Path('KernelR/Robust/Evidence') / (module + '.lean')
            target = output / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text('\n'.join(lines))
            modules.append('KernelR.Robust.Evidence.' + module)
            provenance[str(path.relative_to(REPO))] = {
                'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
                'parameters': data['parameters'], 'bounds': len(names),
                'obligations': len(proofs), 'module': modules[-1]}
    (output / 'KernelR/Robust/Evidence.lean').write_text(
        '\n'.join('import ' + m for m in modules) + '\n')
    (output / 'evidence').mkdir(exist_ok=True)
    (output / 'evidence/ROBUST_GENERATED_FROM.json').write_text(
        json.dumps(provenance, indent=2, sort_keys=True) + '\n')
    return len(provenance)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    if args.check:
        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp)
            count = generate(output)
            expected = set()
            for path in output.rglob('*'):
                if path.is_file():
                    relative = path.relative_to(output)
                    expected.add(relative)
                    if not (ROOT / relative).exists() or path.read_bytes() != (ROOT / relative).read_bytes():
                        raise SystemExit(f'stale generated evidence: {relative}')
            actual = {p.relative_to(ROOT) for p in (ROOT / 'KernelR/Robust/Evidence').glob('*.lean')}
            if not actual <= expected:
                raise SystemExit('unexpected generated module')
    else:
        count = generate(ROOT)
    print(f'{count} robust certificates replayed; generated Lean evidence matches.')


if __name__ == '__main__':
    main()
