"""Build/audit the certificate adapter and reject isolated semantic mutations.

Requires the pinned Lean toolchain and the existing native dependency build.
Mutant .oleans live only in temporary directories, never in the source tree.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
CONTROLLER = HERE.parent
NATIVE = CONTROLLER.parent / 'recursive-learning/native'
FILES = ['Counts.lean', 'Envelope.lean', 'Controller.lean', 'RecordedData.lean',
         'RecordedBridge.lean', 'Replay.lean', 'LogIntervals.lean', 'MeasuredGains.lean',
         'Readout.lean', 'RecordedGains.lean', 'ReadoutBridge.lean', 'IdealExample.lean']


def command(args, cwd=HERE, env=None, timeout=180):
    p = subprocess.run(args, cwd=cwd, env=env, capture_output=True, text=True, timeout=timeout)
    return p.returncode, p.stdout + p.stderr


def hashes():
    paths = [HERE / 'PhysicalEvaluator' / f for f in FILES]
    paths += [HERE / f for f in ['PhysicalEvaluator.lean', 'PhysicalAudit.lean', 'Trace.lean',
              'lakefile.toml', 'lake-manifest.json', 'lean-toolchain', 'verify_physical.py',
              'evidence_check.py', 'gain_check.py']]
    paths += sorted((HERE / 'evidence').iterdir())
    paths += sorted((CONTROLLER / 'ReusableController').glob('*.lean'))
    paths += [CONTROLLER / 'lakefile.toml', NATIVE / 'Search/VariableNeedTolerance.lean',
              NATIVE / 'Search/NeedTolerance.lean', NATIVE / 'lakefile.toml',
              NATIVE.parent / 'RecursiveLearning/Model.lean']
    return {os.path.relpath(p, HERE): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}


def replace_once(text, old, new):
    if text.count(old) != 1:
        raise RuntimeError('mutation anchor not unique: ' + old)
    return text.replace(old, new, 1)


def admit_accuracy(text):
    start = text.index('theorem accuracy_from_certificates')
    body = text.index(' := by', start)
    end = text.index('\nend ReusableController.PhysicalEvaluator', body)
    return text[:body] + ' := by\n  sorry\n' + text[end:]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lake', default='lake')
    parser.add_argument('--report', type=Path)
    args = parser.parse_args()
    located = shutil.which(args.lake)
    if not located:
        parser.error('lake not found')
    lake = str(Path(located).absolute())
    code, version = command([lake, 'env', 'lean', '--version'])
    if code or 'version 4.35.0' not in version:
        raise RuntimeError('wrong Lean toolchain: ' + version)
    before = hashes()
    code, log = command([lake, 'build'], timeout=3600)
    if code or 'Physical audit passed:' not in log:
        raise RuntimeError('positive build/audit failed:\n' + log)
    audit = next(line for line in log.splitlines() if 'Physical audit passed:' in line)
    print(audit, flush=True)
    code, lean = command([lake, 'env', 'which', 'lean'])
    if code:
        raise RuntimeError(lean)
    code, search = command([lake, 'env', 'printenv', 'LEAN_PATH'])
    if code:
        raise RuntimeError(search)
    search = os.pathsep.join(str((HERE / x).resolve()) for x in search.strip().split(os.pathsep))
    original = {f: (HERE / 'PhysicalEvaluator' / f).read_text() for f in FILES}
    mutations = [
        ('non_strict_room', 'Counts.lean', lambda s: replace_once(s,
            'ell + 1 / 8000 < dose0 / 2', 'ell + 1 / 8000 ≤ dose0 / 2'), None),
        ('missing_gain_bound', 'Counts.lean', lambda s: replace_once(s,
            'gainBound : |gain 0 - needCentre level0 dose0 m| ≤ a', 'gainBound : True'), None),
        ('missing_cumulative_bound', 'Counts.lean', lambda s: replace_once(s,
            'cumulativeBound : ∀ k, |gain k - gain 0 - (k.val : ℝ) * dose0| ≤ B',
            'cumulativeBound : True'), None),
        ('weaken_threshold_floor', 'Counts.lean', lambda s: replace_once(s,
            'levelFloor : 19 / 20 ≤ level0 - ell', 'levelFloor : 0 ≤ level0 - ell'), None),
        ('reverse_scalar_observation', 'Counts.lean', lambda s: replace_once(s,
            'scalarCorrespondence : ∀ k, observed k = true ↔',
            'scalarCorrespondence : ∀ k, observed k = false ↔'), None),
        ('shift_first_fire_count', 'Counts.lean', lambda s: replace_once(s,
            '| true :: _ => some 0', '| true :: _ => some 1'), None),
        ('reverse_envelope_detection', 'Envelope.lean', lambda s: replace_once(s,
            'observableSound : ∀ k, observed k = true →',
            'observableSound : ∀ k, observed k = false →'), None),
        ('missing_upper_envelope_completeness', 'Envelope.lean', lambda s: replace_once(s,
            'observableComplete : ∀ k,\n    PulseFires (charge k) (Real.exp (gain k)) (level0 + ell) → observed k = true',
            'observableComplete : True'), None),
        ('accept_missing_readout', 'Controller.lean', lambda s: replace_once(s,
            'let p ← firstFire preparation', 'let p := decodedCount preparation'), None),
        ('omit_acquisition_from_budget', 'Controller.lean', lambda s: replace_once(s,
            'acquisition + menu.count * fixed.validationBound F + F * lesson.cost + overhead * F := by',
            'menu.count * fixed.validationBound F + F * lesson.cost + overhead * F := by'), None),
        ('unused_physical_axiom', 'Counts.lean', lambda s: s + '\naxiom unusedPhysicalAxiom : True\n',
            'Unexpected project axiom'),
        ('admitted_derived_accuracy', 'Counts.lean', admit_accuracy, 'Unexpected axiom sorryAx'),
        ('reverse_response_normalization', 'MeasuredGains.lean', lambda s: replace_once(s,
            ':= y - Real.log (response 1)', ':= y + Real.log (response 1)'), None),
        ('omit_initial_readout_error', 'MeasuredGains.lean', lambda s: replace_once(s,
            '≤ Bhat + deltak + delta0 := by', '≤ Bhat + deltak := by'), None),
        ('halve_log_remainder', 'LogIntervals.lean', lambda s: replace_once(s,
            '2 * |logArgument x| ^ (2 * n + 1)', '|logArgument x| ^ (2 * n + 1)'), None),
        ('false_exponential_lower_bound', 'Readout.lean', lambda s: replace_once(s,
            '(60653065 / 100000000 : ℝ)', '(60653068 / 100000000 : ℝ)'), None),
    ]
    results = []
    for name, changed, mutate, audit_marker in mutations:
        with tempfile.TemporaryDirectory(prefix='physical-negative-') as td:
            folder = Path(td)
            shutil.copytree(HERE / '.lake/build/lib/lean/PhysicalEvaluator', folder / 'PhysicalEvaluator')
            # Lean resolves this prefix as a unit; the aggregate module must
            # accompany its children for the audit import to be meaningful.
            for artifact in (HERE / '.lake/build/lib/lean').glob('PhysicalEvaluator.*'):
                if artifact.is_file():
                    shutil.copy2(artifact, folder / artifact.name)
            relative = 'PhysicalEvaluator/' + changed
            (folder / relative).write_text(mutate(original[changed]))
            env = dict(os.environ, LEAN_PATH=str(folder) + os.pathsep + search)
            code, log = command([lean.strip(), '-o', relative.removesuffix('.lean') + '.olean', relative], folder, env)
            if audit_marker:
                if code:
                    raise RuntimeError(name + ': mutant must compile before audit:\n' + log)
                (folder / 'PhysicalAudit.lean').write_text((HERE / 'PhysicalAudit.lean').read_text())
                code, log = command([lean.strip(), 'PhysicalAudit.lean'], folder, env)
                rejected = code != 0 and audit_marker in log
            else:
                rejected = code != 0 and bool(re.search(re.escape(relative) + r':\d+:\d+: error:', log))
            malformed = any(x in log.lower() for x in ('unexpected token', 'unknown module',
                'unknown identifier', 'unexpected identifier', 'object file', 'does not exist', 'failed to load'))
            if not rejected or malformed:
                raise RuntimeError(name + ': not rejected by intended semantic check:\n' + log)
            results.append({'mutation': name, 'rejected': True, 'check': audit_marker or relative})
            print(name + ': rejected', flush=True)
    if hashes() != before:
        raise RuntimeError('original sources changed during validation')
    result = {'lean': version.strip(), 'positive_build': True, 'axiom_audit': audit,
              'negative_controls': results, 'source_sha256': before,
              'scope': 'Finite scalar certificates derive exact counts; conditional recorded-data adapter; commanded-pulse costs only.'}
    if args.report:
        args.report.write_text(json.dumps(result, indent=2) + '\n')
    print(f'All {len(results)} physical semantic mutations rejected; sources unchanged.', flush=True)


if __name__ == '__main__':
    main()
