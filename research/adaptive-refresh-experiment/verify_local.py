"""Proof and synthetic validation only; no registered comparison is executed."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
FOUNDATIONS = ROOT.parent / 'self-certifying-learning'


def run(args, cwd):
    result = subprocess.run(args, cwd=cwd, text=True, capture_output=True, timeout=120)
    return result.returncode, result.stdout + result.stderr


def main():
    source = (ROOT/'Bridge.lean').read_text()
    if re.search(r'\b(sorry|admit|native_decide|axiom|unsafe)\b', source):
        raise RuntimeError('Forbidden proof shortcut')
    code, output = run(['lake','env','lean',str(ROOT/'Bridge.lean')], FOUNDATIONS)
    if code or output.strip():
        raise RuntimeError(output)
    theorem_names = re.findall(r'^theorem (\w+)', source, re.M)
    checks = {
        'omit_variation_allowance': ('report + error + variation', 'report + error'),
        'omit_sensor_error': ('report + error + variation', 'report + variation'),
        'omit_handoff_buffer': ('Scheduler.plan lower (100 + u + 12) u 40', 'Scheduler.plan lower (100 + u) u 40'),
    }
    with tempfile.TemporaryDirectory(dir=FOUNDATIONS/'.lake', prefix='adaptive-proof-') as temp:
        path = Path(temp)/'Check.lean'
        path.write_text(source + '\n' + '\n'.join('#print axioms AdaptiveRefresh.'+n for n in theorem_names))
        code, output = run(['lake','env','lean',str(path)], FOUNDATIONS)
        if code:
            raise RuntimeError(output)
        for group in re.findall(r'axioms: \[([^]]*)\]', output):
            if set(group.replace(',',' ').split()) - {'propext','Classical.choice','Quot.sound'}:
                raise RuntimeError('Unexpected axioms: '+group)
        audit_output = output
        for name,(old,new) in checks.items():
            if source.count(old) != (2 if name == 'omit_handoff_buffer' else 1):
                raise RuntimeError('Mutation anchor '+name)
            path.write_text(source.replace(old,new))
            code, output = run(['lake','env','lean',str(path)], FOUNDATIONS)
            if not code or not re.search(r'unsolved goals|Type mismatch|omega could not prove', output, re.I):
                raise RuntimeError('Mutation not semantically rejected: '+name+'\n'+output)
            if re.search(r'Unknown identifier|unexpected token|unknown module',output,re.I):
                raise RuntimeError(output)
    code, output = run(['python3','-B','-m','unittest','-v','test_synthetic'], ROOT)
    if code:
        raise RuntimeError(output)
    print(output.strip())
    report = {'bridge_sha256':hashlib.sha256((ROOT/'Bridge.lean').read_bytes()).hexdigest(),
              'local_theorems':theorem_names,'axiom_audit':audit_output.strip(),
              'semantic_mutations_rejected':list(checks),'synthetic_tests':8,
              'registered_experiment_executed':False}
    (ROOT/'validation.json').write_text(json.dumps(report,indent=2)+'\n')
    print(f'PASS: {len(theorem_names)} local theorems, 3 semantic mutations, 8 synthetic tests; no registered run')


if __name__=='__main__':
    main()
