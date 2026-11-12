"""CI entry point: verify saved evidence and synthetic/proof checks only.
Never imports or invokes an experiment runner or a trajectory function.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT=Path(__file__).resolve().parent
REPO=ROOT.parent.parent
V1=ROOT.parent/'discrete-refresh-experiment'
V2=ROOT.parent/'adaptive-refresh-experiment'
FOUNDATIONS=ROOT.parent/'self-certifying-learning'
FROZEN='09b8558fd41516de816544920b5c40315cf53a80'


def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    result=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def check_frozen():
    paths=['research/adaptive-refresh-experiment','research/discrete-refresh-experiment',
           'research/self-certifying-learning']
    difference=subprocess.check_output(['git','diff',FROZEN,'--',*paths],cwd=REPO)
    if difference: raise RuntimeError('Frozen v1/v2/foundation differs from audited snapshot')
    for base in (V1,V2):
        run=base/('run-v1' if base==V1 else 'run-v2')
        check_metadata(base,run)


def check_metadata(base,run):
    meta=json.loads((run/'metadata.json').read_text())
    if meta['git_status_before_run']!='': raise RuntimeError('Recorded run did not use clean source snapshot')
    for name,expected in meta['sha256'].items():
        if hashlib.sha256((base/name).read_bytes()).hexdigest()!=expected:
            raise RuntimeError('Source hash changed: '+str(base/name))
        rel=(base/name).relative_to(REPO).as_posix()
        executed=subprocess.check_output(['git','show',meta['code_commit']+':'+rel],cwd=REPO)
        if executed!=(base/name).read_bytes(): raise RuntimeError('Executed commit/source mismatch: '+name)
    rel=(base/'PREDICTION.md').relative_to(REPO).as_posix()
    if subprocess.check_output(['git','show',meta['protocol_commit']+':'+rel],cwd=REPO)!=(base/'PREDICTION.md').read_bytes():
        raise RuntimeError('Published protocol changed')
    if (run/'exit-status.txt').read_text().strip()!='0': raise RuntimeError('Registered execution failed')
    for name in ('stderr.txt','lean-stderr.txt'):
        if (run/name).read_bytes(): raise RuntimeError('Nonempty registered error log: '+name)


def check_saved(base,run_name,scorer_name,names):
    run=base/run_name
    check_metadata(base,run)
    scorer=module(run_name+'_scorer',base/scorer_name)
    with tempfile.TemporaryDirectory(prefix='saved-evidence-') as d:
        target=Path(d)
        for name in names: shutil.copyfile(run/(name+'.csv'),target/(name+'.csv'))
        summary=scorer.evaluate(target)  # only analyzes immutable recorded rows
        if summary.get('audit_issues'): raise RuntimeError(json.dumps(summary['audit_issues']))
        for file in ('summary.json','REPORT.md'):
            if (target/file).read_bytes()!=(run/file).read_bytes():
                raise RuntimeError('Recorded evaluation mismatch: '+str(run/file))
    print(f'PASS: {run_name} stored trace audit, predictions, report, code/protocol hashes')


def check_proofs():
    # v2 verify_local writes validation.json, so run it only in an isolated
    # copy. The original v2 directory and archived evidence stay untouched.
    with tempfile.TemporaryDirectory(prefix='proof-snapshot-') as d:
        research=Path(d)/'research'; research.mkdir()
        shutil.copytree(FOUNDATIONS,research/'self-certifying-learning')
        shutil.copytree(V2,research/'adaptive-refresh-experiment',ignore=shutil.ignore_patterns('run-v2','__pycache__'))
        copied=research/'adaptive-refresh-experiment'
        subprocess.run([sys.executable,'-B','verify_local.py'],cwd=copied,check=True,timeout=180)
        if (copied/'validation.json').read_bytes()!=(V2/'validation.json').read_bytes():
            raise RuntimeError('Recomputed local validation differs from recorded v2 validation')
    subprocess.run([sys.executable,'-B','-m','unittest','-v','test_synthetic'],cwd=ROOT,check=True,timeout=120)
    print('PASS: v2 local Lean proofs, mutations and synthetic tests; v3 synthetic checks')


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--preflight',action='store_true',help='Explicitly before v3 execution: verify only prior evidence')
    parser.add_argument('--proofs',action='store_true')
    args=parser.parse_args()
    check_frozen()
    check_saved(V1,'run-v1','evaluate.py',['naive','prudent','contract'])
    check_saved(V2,'run-v2','evaluate.py',['naive','prudent','adaptive'])
    if not args.preflight:
        check_saved(ROOT,'run-v3','score_rupture.py',['adaptive'])
    else:
        if (ROOT/'run-v3').exists(): raise RuntimeError('Preflight forbidden after registered v3 execution')
        print('V3 pending by explicit preflight flag; no registered trajectory executed')
    if args.proofs: check_proofs()
    print('PASS: saved-evidence verification only; no experiment runner invoked')


if __name__=='__main__': main()
