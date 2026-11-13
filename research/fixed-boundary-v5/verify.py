"""Proof/fixture preparation and saved-evidence audit; never launches v5."""
import argparse
import ast
import json
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
from common import ROOT,REPO,PROTOCOL,DEPENDENCY,FROZEN,git,source_hashes,provenance_issues

from mutation_controls import MUTATIONS

SEMANTIC=re.compile(r'Type mismatch|unsolved goals|omega could not prove|Tactic `decide` proved',re.I)
BROKEN=re.compile(r'unexpected token|Unknown identifier|Unknown constant|unknown module|unknown package|object file .* does not exist|unknown tactic|failed to synthesize',re.I)


def run(args):
    return subprocess.run(args,cwd=ROOT,text=True,stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT,timeout=180)


def success(args):
    result=run(args)
    if result.returncode or re.search(r'declaration uses.*sorry',result.stdout):
        raise RuntimeError('Positive check failed: '+repr(args)+'\n'+result.stdout)
    return result.stdout


def saved_checks(out):
    from audit import evaluate
    from comparators import compare
    from tests_saved_controls import run_saved_controls
    if (out/'exit-status.txt').read_text().strip()!='0':
        raise RuntimeError('Registered batch failed: preserve it, never relaunch')
    for name in ('stderr.txt','lean-stderr.txt'):
        if (out/name).read_bytes():
            raise RuntimeError('Nonempty registered error log: '+name)
    issues=provenance_issues(out)
    if issues:
        raise RuntimeError('Provenance failed: '+repr(issues))
    with tempfile.TemporaryDirectory(prefix='v5-saved-') as temp:
        target=Path(temp)/'evidence'
        shutil.copytree(out,target,ignore=shutil.ignore_patterns('summary.json','REPORT.md'))
        summary=evaluate(target,issues)
        if summary['audit_issues'] or not all(summary['predictions'].values()):
            raise RuntimeError('Saved evidence violates registered outcomes: '+repr(summary['audit_issues']))
        for name in ('summary.json','REPORT.md'):
            if (target/name).read_bytes()!=(out/name).read_bytes():
                raise RuntimeError('Unedited generated report differs: '+name)
    expected=json.loads((out/'oracle.json').read_text())
    for name,record in expected.items():
        scenario=json.loads((out/'scenarios'/(name+'.json')).read_text())
        if compare(scenario)!=record:
            raise RuntimeError('Saved oracle not reproduced by both solvers: '+name)
    controls=run_saved_controls(out)
    print('PASS: immutable evidence, all outcomes, source provenance, both saved-scenario oracle solvers')
    print('PASS: six semantic saved-trace controls with recomputed valid hashes: '+', '.join(controls))
    return controls


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--preflight',action='store_true')
    parser.add_argument('--report',type=Path)
    args=parser.parse_args()
    if args.preflight and (ROOT/'run-v5').exists():
        raise RuntimeError('Preflight cannot bypass a registered attempt')
    if git('diff',DEPENDENCY,'--',*FROZEN):
        raise RuntimeError('Frozen dependencies changed')
    if git('show',PROTOCOL+':research/fixed-boundary-v5/PREDICTION.md')!=(ROOT/'PREDICTION.md').read_bytes():
        raise RuntimeError('Published protocol changed')
    for path in ROOT.glob('*.py'):
        ast.parse(path.read_text(),filename=str(path))
    source=(ROOT/'Model.lean').read_text()
    if re.search(r'\b(sorry|admit|native_decide)\b|^\s*(?:private\s+)?(?:axiom|unsafe)\s',source,re.M):
        raise RuntimeError('Forbidden proof shortcut')
    success(['lake','build'])
    audit=success(['lake','env','lean','Audit.lean']).strip()
    success(['lake','env','lean','Bridge.lean'])
    success(['python3','-B','-m','unittest','-v','test_synthetic'])
    passed=[]
    (ROOT/'.lake').mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='controls-',dir=ROOT/'.lake') as temp:
        path=Path(temp)/'Control.lean'
        for name,old,new in MUTATIONS:
            if source.count(old)!=1:
                raise RuntimeError('Nonunique proof mutation anchor: '+name)
            path.write_text(source)
            success(['lake','env','lean',str(path)])
            path.write_text(source.replace(old,new))
            result=run(['lake','env','lean',str(path)])
            if not result.returncode or BROKEN.search(result.stdout) or not SEMANTIC.search(result.stdout):
                raise RuntimeError('Mutation not rejected semantically: '+name+'\n'+result.stdout)
            passed.append(name)
    saved=[]
    if args.preflight:
        print('PREPARATION ONLY: no registered scenario generated or trajectory executed')
    else:
        saved=saved_checks(ROOT/'run-v5')
    report=dict(protocol_commit=PROTOCOL,dependency_commit=DEPENDENCY,audit=audit,
                isolated_tests=4,paired_semantic_controls=passed,saved_semantic_controls=saved,
                sha256=source_hashes())
    if args.report:
        args.report.write_text(json.dumps(report,indent=2)+'\n')
    print(audit)
    print('PASS: four isolated tests, five paired proof mutations, frozen sources unchanged')


if __name__=='__main__':
    main()
