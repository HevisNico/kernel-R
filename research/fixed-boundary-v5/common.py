"""Canonical v5 evidence schema and frozen-source authentication."""
import csv
import gzip
import hashlib
import io
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parent.parent
PROTOCOL = '6361398d04cf6cbf7c382b4955b879f6025a07a3'
DEPENDENCY = '2cd95d2043ad2c964304a64178f3b7f1c377d671'
N, H, SERVICE, CAPACITY, DOSE, INITIAL = 1320, 150, 100, 660, 220, 440
FIELDS = ('t','rate','pre','post','probe','delivered','reserve_report','rate_report',
          'lower','upper','carry_before','carry_after','action','delay','due',
          'probes','writes','saturation','refused','conditional_pre','conditional_post',
          'sampled_safe','chain_previous','row_hash')
TEXT = {'action','chain_previous','row_hash'}
FROZEN = ['research/'+name for name in ('boundary-cost-study','self-certifying-learning',
          'discrete-refresh-experiment','adaptive-refresh-experiment','refresh-contract-rupture',
          'refusal-recovery','recovery-v4')]


def chain_hash(previous, row):
    payload = {k: '' if row.get(k) is None else str(row.get(k,'')) for k in FIELDS if k != 'row_hash'}
    return hashlib.sha256((previous+'\n'+json.dumps(payload,sort_keys=True,separators=(',',':'))).encode()).hexdigest()


def load_rows(path):
    with gzip.open(path,'rt',newline='') as stream:
        reader = csv.DictReader(stream)
        if tuple(reader.fieldnames or ()) != FIELDS:
            raise ValueError('Noncanonical trace fields')
        rows = []
        for row in reader:
            if None in row or any(v is None for v in row.values()):
                raise ValueError('Truncated trace row')
            rows.append({k:v if k in TEXT else int(v) if v else None for k,v in row.items()})
        return rows


def source_hashes():
    return {p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(ROOT.iterdir())
            if p.is_file() and (p.suffix in ('.py','.lean') or
                p.name in ('PREDICTION.md','lean-toolchain','lakefile.toml','lake-manifest.json'))}


def git(*args):
    return subprocess.check_output(['git',*args],cwd=REPO)


def check_gate(gate):
    issues = []
    required = {'Fixed boundary cost study','R research checks','Kernel R Lean proofs',
                'Robust birth and latency evidence','Circuit simulation analysis'}
    runs = gate.get('runs',[])
    if (gate.get('head_sha')!=DEPENDENCY or gate.get('pr_head_sha')!=DEPENDENCY
            or not required <= {r['name'] for r in runs}):
        issues.append('Prerequisite workflow inventory or exact head differs')
    for run in runs:
        if (run.get('head_sha')!=DEPENDENCY or run.get('status')!='completed'
                or run.get('conclusion')!='success' or run.get('run_attempt',0)<1
                or not run.get('jobs') or any(j.get('status')!='completed' or
                  j.get('conclusion')!='success' for j in run['jobs'])):
            issues.append('Prerequisite latest attempt/job did not succeed')
    return issues


def provenance_issues(out):
    issues = []
    try:
        meta = json.loads((Path(out)/'metadata.json').read_text())
        if meta.get('protocol_commit')!=PROTOCOL or meta.get('dependency_commit')!=DEPENDENCY:
            issues.append('Protocol/dependency identity differs')
        if meta.get('git_status_before_run')!='':
            issues.append('Executed source snapshot was not clean')
        hashes = source_hashes()
        if meta.get('sha256')!=hashes:
            issues.append('Executed source inventory/hash changed')
        validation = json.loads((ROOT/'validation.json').read_text())
        if validation.get('sha256')!=hashes:
            issues.append('Pre-execution validation inventory/hash differs')
        marker = json.loads((ROOT/'RUN_ATTEMPT.json').read_text())
        if (marker.get('attempt')!=1 or marker.get('protocol_commit')!=PROTOCOL
                or marker.get('implementation_commit')!=meta.get('implementation_commit')):
            issues.append('Persistent attempt/implementation differs')
        for commit in (meta['implementation_commit'],meta['code_commit']):
            for name in hashes:
                if git('show',commit+':research/fixed-boundary-v5/'+name)!=(ROOT/name).read_bytes():
                    issues.append('Source differs from published commit: '+name)
        for name,key in (('CI_GATE.json','gate_sha256'),('RUN_ATTEMPT.json','marker_sha256')):
            data=(ROOT/name).read_bytes()
            if hashlib.sha256(data).hexdigest()!=meta.get(key):
                issues.append('Gate/marker hash differs: '+name)
            if git('show',meta['code_commit']+':research/fixed-boundary-v5/'+name)!=data:
                issues.append('Gate/marker was not in executed published commit: '+name)
        issues += check_gate(json.loads((ROOT/'CI_GATE.json').read_text()))
        if git('show',PROTOCOL+':research/fixed-boundary-v5/PREDICTION.md')!=(ROOT/'PREDICTION.md').read_bytes():
            issues.append('Published protocol changed')
        if git('diff',DEPENDENCY,'--',*FROZEN):
            issues.append('Frozen prior sources/evidence changed')
    except (OSError,KeyError,ValueError,TypeError,subprocess.SubprocessError) as exc:
        issues.append('Source provenance could not be audited: '+str(exc))
    return issues
