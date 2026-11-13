"""Owner-only, one-attempt two-machine launcher; no registered campaign is supplied."""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
import hashlib
import json
import math
import os
from pathlib import Path, PurePosixPath
import platform
import re
import secrets
import signal
import shutil
import subprocess
import sys
import tempfile
import time
import urllib.parse
import urllib.request

EXPECTED = {
    'ngspice_version': '42',
    'ngspice_sha256': '820658317b0b54035208da41936fd6871ce924036e5ea4113a4168b821b7fc45',
    'pdk_commit': '1232782c1b9fab3aacda74d67ce7c92bf7da8105',
    'python_version': '3.12.14', 'numpy_version': '2.3.5', 'machine': 'x86_64',
}


class Refusal(RuntimeError):
    pass


def require(test, message):
    if not test:
        raise Refusal(message)


def utc():
    return datetime.now(timezone.utc).isoformat()


def encoded(value):
    return (json.dumps(value, sort_keys=True, indent=2)+'\n').encode()


def sha(data):
    return hashlib.sha256(data).hexdigest()


def write_new(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('xb') as f:
        f.write(data)
        f.flush()
        os.fsync(f.fileno())


def git(repo, *args, data=None, env=None):
    p = subprocess.run(['git', *args], cwd=repo, input=data, capture_output=True, env=env)
    if p.returncode:
        raise Refusal('Git command refused: '+ ' '.join(args[:2])+'\n'+p.stderr.decode(errors='replace'))
    return p.stdout


def relative(value):
    require(isinstance(value,str) and value and '\\' not in value, 'Invalid path')
    p = PurePosixPath(value)
    require(not p.is_absolute() and p.as_posix()==value and all(x not in ('','.','..') for x in value.split('/')), 'Unsafe path: '+value)
    return value


def frozen_file(repo, name):
    relative(name)
    p = repo
    for part in PurePosixPath(name).parts:
        p /= part
        require(not p.is_symlink(), 'Symlink in frozen input: '+name)
    require(p.is_file(), 'Missing frozen input: '+name)
    return p.read_bytes()


CLEANUP_ALLOWANCE_S = 10


def check_budget(runs,budget_s):
    require(type(budget_s) in (int,float) and math.isfinite(budget_s) and 0 < budget_s <= 14400,
            'Budget must be finite, positive and at most four hours')
    for run in runs:
        estimate,timeout=run.get('estimate_s'),run.get('timeout_s')
        require(type(estimate) in (int,float) and math.isfinite(estimate) and estimate>0,
                'Runtime estimate must be finite and positive')
        require(type(timeout) in (int,float) and math.isfinite(timeout) and timeout>=estimate,
                'Timeout must be finite, positive and at least the estimate')
    estimated=sum(r['estimate_s'] for r in runs)
    execution_cap=sum(r['timeout_s']+CLEANUP_ALLOWANCE_S for r in runs)
    require(math.isfinite(estimated) and estimated<=execution_cap<=budget_s,
            'Aggregate timeouts plus per-run cleanup exceed the campaign budget')
    return dict(estimated_s=estimated,execution_and_cleanup_cap_s=execution_cap,
                cleanup_allowance_per_run_s=CLEANUP_ALLOWANCE_S,budget_s=budget_s)


def read_manifest(repo, path):
    path = path.resolve()
    name = path.relative_to(repo).as_posix()
    data = frozen_file(repo, name)
    m = json.loads(data)
    require(m.get('kind') in ('registered','synthetic'), 'Unknown campaign kind')
    require(m.get('attempt') == 1, 'Only attempt 1 is supported')
    require(re.fullmatch(r'[a-z0-9][a-z0-9-]{2,63}',m.get('campaign_id','')) is not None, 'Invalid campaign ID')
    require(m['kind']!='synthetic' or m['campaign_id'].startswith('synthetic-'), 'Synthetic campaign namespace required')
    require(m['kind']!='registered' or not m['campaign_id'].startswith('synthetic-'), 'Registered namespace cannot be synthetic')
    if m['kind']=='registered':
        require(isinstance(m.get('expected_workflows'),list) and m['expected_workflows'] and all(isinstance(x,str) and x for x in m['expected_workflows']), 'Nonempty expected workflow list required')
    for key in ('protocol_commit','source_commit'):
        require(re.fullmatch('[0-9a-f]{40}',m.get(key,'')) is not None, 'Exact commit required: '+key)
    relative(m['protocol_path']); relative(m['marker_path'])
    require(m['protocol_commit'] != m['source_commit'], 'Protocol must precede implementation')
    git(repo,'merge-base','--is-ancestor',m['protocol_commit'],m['source_commit'])
    protocol = git(repo,'show',m['protocol_commit']+':'+m['protocol_path'])
    require(sha(protocol)==m['protocol_sha256'], 'Protocol digest differs')
    unchanged_protocol(repo,m,protocol)
    sources = m['source_sha256']
    require(isinstance(sources,dict) and sources, 'Frozen source inventory required')
    for name_, digest in sources.items():
        local = frozen_file(repo,name_)
        require(sha(local)==digest, 'Local source differs: '+name_)
        require(git(repo,'show',m['source_commit']+':'+name_)==local, 'Source commit differs: '+name_)
    require(m['launcher_path'] in sources, 'Launcher itself must be frozen')
    require((repo/m['launcher_path']).resolve()==Path(__file__).resolve(), 'Use the frozen launcher from this repository')
    ids=set(); machines=set()
    for run in m['runs']:
        require(re.fullmatch('[a-zA-Z0-9_-]+',run['id']) is not None and run['id'] not in ids, 'Invalid/duplicate run ID')
        ids.add(run['id']); machines.add(run['machine'])
        require(run['machine'] in ('a','b'), 'Machine must be a or b')
        # Numeric runtime and aggregate hard-stop checks follow the inventory check.
        require(isinstance(run['argv'],list) and run['argv'] and run['argv'][0] in ('{python}','{ngspice}'), 'Use a frozen Python runner or ngspice, not a shell')
        require(all(isinstance(x,str) for x in run['argv']), 'argv must be strings')
        if m['kind']=='registered':
            require(run['argv'][0]=='{python}', 'Registered runs require a frozen Python runner with scientific postflight; direct ngspice is forbidden')
        outputs=run.get('required_outputs')
        require(isinstance(outputs,list) and outputs and len(set(outputs))==len(outputs), 'Nonempty unique required_outputs inventory required')
        for name_ in outputs:relative(name_)
        logs=run.get('diagnostic_logs',[])
        require(isinstance(logs,list), 'diagnostic_logs must be a list')
        for name_ in logs:relative(name_)
        if m['kind']=='registered':
            require(logs, 'Registered runs must expose simulator stdout/stderr paths for fatal-error checking')
        require(run['deck'] in sources and run['runner'] in sources, 'Each deck and runner must be frozen')
        if run['argv'][0]=='{python}':
            require(len(run['argv'])>1 and run['argv'][1]=='{repo}/'+run['runner'], 'Python argv must execute the frozen runner')
        else:
            require('{deck}' in run['argv'], 'ngspice argv must use the frozen deck')
    require(machines=={'a','b'}, 'Both machine shards must be nonempty')
    check_budget(m['runs'],m['budget_s'])
    return m, data, name


def unchanged_protocol(repo,m,protocol):
    require(frozen_file(repo,m['protocol_path'])==protocol, 'Local protocol differs from preregistration')
    require(git(repo,'show',m['source_commit']+':'+m['protocol_path'])==protocol,
            'Implementation altered the preregistered protocol')


def runtime_unchanged(repo,m,manifest_path,revision):
    changed=set(git(repo,'diff','--name-only',m['source_commit'],revision).decode().splitlines())
    allowed={manifest_path,m['marker_path']}
    require(changed<=allowed,'Runtime source tree changed after implementation freeze: '+repr(sorted(changed-allowed)))


def github_json(path):
    request=urllib.request.Request('https://api.github.com/repos/HevisNico/kernel-R/'+path,
        headers={'Accept':'application/vnd.github+json','User-Agent':'kernel-R-owner-launchkit'})
    with urllib.request.urlopen(request,timeout=30) as response:
        return json.load(response)


def api_pages(path,key,get=github_json):
    result=[]
    for page in range(1,101):
        separator='&' if '?' in path else '?'
        document=get(path+separator+'per_page=100&page='+str(page))
        items=document[key];result.extend(items)
        if len(items)<100:return result
    raise Refusal('API pagination did not terminate')


def live_ci_gate(m,get=github_json):
    require(m['kind']=='registered','Synthetic fixtures must not use the GitHub CI gate')
    runs=api_pages('actions/runs?head_sha='+m['source_commit'],'workflow_runs',get)
    latest={}
    for run in runs:
        require(run['head_sha']==m['source_commit'],'CI response includes a different commit')
        previous=latest.get(run['workflow_id'])
        if previous is None or (run['id'],run['run_attempt'])>(previous['id'],previous['run_attempt']):
            latest[run['workflow_id']]=run
    require(set(m['expected_workflows'])<={x['name'] for x in latest.values()},'An expected exact-head workflow is missing')
    checked=[]
    for run in latest.values():
        require(run['status']=='completed' and run['conclusion']=='success','Latest exact-head workflow is not successful: '+run['name'])
        jobs=api_pages('actions/runs/'+str(run['id'])+'/attempts/'+str(run['run_attempt'])+'/jobs','jobs',get)
        require(jobs and all(j['status']=='completed' and j['conclusion']=='success' for j in jobs),'Latest-attempt jobs are missing or not successful: '+run['name'])
        checked.append(dict(name=run['name'],id=run['id'],run_attempt=run['run_attempt'],
                            html_url=run['html_url'],jobs=[dict(id=j['id'],name=j['name'],conclusion=j['conclusion']) for j in jobs]))
    require(checked,'No exact-head workflows found')
    return dict(head_sha=m['source_commit'],observed_utc=utc(),workflows=checked)


def preflight(repo, manifest, ngspice, pdk):
    import numpy
    m, data, name = read_manifest(repo,manifest)
    if m['kind']=='registered':
        require(not any(os.environ.get(x) for x in ('LD_PRELOAD','SPICE_SCRIPTS','PYTHONPATH','PYTHONHOME')), 'Unqualified simulator/Python runtime overrides are forbidden for registered launch')
        untracked=set(git(repo,'ls-files','--others','--exclude-standard').decode().splitlines())
        require(untracked<={m['marker_path']},'Untracked files could shadow frozen runtime inputs; use an otherwise clean checkout')
    actual = dict(ngspice_sha256=sha(ngspice.read_bytes()),
                  pdk_commit=git(pdk,'rev-parse','HEAD').decode().strip(),
                  python_version=platform.python_version(),numpy_version=numpy.__version__,machine=platform.machine())
    r = subprocess.run([str(ngspice),'--version'],capture_output=True,text=True,timeout=30)
    match = re.search(r'ngspice-(\d+(?:\.\d+)?)\s*:',r.stdout+r.stderr)
    require(r.returncode==0 and match is not None, 'Cannot identify ngspice version')
    actual['ngspice_version']=match.group(1)
    require(actual==EXPECTED, 'Environment does not match pinned ngspice42/PDK/Python/numpy: '+json.dumps(actual))
    require(not git(pdk,'status','--porcelain','--untracked-files=all').strip(), 'PDK working tree is not clean')
    require(not git(repo,'diff','--name-only').strip() and not git(repo,'diff','--cached','--name-only').strip(), 'Tracked repository changes exist')
    runtime_unchanged(repo,m,name,'HEAD')
    return m,data,name,actual


def marker_value(m, manifest_data, manifest_path, environment):
    return dict(kind=m['kind'],campaign_id=m['campaign_id'],attempt=1,manifest_path=manifest_path,
                manifest_sha256=sha(manifest_data),protocol_commit=m['protocol_commit'],
                source_commit=m['source_commit'],environment=environment,
                shards={machine:[r['id'] for r in m['runs'] if r['machine']==machine] for machine in ('a','b')},
                estimates_s={machine:sum(r['estimate_s'] for r in m['runs'] if r['machine']==machine) for machine in ('a','b')},
                execution_and_cleanup_caps_s={machine:sum(r['timeout_s']+CLEANUP_ALLOWANCE_S for r in m['runs'] if r['machine']==machine) for machine in ('a','b')},
                budget=check_budget(m['runs'],m['budget_s']))


def published_marker(repo, remote, branch, m, data, name, environment):
    if m['kind']=='registered':
        url=git(repo,'remote','get-url',remote).decode().strip().removesuffix('.git')
        require(url in ('https://github.com/HevisNico/kernel-R','git@github.com:HevisNico/kernel-R'), 'Registered claims require the designated GitHub repository')
    git(repo,'fetch','--no-tags',remote,branch)
    commit=git(repo,'rev-parse','FETCH_HEAD').decode().strip()
    git(repo,'merge-base','--is-ancestor',m['source_commit'],commit)
    runtime_unchanged(repo,m,name,commit)
    require(git(repo,'show',commit+':'+name)==data, 'Remote manifest differs or is unpublished')
    marker=json.loads(git(repo,'show',commit+':'+m['marker_path']))
    expected=marker_value(m,data,name,environment)
    require({k:marker.get(k) for k in expected}==expected, 'Published RUN_ATTEMPT does not bind this campaign')
    require(isinstance(marker.get('created_utc'),str), 'Marker timestamp is missing')
    return commit,marker


def claim(repo, remote, published, m, machine):
    ref='refs/heads/owner-launch/protocol-'+m['protocol_sha256']+'/'+machine
    require(not git(repo,'ls-remote','--heads',remote,ref).strip(), 'Machine already claimed: never relaunch, even in another clone/output directory')
    record=dict(campaign_id=m['campaign_id'],protocol_sha256=m['protocol_sha256'],attempt=1,machine=machine,published_marker_commit=published,
                nonce=secrets.token_hex(32),claimed_utc=utc(),status='claimed-before-execution')
    blob=git(repo,'hash-object','-w','--stdin',data=encoded(record)).decode().strip()
    with tempfile.TemporaryDirectory() as tmp:
        env=dict(os.environ,GIT_INDEX_FILE=str(Path(tmp)/'index'))
        git(repo,'read-tree',published,env=env)
        entry='OWNER_LAUNCH_CLAIMS/'+m['campaign_id']+'/'+machine+'.json'
        git(repo,'update-index','--add','--cacheinfo','100644,'+blob+','+entry,env=env)
        tree=git(repo,'write-tree',env=env).decode().strip()
        commit=git(repo,'commit-tree',tree,'-p',published,'-m','Claim owner launch '+m['campaign_id']+' machine '+machine,data=b'').decode().strip()
    # Normal push only. Concurrent claims are distinct sibling commits, so only
    # one can create the ref; no force, deletion, reset, merge or automatic retry.
    git(repo,'push',remote,commit+':'+ref)
    got=git(repo,'ls-remote','--heads',remote,ref).decode().split()
    require(got and got[0]==commit, 'Durable claim could not be confirmed; do not execute')
    return ref,commit,record


def postflight(folder,run):
    # Exit 0 from ngspice does not imply a completed transient. These generic
    # file/log checks complement, never replace, the frozen scientific runner's
    # checks of waveform end time, vectors, event inventory and protocol rules.
    outputs=[]
    for name in run['required_outputs']:
        data=frozen_file(folder,name)
        require(data,'Required output is empty: '+name)
        outputs.append(dict(path=name,bytes=len(data),sha256=sha(data)))
    for name in ['stdout.log','stderr.log']+run.get('diagnostic_logs',[]):
        log=frozen_file(folder,name).lower()
        require(not any(token in log for token in (b'aborted',b'timestep too small',b'transient op failed',b'fatal error')),
                'Fatal simulator marker in '+name+'; preserve evidence, never relaunch')
    return outputs


def launch(repo,m,machine,out,ngspice,pdk,remote,branch,data,name,environment):
    require(not out.exists(),'Output exists: never relaunch or overwrite')
    published,marker=published_marker(repo,remote,branch,m,data,name,environment)
    ci=live_ci_gate(m) if m['kind']=='registered' else {'kind':'synthetic-local-fixture-no-GitHub-CI'}
    ref,claim_commit,record=claim(repo,remote,published,m,machine)
    out.mkdir(parents=True,exist_ok=False)
    write_new(out/'CLAIM.json',encoded(dict(record,claim_ref=ref,claim_commit=claim_commit)))
    write_new(out/'RUN_ATTEMPT.json',encoded(marker))
    write_new(out/'ENVIRONMENT.json',encoded(environment))
    write_new(out/'CI_OBSERVED.json',encoded(ci))
    records=[]
    state=out/'STATE.json'
    def save(status):
        state.write_bytes(encoded(dict(status=status,records=records,claim_commit=claim_commit)))
    save('running')
    try:
        for run in (r for r in m['runs'] if r['machine']==machine):
            folder=out/run['id'];folder.mkdir(exist_ok=False)
            substitutions=dict(repo=str(repo),out=str(folder),python=sys.executable,ngspice=str(ngspice),pdk=str(pdk),deck=str(repo/run['deck']))
            argv=[s.format(**substitutions) for s in run['argv']]
            record=dict(id=run['id'],status='started',started_utc=utc(),argv=argv)
            records.append(record);save('running')
            start=time.monotonic();process=None
            with (folder/'stdout.log').open('xb') as stdout,(folder/'stderr.log').open('xb') as stderr:
                try:
                    process=subprocess.Popen(argv,cwd=repo,stdout=stdout,stderr=stderr,start_new_session=True)
                    code=process.wait(timeout=run['timeout_s'])
                    record.update(returncode=code,status='complete' if code==0 else 'failed',wall_s=time.monotonic()-start)
                    require(code==0,'Run failed; publish survivors; never relaunch')
                    record['required_outputs']=postflight(folder,run)
                except BaseException:
                    if process is not None:
                        try: os.killpg(process.pid,signal.SIGTERM)
                        except ProcessLookupError: pass
                        try: process.wait(timeout=CLEANUP_ALLOWANCE_S)
                        except subprocess.TimeoutExpired:
                            try: os.killpg(process.pid,signal.SIGKILL)
                            except ProcessLookupError: pass
                            process.wait()
                    record.update(status='interrupted-or-failed',wall_s=time.monotonic()-start)
                    raise
                finally:
                    stdout.flush();stderr.flush();os.fsync(stdout.fileno());os.fsync(stderr.fileno())
            save('running')
    except BaseException:
        save('incomplete-no-relaunch')
        raise
    save('complete')
    return dict(machine=machine,status='complete',claim_commit=claim_commit,output=str(out))


def collect(out,destination,interrupted=False):
    out=out.resolve();destination=destination.resolve()
    require(not destination.is_relative_to(out),'Collection destination must be outside the evidence tree')
    require(out.is_dir() and not destination.exists(),'Require existing evidence and a new destination')
    state=json.loads((out/'STATE.json').read_bytes()) if (out/'STATE.json').exists() else dict(status='unknown')
    require(state['status']!='running' or interrupted,'Stop all processes first; explicitly declare an interrupted running state')
    destination.mkdir(parents=True,exist_ok=False)
    files=[]
    for p in sorted(out.rglob('*')):
        require(not p.is_symlink(),'Evidence symlink cannot be silently copied or omitted')
        require(p.is_dir() or p.is_file(),'Unsupported evidence file type; no silent omission')
        if p.is_file():
            rel=p.relative_to(out);data=p.read_bytes();target=destination/rel
            write_new(target,data)
            require(p.read_bytes()==data,'Source changed during collection; preserve both versions and stop')
            files.append(dict(path=rel.as_posix(),bytes=len(data),sha256=sha(data)))
    manifest=dict(interrupted_declared=interrupted,status=state['status'],files=files,
                  rule='Every surviving regular file copied byte for byte; no rerun, compression or deletion')
    write_new(destination/'SURVIVORS.json',encoded(manifest))
    return manifest


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('command',choices=('preflight','prepare','plan','run-machine','collect'))
    p.add_argument('--repo',type=Path,default=Path.cwd());p.add_argument('--manifest',type=Path)
    p.add_argument('--ngspice',type=Path);p.add_argument('--pdk',type=Path)
    p.add_argument('--remote',default='origin');p.add_argument('--branch')
    p.add_argument('--machine',choices=('a','b'));p.add_argument('--out',type=Path)
    p.add_argument('--destination',type=Path);p.add_argument('--interrupted',action='store_true')
    a=p.parse_args();repo=a.repo.resolve()
    if a.command=='collect':
        result=collect(a.out.resolve(),a.destination.resolve(),a.interrupted)
    else:
        require(a.manifest is not None and a.ngspice is not None and a.pdk is not None,'Manifest, ngspice and PDK are required')
        ngspice=a.ngspice.resolve();pdk=a.pdk.resolve()
        m,data,name,environment=preflight(repo,a.manifest,ngspice,pdk)
        if a.command in ('preflight','plan'):
            result=marker_value(m,data,name,environment)
        elif a.command=='prepare':
            if m['kind']=='registered':live_ci_gate(m)
            result=marker_value(m,data,name,environment);result['created_utc']=utc()
            write_new(repo/m['marker_path'],encoded(result))
        else:
            require(a.branch and a.machine and a.out is not None,'Branch, machine and output are required')
            result=launch(repo,m,a.machine,a.out.resolve(),ngspice,pdk,a.remote,a.branch,data,name,environment)
    print(json.dumps(result,indent=2,sort_keys=True))


if __name__=='__main__':
    try: main()
    except (Refusal,KeyError,ValueError,OSError) as e:
        print('REFUSED: '+str(e),file=sys.stderr);sys.exit(1)
