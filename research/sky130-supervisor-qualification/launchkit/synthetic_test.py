"""Exercise the complete launch kit on an RC circuit and a forced interruption.

Uses ngspice42 and the real environment preflight, but only a new local bare
Git repository. Never contacts GitHub or runs an R-cell/registered scenario.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time

HERE=Path(__file__).resolve().parent


def command(argv,cwd,env,expect=0):
    p=subprocess.run(argv,cwd=cwd,env=env,capture_output=True,text=True,timeout=60)
    if (p.returncode==0)!=(expect==0):
        raise AssertionError(str(argv)+'\n'+p.stdout+'\n'+p.stderr)
    return p


def run(root,ngspice,pdk,runtime=None,failure_mode="timeout"):
    root.mkdir(exist_ok=False)
    repo=root/'repo';remote=root/'remote.git';repo.mkdir()
    env=dict(os.environ)
    if runtime:
        tmp=root/'tmp';tmp.mkdir()
        env.update(SPICE_SCRIPTS=str(runtime),LD_PRELOAD=str(runtime/'tmpfile.so'),TMPDIR=str(tmp))
    git=lambda *args:command(['git',*args],repo,env).stdout.strip()
    command(['git','init','--bare',str(remote)],root,env)
    git('init','-b','owner-test');git('config','user.name','Synthetic launch test');git('config','user.email','synthetic@example.invalid')
    git('remote','add','origin',str(remote))
    (repo/'SYNTHETIC_PROTOCOL.txt').write_text('Synthetic RC preflight/launch test only. Not an R cell or registered scenario.\n')
    git('add','.');git('commit','-m','Synthetic protocol stub');protocol=git('rev-parse','HEAD')
    (repo/'tools').mkdir();shutil.copyfile(HERE/'launch.py',repo/'tools'/'launch.py')
    (repo/'rc.spice').write_text('''* Synthetic RC circuit, unrelated to R-cell scenarios
v1 in 0 pulse(0 1 1u 1n 1n 4u 10u)
r1 in out 1k
c1 out 0 1n
.control
tran 100n 20u
set wr_singlescale
set numdgt=16
wrdata trace.txt v(out)
quit
.endc
.end
''')
    (repo/'runner.py').write_text('''import argparse,subprocess,time
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--out',type=Path);p.add_argument('--deck',type=Path);p.add_argument('--ngspice');p.add_argument('--interrupt',action='store_true');p.add_argument('--missing-output',action='store_true');a=p.parse_args()
a.out.mkdir(exist_ok=False)
(a.out/'input.spice').write_bytes(a.deck.read_bytes())
(a.out/'.spiceinit').write_text('set num_threads=1\\n')
if a.interrupt or a.missing_output:
 (a.out/'partial.bin').write_bytes(b'partial-evidence\\x00unchanged\\n')
 if a.interrupt:time.sleep(5)
else:
 r=subprocess.run([a.ngspice,'-b','input.spice'],cwd=a.out,capture_output=True)
 (a.out/'simulator.stdout').write_bytes(r.stdout);(a.out/'simulator.stderr').write_bytes(r.stderr)
 assert r.returncode==0 and (a.out/'trace.txt').exists()
''')
    git('add','.');git('commit','-m','Synthetic implementation');source=git('rev-parse','HEAD')
    sources={p:hashlib.sha256((repo/p).read_bytes()).hexdigest() for p in ('tools/launch.py','runner.py','rc.spice')}
    argv=['{python}','{repo}/runner.py','--out','{out}/evidence','--deck','{deck}','--ngspice','{ngspice}']
    manifest=dict(kind='synthetic',campaign_id='synthetic-rc-launch-test',attempt=1,
        protocol_commit=protocol,source_commit=source,protocol_path='SYNTHETIC_PROTOCOL.txt',
        protocol_sha256=hashlib.sha256((repo/'SYNTHETIC_PROTOCOL.txt').read_bytes()).hexdigest(),
        marker_path='RUN_ATTEMPT.json',launcher_path='tools/launch.py',source_sha256=sources,budget_s=60,
        runs=[dict(id='rc-success',machine='a',deck='rc.spice',runner='runner.py',argv=argv,estimate_s=2,timeout_s=15,required_outputs=['evidence/trace.txt'],diagnostic_logs=['evidence/simulator.stdout','evidence/simulator.stderr']),
              dict(id='forced-interruption',machine='b',deck='rc.spice',runner='runner.py',argv=argv+(['--interrupt'] if failure_mode=='timeout' else ['--missing-output']),estimate_s=.1,timeout_s=.5,required_outputs=['evidence/trace.txt'])])
    (repo/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    git('add','.');git('commit','-m','Synthetic split manifest');git('push','origin','owner-test')
    base=[sys.executable,'-B',str(repo/'tools/launch.py')]
    common=['--repo',str(repo),'--manifest',str(repo/'manifest.json'),'--ngspice',str(ngspice),'--pdk',str(pdk)]
    preflight=command(base+['preflight']+common,repo,env)
    command(base+['prepare']+common,repo,env)
    # A marker merely present locally is insufficient.
    blocked=command(base+['run-machine']+common+['--branch','owner-test','--machine','a','--out',str(root/'unpublished')],repo,env,expect=1)
    assert not (root/'unpublished').exists()
    git('add','RUN_ATTEMPT.json');git('commit','-m','Publish synthetic attempt before launch');git('push','origin','owner-test')
    began=time.monotonic()
    a=command(base+['run-machine']+common+['--branch','owner-test','--machine','a','--out',str(root/'machine-a')],repo,env)
    b=command(base+['run-machine']+common+['--branch','owner-test','--machine','b','--out',str(root/'machine-b')],repo,env,expect=1)
    # New output locations cannot bypass the durable remote claims.
    rejected=[]
    for machine in ('a','b'):
        q=command(base+['run-machine']+common+['--branch','owner-test','--machine',machine,'--out',str(root/('relaunch-'+machine))],repo,env,expect=1)
        assert 'already claimed' in q.stderr
        rejected.append(machine)
    published=[]
    for machine in ('a','b'):
        target=root/('published-'+machine)
        command(base+['collect','--out',str(root/('machine-'+machine)),'--destination',str(target)],repo,env)
        inventory=json.loads((target/'SURVIVORS.json').read_text())
        for f in inventory['files']:
            original=(root/('machine-'+machine)/f['path']).read_bytes()
            assert (target/f['path']).read_bytes()==original and hashlib.sha256(original).hexdigest()==f['sha256']
        published.append(dict(machine=machine,files=len(inventory['files']),status=inventory['status']))
    require_trace=root/'machine-a/rc-success/evidence/trace.txt'
    assert require_trace.is_file()
    assert (root/'published-b/forced-interruption/evidence/partial.bin').read_bytes()==b'partial-evidence\x00unchanged\n'
    return dict(scope='synthetic RC only; local bare Git remote; no R-cell or registered run',
        launcher_sha256=hashlib.sha256((HERE/'launch.py').read_bytes()).hexdigest(),
        preflight=json.loads(preflight.stdout),wall_s=time.monotonic()-began,
        real_ngspice42_trace_sha256=hashlib.sha256(require_trace.read_bytes()).hexdigest(),
        unpublished_marker_refused=True,successful_machine_a=True,
        failure_mode=failure_mode,timeout_preserved_machine_b=failure_mode=='timeout',
        zero_exit_missing_output_refused=failure_mode=='missing-output' and 'Missing frozen input' in b.stderr,
        alternate_output_relaunches_refused=rejected,
        collected_evidence=published,remote_claims=git('ls-remote','--heads','origin','refs/heads/owner-launch/*'))


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--ngspice',type=Path,required=True);p.add_argument('--pdk',type=Path,required=True)
    p.add_argument('--runtime',type=Path);p.add_argument('--work',type=Path,required=True)
    p.add_argument('--report',type=Path,required=True);a=p.parse_args()
    report=run(a.work.resolve(),a.ngspice.resolve(),a.pdk.resolve(),a.runtime.resolve() if a.runtime else None)
    second=Path(str(a.work.resolve())+'-missing-output')
    report['zero_exit_missing_output_fixture']=run(second,a.ngspice.resolve(),a.pdk.resolve(),a.runtime.resolve() if a.runtime else None,failure_mode='missing-output')
    assert report['zero_exit_missing_output_fixture']['zero_exit_missing_output_refused']
    report['zero_exit_missing_output_refused']=True
    report['all_checks_passed']=True
    a.report.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))


if __name__=='__main__': main()
