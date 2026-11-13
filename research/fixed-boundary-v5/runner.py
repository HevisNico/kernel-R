"""Registered single-batch runner. Never invoked by CI or synthetic tests."""
import argparse
import contextlib
import csv
from datetime import datetime,timezone
import gzip
import hashlib
import io
import json
import platform
import subprocess
import sys
import traceback
from common import (ROOT,REPO,PROTOCOL,DEPENDENCY,N,H,SERVICE,CAPACITY,DOSE,INITIAL,
                    FIELDS,TEXT,chain_hash,source_hashes,git,provenance_issues)


from kernel import Kernel


def trajectory(scenario,policy,out,errors):
    path=out/'traces'/f'{scenario["name"]}-{policy}.csv.gz'
    kernel=Kernel(policy,errors)
    post,pending,due,carry=INITIAL,None,0,None
    active,refused=False,False
    probes=writes=saturation=0
    previous='0'*64
    try:
        with path.open('xb') as raw, gzip.GzipFile(filename='',mode='wb',fileobj=raw,mtime=0) as compressed, \
                io.TextIOWrapper(compressed,newline='') as stream:
            writer=csv.DictWriter(stream,FIELDS)
            writer.writeheader()
            for t in range(N+1):
                rate=scenario['rates'][t]
                pre=post if t==0 else post-rate
                delivered=pending==t
                post=min(CAPACITY,pre+DOSE) if delivered else pre
                if delivered:
                    saturation+=max(0,pre+DOSE-CAPACITY)
                    pending=None
                incoming=active and due is not None and t<=due
                probing=t==due or t==N
                row={k:'' if k in TEXT else None for k in FIELDS}
                row.update(t=t,rate=rate,pre=pre,post=post,probe=int(probing),delivered=int(delivered),
                           carry_before=carry,conditional_pre=int(incoming),sampled_safe=0)
                if probing:
                    probes+=1
                    report=pre+scenario['reserve_errors'][t]
                    yr=rate+scenario['rate_errors'][t]
                    fresh=min(CAPACITY,report-2+DOSE) if delivered else report-2
                    upper=min(CAPACITY,report+2+DOSE) if delivered else report+2
                    row.update(reserve_report=report,rate_report=yr,sampled_safe=int(report-2>=SERVICE))
                    if t==N:
                        row.update(action='terminal',delay=0,lower=fresh,upper=upper)
                        due=None
                        active=incoming
                    else:
                        action,delay,lower,upper,new_carry=kernel.decide(report,yr,delivered,carry)
                        row.update(action=action,delay=delay,lower=lower,upper=upper)
                        if action=='refuse':
                            refused,active,carry,due=True,False,None,None
                        else:
                            if delay not in (1,2):
                                raise RuntimeError('Kernel duration outside registered family')
                            carry,due,active=new_carry,t+delay,True
                            if action=='write':
                                if pending is not None or delay!=1:
                                    raise RuntimeError('Overlapping/instantaneous write')
                                writes+=1
                                pending=t+1
                row.update(carry_after=carry,due=due,probes=probes,writes=writes,saturation=saturation,
                           refused=int(refused),conditional_post=int(active),chain_previous=previous)
                row['row_hash']=chain_hash(previous,row)
                previous=row['row_hash']
                writer.writerow(row)
                stream.flush()
        if pending is not None:
            raise RuntimeError('Unfinished physical delivery at horizon')
    finally:
        kernel.close()


def metadata():
    marker=json.loads((ROOT/'RUN_ATTEMPT.json').read_text())
    return dict(protocol_commit=PROTOCOL,dependency_commit=DEPENDENCY,
                implementation_commit=marker['implementation_commit'],code_commit=git('rev-parse','HEAD').decode().strip(),
                git_status_before_run=git('status','--porcelain').decode().strip(),
                started_utc=datetime.now(timezone.utc).isoformat(),python=platform.python_version(),
                lean=subprocess.check_output(['lake','env','lean','--version'],cwd=ROOT,text=True).strip(),
                command='python3 -B runner.py --run-once',sha256=source_hashes(),
                gate_sha256=hashlib.sha256((ROOT/'CI_GATE.json').read_bytes()).hexdigest(),
                marker_sha256=hashlib.sha256((ROOT/'RUN_ATTEMPT.json').read_bytes()).hexdigest())


def execute(out):
    from scenarios import batch
    from comparators import compare
    from audit import evaluate
    (out/'scenarios').mkdir()
    (out/'traces').mkdir()
    oracles={}
    with (out/'lean-stderr.txt').open('x') as errors, (out/'oracle-events.jsonl').open('x') as journal:
        for scenario in batch():
            name=scenario['name']
            with (out/'scenarios'/f'{name}.json').open('x') as f:
                json.dump(scenario,f,separators=(',',':'))
                f.write('\n')
            for policy in (('early',) if name=='outside' else ('early','prudent')):
                trajectory(scenario,policy,out,errors)
                print('completed',name,policy,flush=True)
            if name!='outside':
                result=compare(scenario)
                oracles[name]=result
                journal.write(json.dumps(dict(name=name,**result),sort_keys=True)+'\n')
                journal.flush()
    with (out/'oracle.json').open('x') as f:
        json.dump(oracles,f,indent=2)
        f.write('\n')
    summary=evaluate(out,provenance_issues(out))
    print(json.dumps(summary,sort_keys=True),flush=True)
    return summary


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--run-once',action='store_true',required=True)
    parser.parse_args()
    out=ROOT/'run-v5'
    out.mkdir(exist_ok=False)
    status=1
    try:
        meta=metadata()
        with (out/'metadata.json').open('x') as f:
            json.dump(meta,f,indent=2)
            f.write('\n')
        with (out/'stdout.txt').open('x') as stdout,(out/'stderr.txt').open('x') as stderr, \
                contextlib.redirect_stdout(stdout),contextlib.redirect_stderr(stderr):
            try:
                if sys.version_info[:2]!=(3,12):
                    raise RuntimeError('Registered generator requires Python 3.12')
                issues=provenance_issues(out)
                if issues:
                    raise RuntimeError('Preflight: '+repr(issues))
                summary=execute(out)
                status=int(bool(summary['audit_issues']) or not all(summary['predictions'].values()))
            except BaseException:
                (out/'FAILURE.txt').write_text(traceback.format_exc())
                traceback.print_exc()
    except BaseException:
        (out/'FAILURE.txt').write_text(traceback.format_exc())
        raise
    finally:
        (out/'exit-status.txt').write_text(str(status)+'\n')
    return status


if __name__=='__main__':
    sys.exit(main())
