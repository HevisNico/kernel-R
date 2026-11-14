"""Phase-1 qualification probes, not registered scenarios or a jump campaign."""
import argparse
import gzip
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import time

import numpy as np

HERE = Path(__file__).resolve().parent
CIRCUIT = HERE.parent/'circuit'
spec = importlib.util.spec_from_file_location('phase0_probe',HERE.parent/'sky130-supervisor-map'/'probe.py')
phase0 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(phase0)
SIGNALS = phase0.SIGNALS + ['v(vmem2)','v(x2.sum)','v(x2.si)','i(v.x2.vdose)']
COL = {s:i+1 for i,s in enumerate(SIGNALS)}
NGSPICE_SHA = '820658317b0b54035208da41936fd6871ce924036e5ea4113a4168b821b7fc45'
PDK = phase0.PDK_COMMIT


def digest(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def make_deck(case):
    assert all(x in (0,1) for x in case['actions']), '95% input is diagnostic only, never this actuator'
    text, starts, stop = phase0.deck(case)
    text = text.replace('* Phase 0 action probe:', '* Phase 1 calibration:')
    text = text.replace('.lib "pdk/models/sky130.lib.spice" tt', f'.lib "pdk/models/sky130.lib.spice" {case["section"]}')
    text = text.replace('.option temp=27', f'.option temp={case["temperature_C"]}')
    x2 = next(l for l in text.splitlines() if l.startswith('x2 '))
    new = x2.replace(' vpre vinit rport ', ' vpre vinit2 rport ')
    if case.get('joint'):
        new = new.split(' ta=')[0]+' ta=440u tb=1 tj=2'
    text = text.replace(x2,new)
    text = text.replace('.save '+ ' '.join(phase0.SIGNALS),
                        f'vinit2 vinit2 0 {case.get("vinit2",case["vinit"]):.12g}\n.save '+' '.join(SIGNALS))
    text = text.replace('wrdata trace.txt '+' '.join(phase0.SIGNALS), 'wrdata trace.txt '+' '.join(SIGNALS))
    if case.get('method') == 'gear':
        text = text.replace('.control','.option method=gear maxord=2\n.control')
    if case.get('noise'):
        params=json.loads((CIRCUIT/'noise.json').read_text())['params']
        for node,w,f in [('nzc',params['vncw'],params['vncf']),('nzo',params['vnow'],params['vnof']),('nzi',params['inmw'],0),('nzm',params['vnmw'],params['vnmf'])]:
            old=f'vnz{node[2]} {node} 0 dc 0'
            assert text.count(old)==1
            text=text.replace(old,f'{old} trnoise({w:.16g} {params["tnz"]:.16g} {1 if f else 0} {f:.16g})')
    if case.get('seed') is not None:
        text=text.replace('.control','.control\nsetseed '+str(case['seed'])+'\nreset')
    return text,starts,stop


def sample(d,s,t):
    return float(np.interp(t,d[:,0],d[:,COL[s]]))


def native_integral(d,s,lo,hi):
    mask=(d[:-1,0]>=lo)&(d[1:,0]<=hi)
    dt=np.diff(d[:,0])[mask];v=d[:,COL[s]]
    return dict(value=float(np.sum(dt*(v[:-1][mask]+v[1:][mask])/2)),
                omitted_s=float(hi-lo-sum(dt)))


def analyze(d,case,starts,stop):
    assert d.shape[1]==len(SIGNALS)+1 and np.isfinite(d).all()
    assert d[-1,0]>=stop-1e-12 and np.all(np.diff(d[:,0])>=0)
    actions=[]
    for i,start in enumerate(starts):
        lo=start-4.1e-6;hi=starts[i+1]-4.1e-6 if i+1<len(starts) else stop
        fires=phase0.crossings(d,'v(p)',lo+1e-6,hi-1e-6)
        requested=case['actions'][i]==1
        roles=case.get('roles',['service' if a else 'maintenance' for a in case['actions']])
        act=dict(index=i,role=roles[i],start_s=start,requested_service=requested and roles[i]=='service',
                 fire_times_s=fires,fire_latency_units=(fires[0]-start)/20e-6 if len(fires)==1 else None,
                 pulse_correct=len(fires)==1 and start<=fires[0]<=start+20e-6,
                 pre_vq_V=sample(d,'v(vq)',start-1e-9),pre_protection_V=sample(d,'v(p)',start-1e-9),ports=[])
        act['service_success']=act['pulse_correct'] if act['requested_service'] else None
        for port in (1,2):
            mem=f'v(vmem{port})';summ=f'v(x{port}.sum)';current=f'i(v.x{port}.vdose)'
            q=native_integral(d,current,lo,hi)
            leak=native_integral(d,summ,lo,hi)
            pre=sample(d,mem,start-1e-9);post=sample(d,mem,hi-1e-6)
            slotgain=(sample(d,mem,lo)-sample(d,mem,hi))*1000
            flux=leak['value']/case['rlk']/30e-12*1000
            steering=d[(d[:,0]>=lo)&(d[:,0]<hi),COL[f'v(x{port}.si)']]
            act['ports'].append(dict(port=port,pre_vmem_V=pre,post_vmem_V=post,
                slot_gain_mV=slotgain,native_charge_fC=q['value']*1e15,
                charge_omitted_s=q['omitted_s'],resistor_loss_mV=flux,
                net_plus_resistor_mV=slotgain+flux,steering_seen=bool(np.max(steering)>.9),
                sum_range_V=[float(np.min(d[:,COL[summ]])),float(np.max(d[:,COL[summ]]))]))
        actions.append(act)
    return dict(actions=actions,simulated_s=stop,rows=len(d),
                complete_service_success=all(a['service_success'] for a in actions if a['requested_service']),
                requested_services=sum(a['requested_service'] for a in actions),
                missed_services=sum(a['service_success'] is False for a in actions))


def run(case,out,args):
    out.mkdir(parents=True,exist_ok=False)
    (out/'pdk').symlink_to(args.pdk.resolve(),target_is_directory=True)
    for name in ('blocks.spice',):shutil.copyfile(CIRCUIT/name,out/name)
    shutil.copyfile(CIRCUIT/'spiceinit.txt',out/'.spiceinit')
    text,starts,stop=make_deck(case);(out/'input.spice').write_text(text)
    m=dict(case=case,status='running',ngspice_sha256=digest(args.ngspice),pdk_commit=PDK,
           source_sha256={str(p.relative_to(HERE.parent)):digest(p) for p in (Path(__file__),Path(phase0.__file__),CIRCUIT/'cell.spice',CIRCUIT/'blocks.spice',CIRCUIT/'noise.json')},
           deck_sha256=digest(out/'input.spice'))
    (out/'metadata.json').write_text(json.dumps(m,indent=2)+'\n')
    env=dict(os.environ,SPICE_SCRIPTS=str(args.runtime.resolve()))
    if (args.runtime/'tmpfile.so').exists():
        (out/'tmp').mkdir();env.update(TMPDIR=str((out/'tmp').resolve()),LD_PRELOAD=str((args.runtime/'tmpfile.so').resolve()))
    begin=time.monotonic()
    try:
        r=subprocess.run([str(args.ngspice.resolve()),'-b','input.spice'],cwd=out,env=env,capture_output=True,timeout=900)
        (out/'stdout.log').write_bytes(r.stdout);(out/'stderr.log').write_bytes(r.stderr)
        m.update(returncode=r.returncode,wall_s=time.monotonic()-begin)
        if r.returncode or not (out/'trace.txt').exists():raise RuntimeError('Simulator failed')
        d=np.loadtxt(out/'trace.txt');m['result']=analyze(d,case,starts,stop)
        (out/'trace.txt.gz').write_bytes(gzip.compress((out/'trace.txt').read_bytes(),mtime=0))
        m.update(status='complete',trace_sha256=digest(out/'trace.txt.gz'))
    except Exception as exc:
        m.update(status='failed',error=str(exc),wall_s=time.monotonic()-begin)
        raise
    finally:(out/'metadata.json').write_text(json.dumps(m,indent=2)+'\n')
    print(json.dumps(dict(name=case['name'],status=m['status'],wall_s=m['wall_s'],missed=m['result']['missed_services'])),flush=True)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    for name in ('ngspice','pdk','runtime','cases','output'):p.add_argument('--'+name,type=Path,required=True)
    args=p.parse_args()
    assert digest(args.ngspice)==NGSPICE_SHA,'Use exact ngspice42 binary'
    assert subprocess.check_output(['git','-C',str(args.pdk),'rev-parse','HEAD'],text=True).strip()==PDK
    for case in json.loads(args.cases.read_text()):run(case,args.output/case['name'],args)


if __name__=='__main__':main()
