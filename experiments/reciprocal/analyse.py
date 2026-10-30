"""Separate continuous R learning, explicit setting copies, and autonomous probes."""
from pathlib import Path
import argparse,json
import numpy as np
from engine import Device,NOMINAL,simulate
from simulate import CONFIGS,NAMES,plain


def snapshot(result,when):return min(result['samples'],key=lambda s:abs(s['time']-when))


def probe(cell,port,gap=20.,count=8):
    dates=[k*gap for k in range(count)];arr=[[],[],[]];arr[port]=dates
    dev=Device(np.broadcast_to(NOMINAL,(3,5)).tolist(),.1,[.025]*3,np.log(cell['gains']).tolist(),cell['b'],[0]*3)
    r=simulate(arr,dev,dates[-1]+20.,mode='fixed')
    counts=[sum(s<=t<s+gap for t in r['outputs']) for s in dates]
    return dict(port=port,gap=gap,count=count,responses=counts,correct=sum(c==1 for c in counts),
                all_correct=all(c==1 for c in counts),learning=False,peers_connected=False)


def analyze(dest):
    rows=[]
    for name in CONFIGS:
        r=json.loads((dest/(name+'.json')).read_text())
        if r['status']!='SIMULATED':raise RuntimeError('simulation did not complete')
        a0=snapshot(r,319.9)['cells'][0];a1=snapshot(r,459.9)['cells'][0]
        old=snapshot(r,639.9)['cells'];new=snapshot(r,789.9)['cells']
        early=dict(A_feedback_gain_before=a0['gains'][2],A_feedback_gain_after=a1['gains'][2],
                   A_log_gain_change=float(np.log(a1['gains'][2]/a0['gains'][2])),
                   A_probe_before=probe(a0,2),A_probe_after=probe(a1,2),
                   settings_copies_in_measurement=[c for c in r['copies'] if 319.9<c['time']<=459.9])
        cascade=[]
        for i,port in [(0,2),(1,2),(2,0)]:
            cascade.append(dict(cell=NAMES[i],recovery_before=old[i]['b'],recovery_after=new[i]['b'],
                                recovery_change=new[i]['b']-old[i]['b'],
                                fast_probe_before=probe(old[i],port,4.),fast_probe_after=probe(new[i],port,4.)))
        matrix=[dict(cell=NAMES[i],port=j,slow=probe(new[i],j),fast=probe(new[i],j,4.)) for i in range(3) for j in range(3)]
        rows.append(dict(configuration=name,early_feedback=early,cascade=cascade,final_probes=matrix,
                         total_firings=len(r['outputs']),tail_firings_after_900=sum(x['time']>=900 for x in r['outputs']),
                         min_observed_energy=r['min_observed_energy'],copies=len(r['copies'])))
        print(name,'A feedback',early['A_feedback_gain_before'],'->',early['A_feedback_gain_after'],
              'probe',early['A_probe_before']['correct'],'->',early['A_probe_after']['correct'],
              'cadence',[(x['cell'],round(x['recovery_before'],3),round(x['recovery_after'],3),x['fast_probe_before']['correct'],x['fast_probe_after']['correct']) for x in cascade],
              'tail',rows[-1]['tail_firings_after_900'],flush=True)
    report=plain(dict(scope='Isolated standardized-rest probes with plasticity disabled; peer pulses and parameter copying absent during probes',
                      note='Probes use learned gains/b on independent cell copies; they do not reset the live network',comparisons=rows))
    (dest/'analysis.json').write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n')
    return report
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--out',type=Path,default=Path(__file__).resolve().parents[2]/'audit_runs'/'reciprocal')
    analyze(p.parse_args().out)
