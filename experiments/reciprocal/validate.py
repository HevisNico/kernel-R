"""Routing, bounds, causal contrasts, numerical convergence and independent replay."""
from pathlib import Path
import argparse,json,math
import numpy as np
import simulate as net
from ode_reference import simulate_ode
from engine import Device,NOMINAL


def validate(dest):
    checks=[]
    def check(label,passed,**detail):
        row=dict(test=label,passed=bool(passed),**net.plain(detail));checks.append(row)
        print(json.dumps(row,ensure_ascii=False),flush=True)
    results={name:json.loads((dest/(name+'.json')).read_text()) for name in net.CONFIGS}
    for name,r in results.items():
        cells=[c for s in r['samples'] for c in s['cells']]
        check(name+': bounds',r['status']=='SIMULATED' and all(min(c['gains'])>0 and max(c['gains'])<=4+1e-8 and 0<c['b']<=1.1+1e-8 and 50-1e-6<=c['E']<=100+1e-6 for c in cells))
        births=[0,160,480]
        check(name+': no cell dies',all(c['alive'] for s in r['samples'] for i,c in enumerate(s['cells']) if s['time']>=births[i]))
        for node in range(3):
            history=[s['cells'][node] for s in r['samples']]
            check(name+f': monotone gains/b {net.NAMES[node]}',all(all(a<=b+1e-7 for a,b in zip(x['gains']+[x['b']],y['gains']+[y['b']])) for x,y in zip(history,history[1:])))
        bad=[]
        for arrival in r['arrivals']:
            if arrival['source'] not in net.NAMES:continue
            src=net.NAMES.index(arrival['source']);when=arrival['time']-net.DELAY
            edge=next((e for e in net.EDGES if e['source']==src and e['target']==arrival['node'] and e['port']==arrival['port']),None)
            valid=edge is not None and any(lo<=when<hi for lo,hi in edge['windows']) and any(o['node']==src and abs(o['time']-when)<1e-7 for o in r['outputs'])
            if not valid:bad.append(arrival)
        check(name+': every peer pulse has a causal source',not bad,invalid_arrivals=len(bad))
        check(name+': settings obey ablation',len(r['copies'])==(5 if net.CONFIGS[name]['settings'] else 0))
    analysis=json.loads((dest/'analysis.json').read_text())
    byname={r['configuration']:r for r in analysis['comparisons']}
    for name in ['complet','impulsions']:
        early=byname[name]['early_feedback']
        check(name+': A learns from B before any feedback copy',not early['settings_copies_in_measurement'] and early['A_probe_before']['correct']==0 and early['A_probe_after']['correct']==8)
        check(name+': faster cadence propagates to parents',all(c['recovery_change']>.1 and c['fast_probe_after']['correct']==8 for c in byname[name]['cascade']))
    for name in ['sans_retour','sans_transfert']:
        early=byname[name]['early_feedback']
        check(name+': no feedback leaves A untrained on feedback port',early['A_probe_after']['correct']==0)
    for name in ['complet','impulsions']:
        tight=net.Network(name,rtol=2e-11,atol=2e-13,max_step=.06).run()
        broad=results[name];error=0.;counts=True
        for i in range(3):
            a=[x['time'] for x in broad['outputs'] if x['node']==i];b=[x['time'] for x in tight['outputs'] if x['node']==i]
            counts &= len(a)==len(b)
            if len(a)==len(b):error=max(error,max((abs(x-y) for x,y in zip(a,b)),default=0.))
        check(name+': tighter solver preserves output trace',counts and error<2e-6,max_date_difference=error)
        maxparams=max(abs(x-y) for s,t in zip(broad['samples'],tight['samples']) for c,d in zip(s['cells'],t['cells']) for x,y in zip(c['gains']+[c['b']],d['gains']+[d['b']]))
        check(name+': tighter solver preserves learned settings',maxparams<2e-6,max_parameter_difference=maxparams)
    # Independent one-cell ODE implementation, supplied with the recorded causal arrivals.
    r=results['impulsions']
    for i,birth in enumerate([0.,160.,480.]):
        arrivals=[[a['time']-birth for a in r['arrivals'] if a['node']==i and a['port']==j] for j in range(3)]
        dev=Device(np.broadcast_to(NOMINAL,(3,5)).tolist(),.1,[.025]*3,np.log([.3,1.2,.3]).tolist(),.08,[0]*3)
        independent=simulate_ode(arrivals,dev,net.END-birth)
        recorded=[o['time']-birth for o in r['outputs'] if o['node']==i]
        counts=len(recorded)==len(independent['outputs'])
        error=max((abs(a-b) for a,b in zip(recorded,independent['outputs'])),default=0.) if counts else None
        final=r['samples'][-1]['cells'][i]
        param_error=max([abs(a-b) for a,b in zip(final['gains'],independent['final_gain'])]+[abs(final['b']-independent['final_b'])])
        check('independent replay '+net.NAMES[i],counts and error<2e-6 and param_error<2e-6,max_date_difference=error,max_parameter_difference=param_error)
    report=dict(checks=len(checks),passed=sum(x['passed'] for x in checks),results=checks,
                scope='Numerical/structural checks, not machine-checked correctness or proof over a parameter box')
    (dest/'validation.json').write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n')
    if not all(x['passed'] for x in checks):raise RuntimeError('validation failure')
    return report
if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--out',type=Path,default=net.ROOT/'audit_runs'/'reciprocal')
    validate(parser.parse_args().out)
