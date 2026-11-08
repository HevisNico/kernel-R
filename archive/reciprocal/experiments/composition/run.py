"""Supplementary numerical chain checks using the unchanged single-cell R engine.

These runs check the theorem against a different numerical implementation;
they are not the proof of arbitrary depth or the entire parameter boxes.
"""
from pathlib import Path
from bisect import bisect_right
from fractions import Fraction
import argparse,hashlib,json,math,sys
import numpy as np

ROOT=Path(__file__).resolve().parents[2]
ENGINE=ROOT/'experiments/reciprocal' if (ROOT/'experiments/reciprocal').exists() else ROOT/'02_R_Simulation'
CODE=ROOT/'certify/reciprocal_composition' if (ROOT/'certify/reciprocal_composition').exists() else ROOT/'12_Certified_N_Cell_Composition/code'
sys.path.insert(0,str(ENGINE))
from engine import Device,simulate,NOMINAL
sys.path.insert(0,str(CODE))
from algebra import instantiate

def require(condition,message):
    if not condition: raise RuntimeError(message)

def probe(device,gains,b,port):
    d=Device(params=device.params,initial_q=.1,initial_m=[.025]*3,
        initial_z=np.log(gains).tolist(),initial_b=b,initial_aux=[0]*3)
    arrivals=[[],[],[]];arrivals[port]=list(range(0,29,4))
    return len(simulate(arrivals,d,40,mode='fixed',fixed={'g':gains,'b':b})['outputs'])

def run_case(n,pulses,epsilon,jitter_kind,seed):
    instance=instantiate(n,pulses)
    rng=np.random.default_rng(seed)
    sigma=float(Fraction(instance['per_link_jitter']))
    source_pulses=instance['source_pulses']
    end=float(Fraction(instance['quiescent_by']))-160
    packet=[dict(time=float(4*i),origin=i) for i in range(source_pulses)]
    rows=[]
    for j in range(n):
        params=(np.tile(NOMINAL,(3,1))*rng.uniform(1-epsilon,1+epsilon,(3,5))).tolist()
        birth_g=np.array([.3,1.2,.3])*np.exp(rng.uniform(-1e-5,1e-5,3))
        birth_b=.08+float(rng.uniform(-1e-5,1e-5))
        birth=Device(params=params,initial_q=.1+float(rng.uniform(-1e-5,1e-5)),
            initial_m=(.025+rng.uniform(-1e-5,1e-5,3)).tolist(),initial_z=np.log(birth_g).tolist(),
            initial_b=birth_b,initial_aux=[0]*3)
        training=[[],[],[]];training[1 if j==0 else 2]=list(range(0,121,8))
        prepared=simulate(training,birth,160)
        require(len(prepared['outputs'])==(14 if j==0 else 12),'preparation emission count')
        state=prepared['final_state']
        require(state['main_mode']==0 and state['aux_modes']==[0]*3 and not any(state['raw_active']),'preparation not quiescent')
        d=Device(params=params,initial_q=state['q'],initial_m=state['aux_charge'],
            initial_z=np.log(prepared['final_gain']).tolist(),initial_b=prepared['final_b'],initial_aux=[0]*3)
        port=0 if j==0 else 2
        arrivals=[[],[],[]];arrivals[port]=[p['time'] for p in packet]
        result=simulate(arrivals,d,end)
        outgoing=[]
        for t in result['outputs']:
            index=bisect_right(arrivals[port],t)-1
            require(index>=0 and 0<t-arrivals[port][index]<1,'output outside its certified input support')
            outgoing.append(dict(time=t,origin=packet[index]['origin']))
        expected=source_pulses-5-2*j
        require(len(outgoing)==expected,'fast emission count at cell '+str(j))
        delta_b=result['final_b']-prepared['final_b']
        require(abs(delta_b-.2)<1e-7,'recovery dose at cell '+str(j))
        require(abs(result['final_gain'][port]/birth_g[port]-math.exp(2.4))<1e-6,'gain dose at cell '+str(j))
        require([p['origin'] for p in outgoing[-8:]]==list(range(source_pulses-8,source_pulses)),'final source tail not transmitted')
        before=probe(d,prepared['final_gain'],prepared['final_b'],port)
        after=probe(d,result['final_gain'],result['final_b'],port)
        require(before==(0 if j==0 else 4) and after==8,'retained frozen probe')
        row=dict(index_from_leaf=j,params=params,birth_gains=birth_g.tolist(),birth_b=birth_b,
            preparation_emissions=len(prepared['outputs']),fast_emissions=len(outgoing),
            fast_recovery_change=delta_b,final_b=result['final_b'],final_active_gain=result['final_gain'][port],
            probe_before=before,probe_after=after,last_eight=[pulse.copy() for pulse in outgoing[-8:]])
        if j<n-1:
            centre=float(rng.uniform(.3+sigma,.4-sigma)) if sigma<.05 else .35
            for i,pulse in enumerate(outgoing):
                noise=sigma*(1 if i%2==0 else -1) if jitter_kind=='alternating' else float(rng.uniform(-sigma,sigma))
                pulse['time']+=centre+noise
            row['outgoing_wire_centre']=centre
        rows.append(row);packet=outgoing
    return dict(status='NUMERICALLY_CHECKED_NOT_A_PROOF',epsilon=epsilon,jitter_kind=jitter_kind,seed=seed,instance=instance,
        root_emissions=len(packet),total_fast_emissions=sum(r['fast_emissions'] for r in rows),cells=rows)

def run(out):
    cases=[]
    for args in [(1,None,0.,'alternating',11),(3,25,0.,'alternating',12),
            (4,None,.1,'alternating',13),(16,None,.1,'alternating',14),(32,None,.1,'random',15)]:
        case=run_case(*args);cases.append(case)
        print(json.dumps(dict(cells=args[0],status=case['status'],root_emissions=case['root_emissions'])),flush=True)
    report=dict(scope='Supplementary floating-point checks, not universal proofs',cases=cases,
        source_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [Path(__file__),ENGINE/'engine.py']})
    out.parent.mkdir(parents=True,exist_ok=True);out.write_text(json.dumps(report,indent=2)+'\n')
    return report

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--out',type=Path,required=True);a=p.parse_args()
    run(a.out)
