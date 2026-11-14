"""Re-extract qualification evidence. Does not launch a simulator."""
import argparse
import gzip
import hashlib
import io
import json
from pathlib import Path

import numpy as np

from calibrate import HERE, analyze,make_deck,digest

GROUPS=('capacity','capacity-followup','domain','numerics','timing')


def collect(root):
    cases=[]
    for group in GROUPS:cases.extend(json.loads((HERE/(group+'-cases.json')).read_text()))
    expected={c['name'] for c in cases}
    if {p.parent.name for p in root.glob('*/metadata.json')}!=expected:
        raise ValueError('Incomplete or unexpected qualification inventory')
    records=[];files=[]
    for case in cases:
        folder=root/case['name'];m=json.loads((folder/'metadata.json').read_text())
        if m['case']!=case:raise ValueError('Case differs')
        if m['status']!='complete':raise ValueError('Noncomplete calibration retained: '+case['name'])
        text,starts,stop=make_deck(case)
        if hashlib.sha256(text.encode()).hexdigest()!=m['deck_sha256'] or digest(folder/'input.spice')!=m['deck_sha256']:raise ValueError('Deck changed')
        for name,sha in m['source_sha256'].items():
            if digest(HERE.parent/name)!=sha:raise ValueError('Executed source changed: '+name)
        raw=(folder/'trace.txt.gz').read_bytes()
        if hashlib.sha256(raw).hexdigest()!=m['trace_sha256']:raise ValueError('Raw bytes changed')
        d=np.loadtxt(io.BytesIO(gzip.decompress(raw)))
        result=analyze(d,case,starts,stop)
        if result!=m['result']:raise ValueError('Waveform extraction differs')
        records.append(m)
        for name in ('input.spice','trace.txt.gz','metadata.json','stdout.log','stderr.log'):
            f=folder/name;files.append(dict(path=case['name']+'/'+name,bytes=f.stat().st_size,sha256=digest(f)))
    byname={r['case']['name']:r for r in records}
    capacity=[]
    for r in records:
        if r['case'].get('joint'):
            a=r['result']['actions'][0];lat=a['fire_latency_units']
            capacity.append(dict(name=r['case']['name'],pre_vmem_mV=[p['pre_vmem_V']*1000 for p in a['ports']],
                latency_units=lat,C5_nominal=.2665<=lat<=.2685,
                P12_corner_prediction=.262<=lat<=.272,P7_cohort_prediction=.250<=lat<=.280,
                ideal_model_window=.239<lat<=.256))
    timings=[]
    for i in range(3):
        q=byname[f'timing-pair-{i}-0'];n=byname[f'timing-pair-{i}-1']
        timings.append(dict(pair=i,quiet_s=q['wall_s'],noisy_s=n['wall_s'],ratio=n['wall_s']/q['wall_s'],
                            quiet_missed=q['result']['missed_services'],noisy_missed=n['result']['missed_services']))
    factor=max(t['ratio'] for t in timings)
    # Conservative empirical planning rate, not a runtime guarantee. This
    # keeps the old 35s/period baseline unless the isolated quiet runs exceed it.
    baseline=max(35.0,max(t['quiet_s']/2.5 for t in timings))
    rate=baseline*max(1.0,factor)*1.25
    def estimate(horizon):return 6*((horizon+1)*rate+30)
    horizon=32
    while horizon and estimate(horizon)>14400:horizon-=1
    if horizon<1:raise ValueError('No nonempty proposed campaign fits budget')
    forecast=dict(status='provisional packing only; no registered scenarios or seeds',
                  quiet_baseline_s_per_440us=baseline,measured_noise_factor_max=factor,
                  planning_noise_factor=max(1.0,factor),reserve_factor=1.25,startup_extra_s_per_run=30,
                  sequences=6,service_periods_per_sequence=horizon,initial_32_period_estimate_s=estimate(32),
                  aggregate_s=estimate(horizon),machine_a_s=estimate(horizon)/2,machine_b_s=estimate(horizon)/2,
                  split='three sequences per machine; scenario identities remain unassigned')
    return dict(status='qualification evidence and conditional model proof; physical certificate NOT closed',
                registered_campaign_launched=False,records=records,capacity=capacity,timing_pairs=timings,
                forecast=forecast,evidence_files=files)


def check_trace_hashes(root,deterministic_only=False):
    saved=json.loads((HERE/'RESULTS.json').read_text())
    records=[r for r in saved['records'] if not deterministic_only or not r['case'].get('noise')]
    for record in records:
        path=root/record['case']['name']/'trace.txt.gz'
        if digest(path)!=record['trace_sha256']:
            raise ValueError('Waveform digest differs: '+str(path))
    print(f'PASS: {len(records)} waveform SHA-256 identities')


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--generated',type=Path,default=HERE/'generated');p.add_argument('--check',action='store_true')
    p.add_argument('--check-traces',action='store_true');p.add_argument('--deterministic-only',action='store_true')
    args=p.parse_args()
    if args.check_traces:
        check_trace_hashes(args.generated,args.deterministic_only);return
    if args.deterministic_only:p.error('--deterministic-only requires --check-traces')
    result=collect(args.generated);target=HERE/'RESULTS.json'
    if args.check:
        assert json.loads(target.read_text())==result
        print('PASS: all qualification waveforms, sources, metadata and derived report')
    else:target.write_text(json.dumps(result,indent=2)+'\n')


if __name__=='__main__':main()
