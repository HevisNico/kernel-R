"""CI checks published summaries and proofs; no simulator or registered launch."""
import hashlib
import json
import math
from pathlib import Path
import subprocess
import sys

from calibrate import HERE,make_deck,digest,NGSPICE_SHA,PDK
from report import GROUPS


def saved_summary():
    r=json.loads((HERE/'RESULTS.json').read_text())
    cases=[c for group in GROUPS for c in json.loads((HERE/(group+'-cases.json')).read_text())]
    assert len(cases)==26 and len({c['name'] for c in cases})==26
    assert [m['case'] for m in r['records']]==cases
    assert r['registered_campaign_launched'] is False and 'NOT closed' in r['status']
    byname={m['case']['name']:m for m in r['records']}
    evidence={f['path']:f for f in r['evidence_files']}
    expected={c['name']+'/'+name for c in cases for name in ('input.spice','trace.txt.gz','metadata.json','stdout.log','stderr.log')}
    assert len(evidence)==len(r['evidence_files'])==130 and set(evidence)==expected
    for f in evidence.values():
        assert type(f['bytes']) is int and f['bytes']>=0
        assert len(f['sha256'])==64 and int(f['sha256'],16)>=0
    for m in r['records']:
        c=m['case'];deck,starts,stop=make_deck(c)
        assert m['ngspice_sha256']==NGSPICE_SHA and m['pdk_commit']==PDK
        assert m['status']=='complete' and m['returncode']==0
        assert m['wall_s']>0 and math.isfinite(m['wall_s'])
        assert hashlib.sha256(deck.encode()).hexdigest()==m['deck_sha256']==evidence[c['name']+'/input.spice']['sha256']
        assert m['trace_sha256']==evidence[c['name']+'/trace.txt.gz']['sha256']
        assert hashlib.sha256((json.dumps(m,indent=2)+'\n').encode()).hexdigest()==evidence[c['name']+'/metadata.json']['sha256']
        for source,sha in m['source_sha256'].items():assert digest(HERE.parent/source)==sha
        a=m['result']['actions'];assert len(a)==len(c['actions'])
        assert m['result']['simulated_s']==stop and [x['start_s'] for x in a]==starts
        for x,amplitude in zip(a,c['actions']):
            assert x['requested_service']==(amplitude==1 and x['role']=='service')
            if not x['requested_service']:assert x['service_success'] is None
            else:assert x['service_success']==x['pulse_correct']
        assert m['result']['requested_services']==sum(x['requested_service'] for x in a)
        assert m['result']['missed_services']==sum(x['service_success'] is False for x in a)
    for c in r['capacity']:
        a=byname[c['name']]['result']['actions'][0];lat=a['fire_latency_units']
        assert c['latency_units']==lat
        assert c['pre_vmem_mV']==[p['pre_vmem_V']*1000 for p in a['ports']]
        for key,ok in [('C5_nominal',.2665<=lat<=.2685),('P12_corner_prediction',.262<=lat<=.272),('P7_cohort_prediction',.250<=lat<=.280),('ideal_model_window',.239<lat<=.256)]:assert c[key]==ok
    for i,t in enumerate(r['timing_pairs']):
        q=byname[f'timing-pair-{i}-0'];n=byname[f'timing-pair-{i}-1']
        assert t==dict(pair=i,quiet_s=q['wall_s'],noisy_s=n['wall_s'],ratio=n['wall_s']/q['wall_s'],quiet_missed=q['result']['missed_services'],noisy_missed=n['result']['missed_services'])
    f=r['forecast'];factor=max(t['ratio'] for t in r['timing_pairs'])
    assert f['measured_noise_factor_max']==factor
    assert f['quiet_baseline_s_per_440us']==max(35,max(t['quiet_s']/2.5 for t in r['timing_pairs']))
    assert f['planning_noise_factor']==max(1,factor) and f['reserve_factor']==1.25
    estimate=6*((f['service_periods_per_sequence']+1)*f['quiet_baseline_s_per_440us']*max(1,factor)*1.25+30)
    assert f['aggregate_s']==estimate<=14400 and f['sequences']==6
    assert f['machine_a_s']==f['machine_b_s']==estimate/2
    test=json.loads((HERE/'launchkit/SYNTHETIC_TEST.json').read_text())
    for fixture in (test,test['zero_exit_missing_output_fixture']):
        assert fixture['launcher_sha256']==digest(HERE/'launchkit/launch.py')
        assert fixture['unpublished_marker_refused'] and fixture['successful_machine_a']
        assert fixture['alternate_output_relaunches_refused']==['a','b']
        assert fixture['zero_exit_missing_output_refused']
    assert test['all_checks_passed'] and test['timeout_preserved_machine_b']
    assert not (HERE/'PREDICTION.md').exists() and not (HERE/'CAMPAIGN.json').exists()
    print('PASS: published summaries, source identities, synthetic report and forecast; raw waveforms not checked by CI',flush=True)


def main():
    saved_summary()
    for where in (HERE,HERE/'launchkit'):
        subprocess.run([sys.executable,'-B','-m','unittest','discover','-s',str(where),'-p','test_*.py','-v'],check=True)
    subprocess.run(['lake','build'],cwd=HERE/'lean',check=True)
    subprocess.run([sys.executable,'-B','check_negative.py'],cwd=HERE/'lean',check=True)


if __name__=='__main__':main()
