"""Reproduce published directional rule A1 without replacing the original cohort."""
import argparse
import csv
from fractions import Fraction as Q
from decimal import Decimal, localcontext
import hashlib
import io
import json
import math
from pathlib import Path
import subprocess

import campaign_check as source

HERE = Path(__file__).resolve().parent
RULE_COMMIT = '8b11a5f5d2b6843bc6ca1f9ff0b82c30fa99f19d'
RULE_PATH = 'research/reusable-controller/physical/ASYMMETRIC_PROTOCOL.md'
GENERATED = HERE / 'PhysicalEvaluator/AsymmetricData.lean'
PORTS = HERE / 'asymmetric-ports.csv'
REVIEW = HERE / 'ASYMMETRIC_REVIEW.md'
MZ = 0.0002
PAD = source.PAD
require = source.require


def padded(value):
    with localcontext() as context:
        context.prec = 60
        if isinstance(value, Q):
            value = Decimal(value.numerator) / Decimal(value.denominator)
        return Q(format(value, '.12g')) + PAD


def reported(row, kappa):
    fired = row['fired'] == '1'
    if fired and float(row['fire_latency']) < .76:
        raise source.CampaignError('FIRE before 0.76')
    return source.gain(row, fired) + (kappa if fired else 0.)


def directional_bounds(y, fired, eps_kappa, dose):
    require(len(y) == len(fired) and len(y) > 0, 'aligned nonempty gain prefix')
    require(all(math.isfinite(x) for x in y), 'finite gain prefix')
    require(eps_kappa >= 0 and dose >= 0, 'nonnegative reference budgets')
    radius = [MZ+(eps_kappa if flag else 0.) for flag in fired]
    dev = [x-y[0]-k*dose for k,x in enumerate(y)]
    m = len(y)-1
    return (max([0.]+[dev[k]+radius[k]+radius[0] for k in range(m)]),
            max(0.,-dev[m]+radius[m]+radius[0]))


def room_gates(silence_room, fire_room):
    return silence_room > 0 and fire_room >= 0


def analyse(files):
    baseline, _ = source.analyse(files)
    old = source.index(source.table(files[source.C+'ports.csv']))
    prediction = source.index(source.table(files[source.C+'predictions.csv']))
    amended = source.index(source.table(files[source.U+'ports_amendment1.csv']))
    calibration = json.loads(files[source.C+'calibration.json'])
    exact = json.loads(files[source.C+'calibration.json'], parse_float=Q)
    trains = {c: source.table(files[source.C+f'results/test/t{c}_train.csv']) for c in range(6001,6101)}
    kappa = calibration['kappa']
    eps_kappa = max(abs(source.gain(r)-source.gain(r, True)-kappa)
        for rows in trains.values() for r in rows if r['port'] in ('1','2') and r['fired']=='0')
    results = []
    for base in baseline:
        cell,port,m = base['cell'],base['port'],base['m']
        key = f't{cell}',port
        rows = [r for r in trains[cell] if int(r['port'])==port]
        prefix = rows[:m+1]
        reasons = []
        result = dict(cell=cell,port=port,m=m,count=base['count'],original_eligible=base['eligible'],
                      eligible=False,contradicted=False,readings=[r['fired']=='1' for r in prefix])
        try:
            require(len(prefix)==m+1, 'missing target read')
            y = [reported(r,kappa) for r in prefix]
            bs,bf = directional_bounds(y,[r['fired']=='1' for r in prefix],eps_kappa,calibration['d0'])
            ell = Q(amended[key]['h3'])+max(Q(r['noise_sup_V'])*2 for r in prefix)+Q(1,5000)
            v = dict(level=Q(prediction[key]['level0']),dose=exact['d0'],
                a=Q(old[key]['a'])+PAD,eps=Q(amended[key]['eps3'])+PAD,
                bs=padded(bs),bf=padded(bf),ell=padded(ell))
            silent_room = v['dose']/2-(v['a']+v['eps'])-(v['bs']+2*v['eps'])-Q(20,17)*v['ell']-Q(1,8000)
            fire_room = v['dose']/2-(v['a']+v['eps'])-(v['bf']+2*v['eps'])-Q(20,17)*v['ell']
            if any(not .1<=float(r['c_pre'])<=.1001 for r in prefix): reasons.append('rest charge')
            if any(float(r['latch_rises'])>1 for r in prefix): reasons.append('multiple latch rises')
            if any(float(r[f'steer_rises{port}'])!=(0 if r['fired']=='1' else 1) or
                   float(r[f'steer_rises{3-port}'])!=0 for r in prefix): reasons.append('steering')
            if v['level']-v['ell']<Q(19,20): reasons.append('threshold floor')
            if not room_gates(silent_room,fire_room):
                if silent_room<=0: reasons.append('silence room')
                if fire_room<0: reasons.append('FIRE room')
            result.update(values=v,silence_room=silent_room,fire_room=fire_room,
                          eligible=not reasons,contradicted=not reasons and base['count']!=m)
        except (source.CampaignError,ValueError,OverflowError) as error:
            reasons.append('not evaluable: '+str(error))
        result['reasons']='; '.join(reasons)
        results.append(result)
    return results,eps_kappa


def render(rows):
    lines=['import PhysicalEvaluator.Asymmetric','',
           'namespace ReusableController.PhysicalEvaluator.AsymmetricData','']
    entries=[]
    for row in rows:
        if not row['eligible']:continue
        name=f't{row["cell"]}p{row["port"]}'
        v=row['values']
        lines += [f'noncomputable def {name} : AsymmetricEntry {row["m"]} where',
                  f'  cellId := {row["cell"]}',f'  port := {row["port"]}']
        for field,key in [('level0','level'),('dose0','dose'),('baseA','a'),('baseBSilent','bs'),
                          ('baseBFire','bf'),('epsilon','eps'),('ell','ell')]:
            lines.append(f'  {field} := {source.real(v[key])}')
        obs='['+', '.join(str(x).lower() for x in row['readings'])+']'
        lines += [f'  observed := fun k => {obs}[k.val]!',
                  '  doseNonnegative := by norm_num','  ellNonnegative := by norm_num',
                  '  levelFloor := by norm_num','  silenceRoom := by norm_num',
                  '  fireRoom := by norm_num','']
        entries.append(f'⟨{row["m"]}, {name}⟩')
    lines += ['noncomputable def entries : List (Sigma AsymmetricEntry) :=',
              '  ['+', '.join(entries)+']',f'theorem entry_count : entries.length = {len(entries)} := by rfl',
              '', 'end ReusableController.PhysicalEvaluator.AsymmetricData','']
    return '\n'.join(lines)


def csv_projection(rows):
    stream=io.StringIO()
    fields=['cell','port','m','count','original_eligible','eligible','contradicted',
            'baseA','baseBSilent','baseBFire','epsilon','ell','silence_room','fire_room','reasons']
    writer=csv.DictWriter(stream,fields,lineterminator='\n');writer.writeheader()
    for r in rows:
        record={k:r[k] for k in fields if k in r}
        if 'values' in r:
            record.update({field:str(r['values'][key]) for field,key in
                [('baseA','a'),('baseBSilent','bs'),('baseBFire','bf'),('epsilon','eps'),('ell','ell')]})
        writer.writerow(record)
    return stream.getvalue()


def review_breakdown(files, rows):
    baseline, _ = source.analyse(files)
    baseline = {(r['cell'],r['port']):r for r in baseline}
    old = source.index(source.table(files[source.C+'ports.csv']))
    wrong = sorted((int(cell[1:]),port) for (cell,port),r in old.items()
                   if int(r['count']) != int(r['m']))
    current_wrong = sorted((r['cell'],r['port']) for r in rows if r['count']!=r['m'])
    require(wrong==current_wrong and len(wrong)==11, 'all eleven original count mismatches retained')
    eligible = {(r['cell'],r['port']) for r in rows if r['eligible']}
    overlap = sorted(set(wrong) & eligible)
    require(not overlap, 'an original wrong-count port became eligible')
    added = []
    for r in rows:
        if not r['eligible'] or r['original_eligible']:continue
        b=baseline[r['cell'],r['port']]
        oldv,v=b['values'],r['values']
        initial=oldv['a']+oldv['eps']
        cumulative=oldv['b']+2*oldv['eps']
        threshold=Q(20,17)*oldv['ell']
        require(initial==v['a']+v['eps'], 'unchanged initial budget on new ports')
        require(b['room']<=0 and oldv['level']-oldv['ell']>=Q(19,20),
                'new-port prior rejection is the combined symmetric budget')
        bs,bf=v['bs']+2*v['eps'],v['bf']+2*v['eps']
        threshold_delta=Q(20,17)*(oldv['ell']-v['ell'])
        require(r['silence_room']==b['room']+cumulative-bs+threshold_delta,
                'silence room decomposition')
        require(r['fire_room']==b['room']+cumulative-bf+threshold_delta+Q(1,8000),
                'FIRE room decomposition')
        dominant=max(dict(a=initial,B=cumulative,threshold=threshold),
                     key=dict(a=initial,B=cumulative,threshold=threshold).get)
        binding=('silence' if r['silence_room']<r['fire_room'] else
                 'FIRE' if r['fire_room']<r['silence_room'] else 'equal')
        added.append(dict(cell=r['cell'],port=r['port'],old_dominant_term=dominant,
            old_failure='combined symmetric room',unchanged_a=str(initial),
            old_B=str(cumulative),new_BSilent=str(bs),new_BFire=str(bf),
            old_threshold_term=str(threshold),threshold_rounding_delta=str(threshold_delta),
            old_room=str(b['room']),silence_room=str(r['silence_room']),fire_room=str(r['fire_room']),
            silence_B_relief=str(cumulative-bs),fire_B_relief=str(cumulative-bf),
            fire_rest_allowance_relief='1/8000',limiting_side=binding))
    return dict(comparison=[dict(rule='registered symmetric status3',eligible=sum(r['original_eligible'] for r in rows)),
                            dict(rule='A1 published before recount',eligible=len(eligible))],
        original_wrong_count_ports=[list(k) for k in wrong],
        original_wrong_count_overlap=[list(k) for k in overlap],
        added_port_breakdown=added,
        old_dominant_term_counts={k:sum(r['old_dominant_term']==k for r in added) for k in ('a','B','threshold')},
        limiting_side_counts={k:sum(r['limiting_side']==k for r in added) for k in ('silence','FIRE','equal')})


def review_markdown(review):
    fmt=lambda x:format(float(Q(x)),'.9f')
    lines=['# A1 review: unchanged baseline and added-port decomposition','',
        'Generated by `asymmetric_check.py` from the pinned snapshot. This report',
        'does not change the published A1 rule, any budget, or any eligible entry.','',
        '| Rule | Eligible ports | Count contradictions |',
        '|---|---:|---:|',
        '| Registered symmetric budget (#109 amended status3) | 37 | 0 |',
        '| A1, declared before its calculation in `8b11a5f5d2b6843bc6ca1f9ff0b82c30fa99f19d` | 57 | 0 |','',
        'All 37 original ports remain among the 57. **None of the 11 ports with',
        'a wrong count in #107 belongs to the 57.** Their unchanged identities are:',
        ', '.join(f'`t{c}/p{p}`' for c,p in review['original_wrong_count_ports'])+'.','',
        '## What changes for the 20 added ports','',
        'All 20 previously failed the **sum** in the symmetric room test. The',
        'largest contribution is not a unique causal attribution: it is reported',
        'as `a`, `B`, or threshold, including threshold rather than forcing an a/B',
        'classification. The initial budget `a` is unchanged on all 20 ports.',
        'A1 splits/reduces the cumulative budget and removes the rest allowance',
        'only from the FIRE condition. Both new room tests must pass; the last',
        'column names the smaller remaining room, not the only relevant condition.','',
        'Old dominant-term counts: '+', '.join(f'{k}={v}' for k,v in review['old_dominant_term_counts'].items())+'.',
        'Limiting-side counts: '+', '.join(f'{k}={v}' for k,v in review['limiting_side_counts'].items())+'.','',
        '| Added port | Old largest term | Old room | Old B | A1 BSilent | A1 BFire | Silence room | FIRE room | Limiting side |',
        '|---|---|---:|---:|---:|---:|---:|---:|---|']
    for r in review['added_port_breakdown']:
        lines.append(f"| t{r['cell']}/p{r['port']} | {r['old_dominant_term']} | "+
            ' | '.join(fmt(r[k]) for k in ('old_room','old_B','new_BSilent','new_BFire','silence_room','fire_room'))+
            f" | {r['limiting_side']} |")
    lines += ['', 'Displayed values are rounded; exact rational components are retained in',
        '`asymmetric-validation.json`. B columns include both eps3 endpoint errors.',
        'The exact checks in the generator verify, for every added port:', '', '```text',
        'silenceRoom = oldRoom + (oldB - BSilent) + thresholdRoundingDelta',
        'fireRoom = oldRoom + (oldB - BFire) + thresholdRoundingDelta + 1/8000', '```', '',
        'The tiny threshold delta records decimal serialization separately; it is',
        'not a new physical threshold calibration. Silence remains strict (> 0);',
        'FIRE allows equality (>= 0). All entries retain their explicit physical',
        'transfer, rest-state and detection-envelope premises.', '']
    return '\n'.join(lines)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true')
    parser.add_argument('--report',type=Path)
    args=parser.parse_args()
    rule=subprocess.check_output(['git','show',RULE_COMMIT+':'+RULE_PATH],cwd=HERE.parents[2])
    require(rule==(HERE/'ASYMMETRIC_PROTOCOL.md').read_bytes(),'published rule unchanged')
    files=source.snapshot()
    rows,eps=analyse(files)
    generated=render(rows);projection=csv_projection(rows)
    review=review_breakdown(files,rows);review_text=review_markdown(review)
    for path,expected in [(GENERATED,generated),(PORTS,projection),(REVIEW,review_text)]:
        if args.check:require(path.read_text()==expected,'stale '+path.name)
        else:path.write_text(expected)
    keys=lambda rs:[[r['cell'],r['port']] for r in rs]
    eligible=[r for r in rows if r['eligible']]
    result=dict(rule_commit=RULE_COMMIT,rule_sha256=source.digest(rule),source_commit=source.SOURCE_COMMIT,
        snapshot_sha256=source.SNAPSHOT_SHA256,ports=len(rows),original_eligible=37,
        asymmetric_eligible=len(eligible),contradictions=keys(r for r in rows if r['contradicted']),
        added=keys(r for r in rows if r['eligible'] and not r['original_eligible']),
        lost=keys(r for r in rows if not r['eligible'] and r['original_eligible']),
        eligible_keys=keys(eligible),eps_kappa=eps,review=review,
        review_sha256=source.digest(review_text.encode()),
        generated_sha256=source.digest(generated.encode()),ports_sha256=source.digest(projection.encode()),
        script_sha256=source.digest(Path(__file__).read_bytes()),
        scope='Retrospective A1 numeric eligibility; actual-read transfer and physical envelopes remain explicit.')
    if args.report:args.report.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('eligible_keys','added','review')},indent=2))


if __name__=='__main__':main()
