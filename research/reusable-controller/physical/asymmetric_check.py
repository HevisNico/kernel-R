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
    for path,expected in [(GENERATED,generated),(PORTS,projection)]:
        if args.check:require(path.read_text()==expected,'stale '+path.name)
        else:path.write_text(expected)
    keys=lambda rs:[[r['cell'],r['port']] for r in rs]
    eligible=[r for r in rows if r['eligible']]
    result=dict(rule_commit=RULE_COMMIT,rule_sha256=source.digest(rule),source_commit=source.SOURCE_COMMIT,
        snapshot_sha256=source.SNAPSHOT_SHA256,ports=len(rows),original_eligible=37,
        asymmetric_eligible=len(eligible),contradictions=keys(r for r in rows if r['contradicted']),
        added=keys(r for r in rows if r['eligible'] and not r['original_eligible']),
        lost=keys(r for r in rows if not r['eligible'] and r['original_eligible']),
        eligible_keys=keys(eligible),eps_kappa=eps,
        generated_sha256=source.digest(generated.encode()),ports_sha256=source.digest(projection.encode()),
        script_sha256=source.digest(Path(__file__).read_bytes()),
        scope='Retrospective A1 numeric eligibility; actual-read transfer and physical envelopes remain explicit.')
    if args.report:args.report.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('eligible_keys','added')},indent=2))


if __name__=='__main__':main()
