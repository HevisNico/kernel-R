"""Recompute the pinned #109 campaign and its conditional Lean projection.

Uses public read/current summaries, not private traces or a new simulation.
Fetch SOURCE_COMMIT before running; source files are read from Git objects.
"""
import argparse
import csv
from fractions import Fraction as Q
import hashlib
import io
import json
import math
from pathlib import Path
import statistics
import subprocess
import tarfile

HERE = Path(__file__).resolve().parent
SOURCE_COMMIT = '7ded279f103dab5beb6c1c671f1acbdf4cff18c0'
SNAPSHOT_SHA256 = '0c0743b755508ca84fae594ff28085e82804591c1d0844a5c2ee9302ec6f8846'
U = 'research/circuit/certification-unconditional/'
C = 'research/circuit/certification/'
PATHS = [U.rstrip('/'), C+'results/test', C+'results/preflight',
         C+'calibration.json', C+'predictions.csv', C+'ports.csv']
GENERATED = HERE/'PhysicalEvaluator/CampaignData.lean'
PAD = Q(1, 10**10)


class CampaignError(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise CampaignError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def snapshot():
    raw = subprocess.check_output(['git', 'archive', SOURCE_COMMIT, *PATHS], cwd=HERE.parents[2])
    with tarfile.open(fileobj=io.BytesIO(raw)) as archive:
        files = {m.name: archive.extractfile(m).read() for m in archive if m.isfile()}
    combined = ''.join(p+'\0'+digest(files[p])+'\n' for p in sorted(files)).encode()
    require(len(files) == 1035 and digest(combined) == SNAPSHOT_SHA256, 'pinned snapshot integrity')
    return files


def table(data):
    return list(csv.DictReader(io.StringIO(data.decode())))


def index(rows):
    keyed = {(r['cell'], int(r['port'])): r for r in rows}
    require(len(keyed) == len(rows), 'unique port keys')
    return keyed


def close(actual, recorded, label):
    require(math.isfinite(actual) and abs(actual-float(recorded)) <= 1e-10, label)


def gain(row, early=False):
    q = float(row['q_tc' if early else 'q_peak'])
    x = q-.1-(float(row['c_pre'])-.1)*math.exp(-(.375 if early else .5))
    require(math.isfinite(x) and x > 0, 'positive readout input')
    return math.log(x)


def measurements(rows, charges, early, port, kappa):
    reads = [(r, math.log(float(w[f'w{port}'])), math.log(float(e[f'e{port}'])))
             for r,w,e in zip(rows, charges, early) if int(r['port']) == port]
    silent = [(gain(r), gain(r, True), gi, ge) for r,gi,ge in reads if r['fired'] == '0']
    require(silent, 'silent calibration reads')
    d = statistics.mean(g-gi for g,y,gi,ge in silent)
    de = statistics.mean(y-ge for g,y,gi,ge in silent)
    full = [abs(g-gi-d) for g,y,gi,ge in silent]
    es = [abs(y-ge-de) for g,y,gi,ge in silent]
    ef, registered, left = [], [], 0
    for r,gi,ge in reads:
        if r['fired'] == '1':
            if float(r['fire_latency']) < .76:
                left += 1
            else:
                y = gain(r, True)
                ef.append(abs(y-ge-de))
                registered.append(abs(y+kappa-gi-d))
    return dict(D=d, DE=de, eps=max(full+registered)+.0001,
                eps3=max(full+es+ef)+.0001, full=max(full), early_silent=max(es),
                early_fired=max(ef) if ef else 0., left=left,
                silent=len(silent), fired=len(ef))


def load_run(files, stage, run):
    prefix = U+'results/'+stage+'/'+run['name']
    rows, charges, early = (table(files[prefix+s]) for s in ('.csv','.charge.csv','.early.csv'))
    meta = json.loads(files[prefix+'.json'])
    require(meta['status'] == 'done' and meta['run'] == run and run['noise'] is False,
            'completed noiseless run identity')
    require(digest(files[prefix+'.csv']) == meta['csv_sha256'], 'run CSV hash')
    require(len(meta['trace_sha256']) == 64 and len(meta['ngspice_sha256']) == 64, 'trace/simulator identities')
    require(len(rows) == len(charges) == len(early), 'aligned read/current lengths')
    for i,(r,w,e) in enumerate(zip(rows,charges,early)):
        require(int(r['pulse']) == i and all(r[k] == w[k] == e[k] for k in ('pulse','port')),
                'aligned read/current indices')
        require(r['fired'] in ('0','1'), 'Boolean observation')
        require(all(math.isfinite(float(v)) for v in r.values()), 'finite read summary')
        require(all(math.isfinite(float(x[k])) and float(x[k]) > 0
                    for x,ks in ((w,('w1','w2')),(e,('e1','e2'))) for k in ks),
                'positive independent current integral')
    expected = [1]*40 if run['mode'] == 'leak' else [1]*10+[2]*10+[0]
    require([int(r['port']) for r in rows] == expected, 'run pulse schedule')
    return rows,charges,early


def analyse(files):
    manifest = json.loads(files[U+'manifest.json'])
    cal = json.loads(files[C+'calibration.json'])
    cal_exact = json.loads(files[C+'calibration.json'], parse_float=Q)
    old = index(table(files[C+'ports.csv']))
    prediction = index(table(files[C+'predictions.csv']))
    published = index(table(files[U+'ports_amendment1.csv']))
    cells = {r['cell']:r for r in table(files[U+'cells.csv'])}
    require(len(old) == len(prediction) == len(published) == 200 and
            old.keys() == prediction.keys() == published.keys(), 'complete 200-port cohort')
    require([len(manifest['stages'][s]) for s in ('preflight','scan','gain')] == [2,100,100], '202-run campaign')
    require([r['seed'] for r in manifest['stages']['scan']] == list(range(6001,6101)) and
            [r['seed'] for r in manifest['stages']['gain']] == list(range(6001,6101)), 'ordered complete cell cohorts')
    runs = {}
    for stage in ('preflight','scan','gain'):
        for run in manifest['stages'][stage]:
            runs[stage,run['name']] = load_run(files,stage,run)
            if stage == 'preflight':
                require(files[U+'results/preflight/'+run['name']+'.csv'] ==
                        files[C+'results/preflight/'+run['name']+'.csv'], 'unchanged preflight')
    output, stats = [], {k:0 for k in ('old','status1','status2','status3','contradictions','mu_inside','bracket_inside')}
    for seed in range(6001,6101):
        cell = f't{seed}'
        scan = runs['scan',f'u{seed}_leak']
        train = runs['gain',f'u{seed}_train']
        sc = measurements(*scan,1,cal['kappa'])
        first = next(i for i,r in enumerate(scan[0]) if r['fired'] == '1')
        after = next(i for i in range(first+1,len(scan[0])) if scan[0][i]['fired'] == '0')
        before = scan[0][after-1]
        require(float(before['fire_latency']) >= .76, 'usable scan upper bracket')
        ps = float(scan[0][after]['q_peak'])
        level = float(prediction[cell,1]['level0'])
        base = .1+(float(before['c_pre'])-.1)*math.exp(-.5)
        pf = base+math.exp(gain(before,True)+cal['kappa'])
        require(pf >= ps, 'nonempty threshold bracket')
        h1 = max(abs(ps-level),abs(pf-level))
        h2 = max(abs(ps-level),abs(base+math.exp(gain(before,True)+cal['kappa']+sc['eps'])-level))
        h3 = max(abs(ps-level),abs(base+math.exp(gain(before,True)+cal['kappa']+sc['eps3'])-level))
        mu_cell = (ps+pf)/2-float(prediction[cell,1]['static_level'])
        stats['mu_inside'] += abs(mu_cell-cal['mu']) <= cal['h_mu']
        stats['bracket_inside'] += h1 <= cal['h_mu']
        for field,value in [('Ps',ps),('Pf',pf),('mu_cell',mu_cell),('h1',h1),('h2',h2)]:
            close(value,cells[cell][field], 'cell '+field)
        same = gain(train[0][0])-float(prediction[cell,1]['start_gain'])
        close(same,cells[cell]['same_cell_diff1'],'same-cell distance')
        require(abs(same) <= .0002 and cells[cell]['same_cell']=='True', 'same-cell transfer check')
        noisy_bytes = files[C+'results/test/'+cell+'_train.csv']
        noisy_meta = json.loads(files[C+'results/test/'+cell+'_train.json'])
        require(digest(noisy_bytes) == noisy_meta['csv_sha256'] and noisy_meta['run']['noise'] is True,
                'separate noisy evidence identity')
        noisy = table(noisy_bytes)
        for port in (1,2):
            o,r = old[cell,port],published[cell,port]
            g = measurements(*train,port,cal['kappa'])
            require(g['left'] == sc['left'] == 0, 'no omitted early FIRE')
            for field,value in [('D',g['D']),('eps_peak',g['eps']),('eps3',g['eps3']),
                ('eps3_full_silent',g['full']),('eps3_early_silent',g['early_silent']),
                ('eps3_early_fired',g['early_fired']),('eps3_scan',sc['eps3']),('h3',h3)]:
                close(value,r[field], 'port '+field)
            selected = [x for x in noisy if int(x['port']) == port]
            count = next(i for i,x in enumerate(selected) if x['fired']=='1')
            m = int(prediction[cell,port]['m'])
            require(count == int(r['count']) == int(o['count']) and str(count==m)==r['count_agrees'], 'noisy count crosscheck')
            stats['old'] += o['status'] == 'certified, count confirmed'
            for j,h,eps in [(1,h1,0),(2,h2,g['eps']),(3,h3,g['eps3'])]:
                a,b = float(o['a'])+eps,float(o['B'])+2*eps
                ell = h+float(o['noise'])+.0002
                room = cal['d0']/2-a-b-20/17*ell-1/8000
                for field,value in [(f'ell{j}',ell),(f'room{j}',room)]+([(f'a{j}',a),(f'B{j}',b)] if j>1 else []):
                    close(value,r[field], 'derived '+field)
                bad = any(x.startswith(('a rest state','the latch','the steering')) for x in o['reason'].split('; '))
                status = ('outside the certified domain' if bad or level-ell<.95 or room<=0 else
                          'certified, count confirmed' if count==m else 'certified, count contradicted')
                require(r[f'status{j}'] == status, 'recomputed campaign status')
                stats[f'status{j}'] += status.startswith('certified')
                stats['contradictions'] += status == 'certified, count contradicted'
            values = dict(level=Q(prediction[cell,port]['level0']),dose=cal_exact['d0'],
                          a=Q(o['a'])+PAD,b=Q(o['B'])+PAD,eps=Q(r['eps3'])+PAD,ell=Q(r['ell3'])+PAD)
            room = values['dose']/2-(values['a']+values['eps'])-(values['b']+2*values['eps'])-Q(20,17)*values['ell']-Q(1,8000)
            eligible = r['status3']=='certified, count confirmed'
            require(not eligible or room>0 and values['level']-values['ell']>=Q(19,20), 'outward-rounded domain')
            output.append(dict(cell=seed,port=port,m=m,count=count,eligible=eligible,values=values,
                room=room,eps3=g['eps3'],readings=[x['fired']=='1' for x in selected[:m+1]]))
    require(stats == dict(old=59,status1=58,status2=0,status3=37,contradictions=0,mu_inside=100,bracket_inside=67),
            'published cohort totals')
    return output,stats


def real(x):
    return f'({x.numerator} / {x.denominator} : ℝ)'


def render(rows):
    lines = ['import PhysicalEvaluator.CampaignBridge','',
             'namespace ReusableController.PhysicalEvaluator.CampaignData','']
    entries = []
    for r in rows:
        if not r['eligible']:
            continue
        n = f't{r["cell"]}p{r["port"]}'
        v = r['values']
        obs = '['+', '.join(str(b).lower() for b in r['readings'])+']'
        lines += [f'noncomputable def {n} : CampaignEntry {r["m"]} where',
                  f'  cellId := {r["cell"]}',f'  port := {r["port"]}']
        for field,key in [('level0','level'),('dose0','dose'),('baseA','a'),('baseB','b'),('epsilon','eps'),('ell','ell')]:
            lines.append(f'  {field} := {real(v[key])}')
        lines += [f'  observed := fun k => {obs}[k.val]!',
                  '  ellNonnegative := by norm_num','  levelFloor := by norm_num','  room := by norm_num','']
        entries.append(f'⟨{r["m"]}, {n}⟩')
    lines += ['noncomputable def entries : List (Sigma CampaignEntry) :=', '  ['+', '.join(entries)+']',
              'theorem entry_count : entries.length = 37 := by rfl','']
    old = next(r for r in rows if (r['cell'],r['port'])==(6004,1))['values']
    lines += ['theorem t6004_preparation_budget_rejected :',
              f'    ¬ ({real(old["a"])} + {real(old["eps"])}) + ({real(old["b"])} + 2*{real(old["eps"])}) +',
              f'      20/17*{real(old["ell"])} + 1/8000 < {real(old["dose"])}/2 := by norm_num',
              '', 'end ReusableController.PhysicalEvaluator.CampaignData', '']
    return '\n'.join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true')
    parser.add_argument('--report',type=Path)
    args=parser.parse_args()
    files=snapshot()
    rows,stats=analyse(files)
    generated=render(rows)
    if args.check:
        require(GENERATED.read_text()==generated,'stale campaign Lean projection')
    else:
        GENERATED.write_text(generated)
    def change_csv(path,fn):
        changed=dict(files); records=table(changed[path]);fn(records)
        stream=io.StringIO();w=csv.DictWriter(stream,fieldnames=list(records[0]),lineterminator='\n');w.writeheader();w.writerows(records)
        changed[path]=stream.getvalue().encode();return changed
    controls=[]
    cases=[('forged_eps3',U+'ports_amendment1.csv',lambda rs:rs[0].update(eps3='0')),
           ('forged_status',U+'ports_amendment1.csv',lambda rs:rs[0].update(status3='certified, count confirmed')),
           ('current_row_mismatch',U+'results/gain/u6001_train.early.csv',lambda rs:rs[0].update(pulse='1')),
           ('altered_current',U+'results/gain/u6001_train.early.csv',lambda rs:rs[0].update(e1=str(float(rs[0]['e1'])*1.01))),
           ('missing_port',U+'ports_amendment1.csv',lambda rs:rs.pop()),
           ('forged_room',U+'ports_amendment1.csv',lambda rs:rs[0].update(room3='1'))]
    for name,path,fn in cases:
        try:analyse(change_csv(path,fn))
        except CampaignError as error:controls.append(dict(mutation=name,rejected=True,reason=str(error)))
        else:raise CampaignError('mutation accepted: '+name)
    pairs=[c for c in range(6001,6101) if all(next(r for r in rows if (r['cell'],r['port'])==(c,p))['eligible'] for p in (1,2))]
    report=dict(source_commit=SOURCE_COMMIT,snapshot_sha256=SNAPSHOT_SHA256,source_files=1035,
        checked_runs=202,counts=stats,eps3=dict(min=min(r['eps3'] for r in rows),median=statistics.median(r['eps3'] for r in rows),max=max(r['eps3'] for r in rows)),
        ports_exceeding_old_log_tolerance=sum(r['eps3']>1e-4 for r in rows),eligible_pairs=pairs,
        selected_pair=pairs[0],selection='lowest cell id with both status-3 ports eligible; retrospective',
        retained_negative=dict(cell=6004,port=1,room=float(next(r for r in rows if (r['cell'],r['port'])==(6004,1))['room'])),
        eligible_keys=[[r['cell'],r['port']] for r in rows if r['eligible']],negative_controls=controls,
        generated_sha256=digest(generated.encode()),script_sha256=digest(Path(__file__).read_bytes()),
        limitations=['Published summaries reanalysed; no new simulator run or hardware measurement.',
                     'Current integrals not re-extracted: private compact traces unavailable.',
                     'eps3 is a logarithmic residual after per-port fitted offsets, with declared quadrature margin.',
                     'Noiseless-to-noisy transfer and the post-0.75 FIRE correction remain conditional.',
                     'Threshold bracket sampled once on port 1; future/reset validations are not established.'])
    if args.report:args.report.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('eligible_keys','negative_controls')},indent=2))


if __name__=='__main__':
    main()
