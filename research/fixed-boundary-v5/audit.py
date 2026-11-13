"""Independent arithmetic audit of saved v5 evidence; never runs a controller.

This module reads existing scenarios and traces. It does not preview seeds,
query Lean, or execute a registered trajectory. Seed draws are checked only
after their scenario files exist as recorded evidence. Source validation is supplied
by mandatory runner/verification preflight through provenance_issues.
"""
import csv
from fractions import Fraction
import gzip
import hashlib
import json
import random
from pathlib import Path
from statistics import median

from common import FIELDS, chain_hash

N, H, S, D, C, INITIAL = 1320, 150, 100, 220, 660, 440
TEXT = {'action', 'chain_previous', 'row_hash'}
SEEDS = list(range(2026111301, 2026111313))
NAMES = ['known', *['seed'+str(s) for s in SEEDS], 'outside']


def load_rows(path):
    with gzip.open(path, 'rt', newline='') as stream:
        reader = csv.DictReader(stream)
        if tuple(reader.fieldnames or ()) != tuple(FIELDS):
            raise ValueError('Noncanonical trace fields')
        rows = []
        for raw in reader:
            if None in raw or any(value is None for value in raw.values()):
                raise ValueError('Truncated or extra trace fields')
            rows.append({k: v if k in TEXT else int(v) if v else None for k, v in raw.items()})
        return rows


def scenario_issues(scenario, name):
    issues = []
    if scenario.get('name') != name:
        issues.append('scenario identity differs: '+name)
    for key, lower, upper in (('rates', 0, 170 if name == 'outside' else H),
                              ('reserve_errors', -2, 2), ('rate_errors', -1, 1)):
        values = scenario.get(key)
        if (not isinstance(values, list) or len(values) != N+1
                or any(type(v) is not int or not lower <= v <= upper for v in values)):
            issues.append('scenario array invalid: '+name+':'+key)
    if issues:
        return issues
    if name in ('known', 'outside'):
        after = 170 if name == 'outside' else 140
        if scenario['rates'] != [10 if t < 661 else after for t in range(N+1)]:
            issues.append('deterministic registered plant differs: '+name)
        if scenario['reserve_errors'] != [(7*t+1)%5-2 for t in range(N+1)]:
            issues.append('deterministic reserve errors differ: '+name)
        if scenario['rate_errors'] != [(5*t+2)%3-1 for t in range(N+1)]:
            issues.append('deterministic rate errors differ: '+name)
    else:
        seed = int(name.removeprefix('seed'))
        if scenario.get('seed') != seed:
            issues.append('registered seed identity differs: '+name)
        # Verify only an already saved scenario's declared draws. This audit
        # is called after the registered batch, never to preview a seed.
        plant, reserve, rate_sensor = (random.Random(seed),random.Random(seed+100000),
                                       random.Random(seed+200000))
        if seed <= 2026111304:
            first = 10*plant.randrange(16)
            at = plant.randrange(1,N+1)
            second = 10*plant.randrange(16)
            expected_rates = [first if t < at else second for t in range(N+1)]
            kind = 'jump'
        elif seed <= 2026111308:
            current = 10*plant.randrange(16)
            expected_rates = [current]
            for t in range(1,N+1):
                if t % 20 == 0:
                    current = min(H,max(0,current+plant.choice((-10,0,10))))
                expected_rates.append(current)
            kind = 'walk'
        else:
            expected_rates = [10*plant.randrange(16) for _ in range(N+1)]
            kind = 'jitter'
        if scenario.get('kind') != kind or scenario['rates'] != expected_rates:
            issues.append('saved plant differs from registered seed draws: '+name)
        if scenario['reserve_errors'] != [reserve.randint(-2,2) for _ in range(N+1)]:
            issues.append('saved reserve errors differ from registered seed draws: '+name)
        if scenario['rate_errors'] != [rate_sensor.randint(-1,1) for _ in range(N+1)]:
            issues.append('saved rate errors differ from registered seed draws: '+name)
    return issues


def audit_trace(scenario, policy, rows):
    issues = []
    def check(ok, t, message):
        if not ok:
            issues.append(f't={t}: {message}')
    check(policy in ('early', 'prudent'), -1, 'known policy')
    check(len(rows) == N+1, -1, 'complete registered horizon')
    required = ('t', 'rate', 'pre', 'post', 'probe', 'delivered', 'probes', 'writes',
                'saturation', 'refused', 'conditional_pre', 'conditional_post', 'sampled_safe')
    for index, row in enumerate(rows):
        if set(row) != set(FIELDS) or any(type(row.get(k)) is not int for k in required):
            return issues+[f'row={index}: malformed required fields']
    if any(len(scenario.get(key, [])) != N+1 for key in ('rates','reserve_errors','rate_errors')):
        return issues+['scenario arrays missing or incomplete']
    post, pending, due, carry = INITIAL, None, 0, None
    active = refused = False
    probes = writes = saturation = 0
    previous_hash = '0'*64
    for index, row in enumerate(rows):
        t = row['t']
        check(t == index and 0 <= t <= N, t, 'chronological row')
        if not 0 <= t <= N:
            return issues
        check(row['chain_previous'] == previous_hash, t, 'append-chain predecessor')
        check(row['row_hash'] == chain_hash(previous_hash, row), t, 'unchanged emitted row')
        previous_hash = row['row_hash']
        rate = scenario['rates'][t]
        pre = post if t == 0 else post-rate
        delivered = pending == t
        post = min(C, pre+D) if delivered else pre
        if delivered:
            saturation += max(0, pre+D-C)
            pending = None
        probe = due == t or t == N
        incoming = bool(active and due is not None and t <= due)
        check((row['rate'],row['pre'],row['post'],row['delivered']) ==
              (rate,pre,post,int(delivered)), t, 'loss, signed reserve and delayed dose')
        check(row['probe'] == int(probe), t, 'paid observation calendar')
        check(row['carry_before'] == carry, t, 'incoming H-based carry')
        check(row['conditional_pre'] == int(incoming), t, 'incoming pre-delivery contract')
        action, delay, lower, upper = '', None, None, None
        sampled_safe = 0
        if probe:
            probes += 1
            report = pre+scenario['reserve_errors'][t]
            rate_report = rate+scenario['rate_errors'][t]
            check((row['reserve_report'],row['rate_report']) == (report,rate_report),
                  t, 'sensor provenance')
            fresh = min(C, report-2+D) if delivered else report-2
            upper = min(C, report+2+D) if delivered else report+2
            sampled_safe = int(report-2 >= S)
            if t == N:
                action, delay, lower, due = 'terminal', 0, fresh, None
                active = incoming
            else:
                lower = fresh if carry is None else max(fresh,carry)
                if rate_report-1 > H:
                    # A disproved hard premise invalidates its carried value.
                    action, delay, lower, carry, due = 'refuse', 0, fresh, None, None
                    active, refused = False, True
                elif not S+H <= lower <= C:
                    action, delay, carry, due = 'refuse', 0, None, None
                    active, refused = False, True
                else:
                    limit = min(40,max(0,(lower-S-H)//H))
                    if policy == 'early' and upper+D <= C:
                        action, delay = 'write', 1
                    elif limit:
                        action, delay = 'wait', 1 if policy == 'prudent' else limit
                    else:
                        action, delay = 'write', 1
                    carry = min(C,lower-H+D) if action == 'write' else lower-H*delay
                    due = t+delay
                    active = True
                    if action == 'write':
                        check(pending is None and delay == 1, t, 'one delayed physical command')
                        pending = t+1
                        writes += 1
                    if scenario['name'] != 'outside':
                        check(lower <= post, t, 'certified lower encloses physical post reserve')
                        check(carry >= S+H, t, 'guard funds next repair latency')
        else:
            check(row['reserve_report'] is None and row['rate_report'] is None,
                  t, 'no report without a paid observation')
            active = incoming
        check((row['action'],row['delay'],row['lower'],row['upper'],row['due']) ==
              (action,delay,lower,upper,due), t, 'proved policy arithmetic and next calendar')
        check(row['carry_after'] == carry, t, 'outgoing fixed-H carry')
        check(row['refused'] == int(refused), t, 'latched refusal without automatic restart')
        check(row['conditional_post'] == int(active), t, 'post-delivery contract after decision')
        check(row['sampled_safe'] == sampled_safe, t, 'fresh pre-instant claim')
        check((row['probes'],row['writes'],row['saturation']) == (probes,writes,saturation),
              t, 'complete cumulative ledger and dose saturation')
    check(pending is None, N, 'no outstanding physical dose')
    return issues


def metrics(rows):
    if not rows:
        return dict(rows=0,probes=0,writes=0,delivered=0,cost=0,unsafe_pre=[],unsafe_post=[],
                    false_sampled=[],false_conditional_pre=[],false_conditional_post=[],
                    refusals=[],commands=[],post_jump_probes=[],min_pre=None,final_pre=None,
                    final_post=None,saturation_loss=None,external_authorizations=0)
    times = lambda pred: [r['t'] for r in rows if pred(r)]
    probes = sum(r['probe'] for r in rows)
    writes = sum(r['action']=='write' for r in rows)
    return dict(rows=len(rows),probes=probes,writes=writes,delivered=sum(r['delivered'] for r in rows),
                cost=probes+10*writes,
                unsafe_pre=times(lambda r:r['t']>0 and r['pre']<S),
                unsafe_post=times(lambda r:r['t']>0 and r['post']<S),
                false_sampled=times(lambda r:r['sampled_safe'] and r['pre']<S),
                false_conditional_pre=times(lambda r:r['conditional_pre'] and r['pre']<S),
                false_conditional_post=times(lambda r:r['conditional_post'] and r['post']<S),
                refusals=times(lambda r:r['action']=='refuse'),
                commands=times(lambda r:r['action']=='write'),
                post_jump_probes=times(lambda r:r['probe'] and r['t']>=661),
                min_pre=min((r['pre'] for r in rows if r['t']>0),default=None),
                final_pre=rows[-1]['pre'],final_post=rows[-1]['post'],
                saturation_loss=rows[-1]['saturation'],external_authorizations=0)


def distribution(values):
    return dict(min=min(values),median=median(values),max=max(values)) if values else None


def render(summary):
    lines = ['# V5 — unedited registered evidence report', '',
        '**Scope:** service under fixed H=150 and the registered sensor/dose laws.',
        'No runtime external authority or optimistic learned law is used. This is a',
        'discrete-model result, not transistor validation or a full proof of arbitrary',
        'Python execution. The Lean kernel/composition and Python evidence checks have',
        'distinct roles. Source and protocol identity are checked by mandatory preflight.', '',
        '## Already explored replication', '',
        'The known v3 scenario was explored before preregistration. Its reproduction',
        'is not a blind prediction. The <2.82% claim is restricted to that scenario',
        'and the declared oracle action family; it is not a random-case guarantee.', '']
    known = summary['cases'].get('known',{})
    lines += [f'Early-refill cost: {known.get("early",{}).get("cost")}; safe-prudent cost: {known.get("prudent",{}).get("cost")}.',
              f'Oracle cost: {known.get("oracle",{}).get("cost")}; relative excess: {known.get("gap_percent")}% (exact fraction {known.get("gap_fraction")}).', '',
              '## New seeded cases', '',
              '| Seed | Early cost | Prudent cost | Oracle | Gap % | Probes | Writes | Min pre | Final post | Saturation | Unsafe pre/post |',
              '|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|']
    for seed in SEEDS:
        entry = summary['cases'].get('seed'+str(seed),{})
        e,p,o = entry.get('early',{}),entry.get('prudent',{}),entry.get('oracle',{})
        lines += [f'| {seed} | {e.get("cost")} | {p.get("cost")} | {o.get("cost")} | {entry.get("gap_percent")} | {e.get("probes")} | {e.get("writes")} | {e.get("min_pre")} | {e.get("final_post")} | {e.get("saturation_loss")} | {len(e.get("unsafe_pre",[]))}/{len(e.get("unsafe_post",[]))} |']
    lines += ['', 'Seeded distributions (min / median / max):', '',
              '```json',json.dumps(summary['seeded_statistics'],indent=2,sort_keys=True),'```','',
              f'Seeded gaps below 2.82%: {summary["seeded_gap_below_2_82"]}/12.',
              f'Seeded early-refill cases without cost improvement over prudent: {summary["seeded_no_improvement"]}/12.',
              'These counts have no pass threshold and imply no population confidence or significance.', '',
              '## Oracle scope and accounting', '',
              'The offline oracle knows all future loss and noise. It minimizes probes+10*writes',
              'within the registered Ready-at-next-probe, one-command action family. It is not',
              'an autonomous controller or a global physical optimum. There is no terminal',
              'inventory value; saturation and final reserves are retained separately below.', '',
              '| Case | Oracle probes | Writes | Saturation | Final post | Forward/backward agree |',
              '|---|---:|---:|---:|---:|---|']
    for name in NAMES[:-1]:
        entry = summary['cases'].get(name,{})
        o = entry.get('oracle',{})
        lines += [f'| {name} | {o.get("probes")} | {o.get("writes")} | {o.get("saturation_loss")} | {o.get("final_post")} | {entry.get("oracle_agrees")} |']
    outside = summary['cases'].get('outside',{}).get('early',{})
    lines += ['', '## Outside-boundary control', '',
              f'Refusal timestamps: {outside.get("refusals",[])}.',
              f'Unsafe pre/post periods: {len(outside.get("unsafe_pre",[]))}/{len(outside.get("unsafe_post",[]))}.',
              f'Unsafe pre range: {outside.get("unsafe_pre",[])[:1]} to {outside.get("unsafe_pre",[])[-1:]}.',
              f'Conditional pre/post claim violations: {outside.get("false_conditional_pre",[])}/{outside.get("false_conditional_post",[])}.',
              f'False fresh sampled claims: {outside.get("false_sampled",[])}.',
              'All exposure remains in the saved trace. No service guarantee is asserted once',
              'the fixed physical premise fails. Refusal at an observed lower-bound violation',
              'does not establish detection of every small or between-probe excursion.', '',
              '## Registered outcomes', '', '| Outcome | Verdict |', '|---|---|']
    lines += [f'| {k} | {"PASS" if v else "FAIL"} |' for k,v in summary['predictions'].items()]
    lines += ['',f'Audit issues: {len(summary["audit_issues"])}.']
    lines += ['- '+issue for issue in summary['audit_issues']]
    lines += ['', 'The report audits existing records. It does not execute another controller',
              'trajectory. Every failed prediction and partial/missing record is retained.', '']
    return '\n'.join(lines)


def evaluate(out, provenance_issues=()):
    out = Path(out)
    issues = list(provenance_issues)
    cases, hashes = {}, {}
    expected_scenarios = {name+'.json' for name in NAMES}
    actual_scenarios = {p.name for p in (out/'scenarios').glob('*.json')}
    if actual_scenarios != expected_scenarios:
        issues.append('missing or unexpected scenario inventory')
    expected_traces = {f'{name}-{policy}.csv.gz' for name in NAMES
                       for policy in (('early',) if name=='outside' else ('early','prudent'))}
    if {p.name for p in (out/'traces').glob('*.csv.gz')} != expected_traces:
        issues.append('missing or unexpected policy trace inventory')
    try:
        oracles = json.loads((out/'oracle.json').read_text())
    except (OSError,ValueError) as exc:
        issues.append('oracle evidence unavailable: '+str(exc))
        oracles = {}
    if set(oracles) != set(NAMES[:-1]):
        issues.append('missing or unexpected oracle inventory')
    try:
        journal = [json.loads(line) for line in (out/'oracle-events.jsonl').read_text().splitlines()]
        expected = [dict(name=name,**oracles[name]) for name in NAMES[:-1] if name in oracles]
        if journal != expected:
            issues.append('oracle journal differs from final oracle evidence')
    except (OSError,ValueError,TypeError) as exc:
        issues.append('oracle journal unavailable: '+str(exc))
    oracle_ok = True
    for name in NAMES:
        entry = cases[name] = {}
        try:
            path = out/'scenarios'/(name+'.json')
            scenario = json.loads(path.read_text())
            hashes['scenarios/'+path.name] = hashlib.sha256(path.read_bytes()).hexdigest()
            si = scenario_issues(scenario,name)
            issues += si
        except (OSError,ValueError,TypeError) as exc:
            issues.append(name+': scenario unavailable: '+str(exc))
            scenario,si = {}, ['invalid scenario']
        for policy in (('early',) if name=='outside' else ('early','prudent')):
            path = out/'traces'/f'{name}-{policy}.csv.gz'
            try:
                rows = load_rows(path)
                ai = audit_trace(scenario,policy,rows) if not si else ['invalid scenario prevents trace audit']
                issues += [name+':'+policy+': '+message for message in ai]
                entry[policy] = metrics(rows)
                hashes['traces/'+path.name] = hashlib.sha256(path.read_bytes()).hexdigest()
            except (OSError,EOFError,ValueError,TypeError,KeyError) as exc:
                issues.append(name+':'+policy+': trace unavailable: '+str(exc))
                entry[policy] = metrics([])
        if name != 'outside':
            try:
                record = oracles[name]
                backward = record['backward']
                cost = backward['cost']
                if (type(cost) is not int or cost <= 0 or cost != backward['probes']+10*backward['writes']
                        or backward['min_pre'] < S or backward['final_post'] < S
                        or backward['saturation_loss'] < 0):
                    raise ValueError('malformed oracle cost/physical accounting')
                agree = record['forward_cost'] == cost
                entry.update(oracle=backward,oracle_agrees=agree)
                for policy in ('early','prudent'):
                    if cost > entry[policy]['cost']:
                        issues.append(name+': oracle exceeds '+policy+' cost')
                        oracle_ok = False
                if not agree:
                    issues.append(name+': forward/backward oracle disagreement')
                    oracle_ok = False
                gap = Fraction(entry['early']['cost']-cost,cost)
                entry.update(gap_fraction=str(gap),gap_percent=round(float(100*gap),6))
            except (ValueError,TypeError,KeyError) as exc:
                issues.append(name+': invalid oracle evidence: '+str(exc))
                oracle_ok = False
    known = cases['known']
    early,prudent,oracle = known['early'],known['prudent'],known.get('oracle',{})
    seeded = [cases['seed'+str(seed)] for seed in SEEDS]
    complete_seeded = all('oracle' in e and 'gap_fraction' in e for e in seeded)
    fields = ('cost','probes','writes','min_pre','final_post','saturation_loss')
    statistics = {}
    for field in fields:
        values = [e['early'][field] for e in seeded if e['early'][field] is not None]
        statistics[field] = distribution(values) if len(values)==len(SEEDS) else None
    statistics['gap_percent'] = distribution([e['gap_percent'] for e in seeded]) if complete_seeded else None
    below = sum(Fraction(e['gap_fraction']) < Fraction(282,10000) for e in seeded) if complete_seeded else None
    no_improvement = sum(e['early']['cost'] >= e['prudent']['cost'] for e in seeded)
    outside = cases['outside']['early']
    refusal = outside['refusals']
    safe = lambda m: m['rows'] == N+1 and bool(m['probes']) and not (m['unsafe_pre'] or m['unsafe_post'] or m['refusals']
                                              or m['false_sampled'] or m['false_conditional_pre'] or m['false_conditional_post'])
    predictions = {
        'S1': safe(early) and safe(prudent) and
              (early['probes'],early['writes'],early['delivered'],early['cost'],early['final_post'],prudent['cost'])
              == (1171,450,450,5671,440,5821),
        'S2': early['cost'] == 5671 and oracle.get('cost') == 5516 and known.get('oracle_agrees',False)
              and Fraction(early['cost']-5516,5516) < Fraction(282,10000),
        'S3': all(safe(e[p]) for e in seeded for p in ('early','prudent')),
        'S4': not issues and oracle_ok,
        'S5': len(refusal)==1 and bool(outside['post_jump_probes'])
              and refusal[0]==outside['post_jump_probes'][0] and 661<=refusal[0]<=663
              and all(t<refusal[0] for t in outside['commands']),
        'S6': complete_seeded and all(v is not None for v in statistics.values()),
    }
    summary = dict(status='single registered v5 batch; known case is an explored replication',
                   cases=cases,predictions=predictions,audit_issues=issues,
                   seeded_statistics=statistics,seeded_gap_below_2_82=below,
                   seeded_no_improvement=no_improvement,evidence_sha256=hashes)
    with (out/'summary.json').open('x') as stream:
        json.dump(summary,stream,indent=2)
        stream.write('\n')
    with (out/'REPORT.md').open('x') as stream:
        stream.write(render(summary))
    return summary
