"""Evaluate recorded CSVs only; never executes a plant or controller trajectory."""
import csv
import hashlib
import json
from pathlib import Path

N, JUMP, FLOOR = 1320, 661, 100


def load_rows(path):
    with path.open(newline='') as f:
        return [{k: (v if k == 'action' else int(v) if v else None)
                 for k, v in row.items()} for row in csv.DictReader(f)]


def metrics(rows):
    unsafe = hidden = post_unsafe = longest = streak = 0
    for r in rows:
        if r['t'] == 0:
            continue
        bad = r['pre'] < FLOOR
        undetected = bad and not r['alarm_detected']
        unsafe += bad
        post_unsafe += r['post'] < FLOOR
        hidden += undetected
        streak = streak + 1 if undetected else 0
        longest = max(longest, streak)
    probes = sum(r['probe'] for r in rows)
    writes = sum(r['command'] for r in rows)
    reopens = [r['t'] for r in rows if r['reopened']]
    first_after = next((r['t'] for r in rows if r['probe'] and r['t'] >= JUMP), None)
    previous, variation = None, 0
    for r in rows:
        if r['probe']:
            if previous is not None:
                variation += abs(r['rate'] - previous)
            previous = r['rate']
    return dict(probes=probes, writes=writes, delivered=sum(r['delivery'] for r in rows),
                probe_cost=probes, write_cost=10*writes, total_cost=probes+10*writes,
                pre_unsafe=unsafe, post_unsafe=post_unsafe, undetected=hidden,
                longest_undetected=longest, reopenings=len(reopens), reopening_times=reopens,
                first_post_jump_probe=first_after,
                reopening_delay=(reopens[0]-JUMP if reopens else None),
                sampled_rate_variation=variation, refusals=sum(r['refused'] for r in rows),
                final_reserve=rows[-1]['post'], ambiguous=sum(r['ambiguous'] for r in rows),
                invalidations=sum(r['invalidated'] for r in rows),
                before_ceilings=sorted({r['bound'] for r in rows if r['probe'] and r['t'] < JUMP}),
                after_ceilings=sorted({r['bound'] for r in rows if r['probe'] and r['t'] >= JUMP}))


def audit(name, rows):
    issues = []
    def check(condition, t, message):
        if not condition:
            issues.append(f'{name} t={t}: {message}')
    check(len(rows) == N+1, -1, 'trace length')
    last_post, last_command, due, alarm, anchor = 440, 0, 0, 0, None
    previous_decision = None
    for expected_t, r in enumerate(rows):
        t = r['t']
        check(t == expected_t, t, 'timestamp order')
        check(r['rate'] == (10 if t < JUMP else 20), t, 'registered leakage')
        expected_pre = 440 if t == 0 else last_post - r['rate']
        check(r['pre'] == expected_pre, t, 'leak before measurement/delivery')
        check(r['delivery'] == last_command, t, 'exact one-period write latency')
        expected_post = min(660, expected_pre+220) if r['delivery'] else expected_pre
        check(r['post'] == expected_post, t, 'dose/conservation/saturation')
        check(r['probe'] == int(due == t), t, 'scheduled paid observation')
        check(r['alarm_before'] == alarm, t, 'alarm memory')
        if r['probe']:
            check(r['reserve_error'] == (7*t+1)%5-2, t, 'reserve noise schedule')
            check(r['rate_error'] == (5*t+2)%3-1, t, 'rate noise schedule')
            check(abs(r['reserve_error']) <= 2 and abs(r['rate_error']) <= 1, t, 'sensor bounds')
            check(r['reserve_report'] == r['pre']+r['reserve_error'], t, 'reserve report')
            check(r['rate_report'] == r['rate']+r['rate_error'], t, 'rate report')
            lower_before = r['reserve_report']-2
            alarm = int(bool(alarm or lower_before < 100))
            check(r['alarm_detected'] == alarm, t, 'detection precedes dose')
            fresh = min(660, lower_before+220) if r['delivery'] else lower_before
            if fresh >= 100:
                alarm = 0
            bound = r['rate_report'] + 11
            check(r['bound'] == bound, t, 'measurement-derived ceiling')
            lower = fresh
            if name == 'adaptive':
                check(r['lease_end'] == t+41, t, 'lease horizon')
                old_bound, carried, invalidated, ambiguous = None, None, False, False
                if previous_decision is not None:
                    old = previous_decision
                    old_bound = old['bound']
                    check(t == old['t']+old['delay'] and t <= old['lease_end'], t, 'covered handoff')
                    carried = (old['lower']-old_bound*old['delay'] if old['action']=='wait'
                               else min(660, old['lower']+220-old_bound))
                    invalidated = max(0, r['rate_report']-1) > old_bound
                    ambiguous = not invalidated and r['rate_report']+1 > old_bound
                    check(bound <= old_bound+12, t, 'next-ceiling growth')
                    if not invalidated:
                        check(carried <= r['post'], t, 'carried certificate')
                        lower = max(fresh, carried)
                check(r['old_bound'] == old_bound and r['carried'] == carried, t, 'certificate provenance')
                check(r['invalidated'] == int(invalidated) and r['ambiguous'] == int(ambiguous),
                      t, 'violation versus ambiguous exceedance')
            check(r['lower'] == lower and lower <= r['post'], t, 'sound effective lower')
            if name == 'adaptive':
                center = r['rate_report']
                if anchor is None:
                    anchor = center
                reopen = abs(center-anchor) >= 7  # two radius-1 intervals, gap >=5
                if reopen:
                    anchor = center
                check(r['anchor'] == anchor and r['reopened'] == int(reopen), t, 'interval memory')
                if r['invalidated'] or bound >= 220 or 100+2*bound > 660 or lower < 100+bound or lower > 660:
                    kind, delay = 'refuse', 0
                else:
                    spacing = min(40, (lower-100-bound-12)//bound) if lower >= 100+bound+12 else 0
                    kind, delay = ('wait', spacing) if spacing > 0 else ('write', 1)
            else:
                kind = 'write' if lower < 100+2*bound else 'wait'
                delay = 1 if kind == 'write' or name == 'prudent' or lower_before < 100 else 40
                check(r['reopened'] == 0 and r['anchor'] is None, t, 'baseline has no contract anchor')
            check((r['action'], r['delay']) == (kind, delay), t, 'registered decision rule')
            check(r['refused'] == int(kind == 'refuse'), t, 'refusal accounting')
            command = int(kind == 'write' and t < N)
            check(r['command'] == command, t, 'charged command / terminal stop')
            due = None if t == N or kind == 'refuse' else t+delay
            if name == 'adaptive':
                previous_decision = r
        else:
            check(all(r[k] is None for k in ('reserve_report', 'rate_report', 'lower', 'delay', 'anchor')),
                  t, 'no uncharged measurement or decision')
            check(not r['action'] and not r['command'] and not r['reopened'] and not r['refused'],
                  t, 'no unobserved controller action')
            check(r['alarm_detected'] == alarm, t, 'unobserved alarm retained')
        check(r['alarm_after'] == alarm and r['due'] == due, t, 'post-detection state / schedule')
        last_post, last_command = r['post'], r['command']
    if name == 'adaptive':
        for r in rows:
            t = r['t']
            if not r['probe'] or t == N or r['action'] == 'refuse':
                continue
            lower = r['lower']
            bound = r['bound']
            check(100+bound <= lower <= 660, t, 'ready guard')
            if r['action'] == 'wait':
                delay = r['delay']
                check(0 < delay <= 40 and bound*delay+100+bound+12 <= lower, t, 'wait certificate')
                for q in rows[t+1:min(N, t+delay)+1]:
                    check(q['rate'] <= bound and q['pre'] >= lower-bound*(q['t']-t), q['t'], 'wait lower law')
                    check(q['pre'] >= 100 and q['post'] >= 100, q['t'], 'wait substep service')
            else:
                q = rows[t+1]
                check(q['pre'] >= lower-bound and q['pre'] >= 100, t+1, 'repair-time buffer')
                check(q['post'] >= min(660, lower-bound+220), t+1, 'delayed dose lower law')
    return issues


def render(summary):
    lines = ['# Adaptive refresh v2 — unedited generated report', '',
             'One preregistered invocation; three fixed controller trajectories; no pilot or sweep.',
             'Protocol: `c58ba5af913a5d129734aaa6d66a16fce99e27aa`.',
             'V1 comparison uses its published result, not a rerun.', '',
             '| Controller | Probes | Writes | Probe cost | Write cost | Total | Pre unsafe | Post unsafe | Undetected | Longest | Anchor reopenings | Ambiguous | Invalidations | Refusals | Final reserve |',
             '|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|']
    keys = ('probes','writes','probe_cost','write_cost','total_cost','pre_unsafe','post_unsafe',
            'undetected','longest_undetected','reopenings','ambiguous','invalidations','refusals','final_reserve')
    for name,m in summary['controllers'].items():
        lines.append('| '+name+' | '+' | '.join(str(m[k]) for k in keys)+' |')
    lines += ['', '## Registered predictions', '', '| ID | Verdict |', '|---|---|']
    for key,value in summary['predictions'].items():
        lines.append(f'| {key} | {"PASS" if value else "FAIL"} |')
    c,p = summary['controllers']['adaptive'],summary['controllers']['prudent']
    lines += ['', f'Adaptive/prudent cost: {c["total_cost"]}/{p["total_cost"]} = {c["total_cost"]/p["total_cost"]:.6f}.',
              f'Adaptive/v1 known-ceiling cost: {c["total_cost"]}/1247 = {c["total_cost"]/1247:.6f}.',
              f'Observed adaptive ceilings before jump: {c["before_ceilings"]}; after jump: {c["after_ceilings"]}.',
              f'Anchor reopenings at {c["reopening_times"]}; delay {c["reopening_delay"]} periods.',
              f'Sampled true-rate variation {c["sampled_rate_variation"]}; 5 × anchor reopenings = {5*c["reopenings"]}.',
              '', '## Integrity and deviations', '', f'Trace audit issues: {len(summary["audit_issues"])}.']
    lines += ['- '+issue for issue in summary['audit_issues']]
    lines += ['', 'No protocol parameter or prediction was revised after publication. All verdicts are retained.',
              'Each adaptive decision came from the Lean bridge. The separate trace audit checks',
              'chronology, observations, prices, variable thresholds, carry propagation, lease coverage,',
              'the distinction between ambiguous and proven violations, and local wait/write laws.',
              'Lean proves the local ceiling, handoff and repair lemmas; the complete Python wrapper',
              'is not asserted to have a new end-to-end formal proof.', '', '## Limits', '',
              'No absolute leakage ceiling was provided. The variation law B=10 over H=41 was provided,',
              'not learned. This law covers the hidden jump and is indispensable to future safety.',
              'A demonstrated violation would invalidate the old guarantee; a later repair cannot',
              'make the past safe. Ambiguous sensor exceedances are counted separately from anchor changes.',
              'This single deterministic model run is neither statistical confidence nor circuit validation.',
              'The two-channel sensor and dose are assumed; prices are model units and sensing latency is absent.',
              'The nominal 22-period R calibration still needs a waveform-based state/sensor/dose adapter.',
              'The v1 comparison changes information and repair policies, not just observation expense.',
              '', 'Raw CSVs, metadata, stdout/stderr, exit status and hashes accompany this report.', '']
    return '\n'.join(lines)


def evaluate(out):
    rows = {name: load_rows(out/f'{name}.csv') for name in ('naive','prudent','adaptive')}
    counts = {name: metrics(trace) for name,trace in rows.items()}
    issues = [issue for name,trace in rows.items() for issue in audit(name,trace)]
    # Independently check the physical variation hypothesis on every complete
    # available horizon, not just observed endpoints.
    reference = rows['adaptive']
    for i,r in enumerate(reference):
        if any(q['rate'] > r['rate']+10 for q in reference[i:min(N,i+41)+1]):
            issues.append(f'adaptive t={i}: variation hypothesis violated')
    n,p,c = (counts[name] for name in ('naive','prudent','adaptive'))
    zero = lambda m: m['pre_unsafe']==m['post_unsafe']==m['undetected']==0
    audit_ok = not any(i.startswith('adaptive ') for i in issues)
    predictions = {
        'A1': p['probes']==1321 and 88<=p['writes']<=94 and zero(p),
        'A2': c['refusals']==c['invalidations']==0 and zero(c),
        'A3': 200<=c['probes']<=800 and 88<=c['writes']<=94 and 5*c['total_cost']<=4*p['total_cost'],
        'A4': 1247<=c['total_cost'] and 2*c['total_cost']<=3*1247,
        'A5': c['reopenings']==1 and c['reopening_times'][0]==c['first_post_jump_probe']
              and 0<=c['reopening_delay']<=40 and 5*c['reopenings']<=c['sampled_rate_variation']==10
              and 0<=c['ambiguous']<=1,
        'A6': all(20<=u<=22 for u in c['before_ceilings']) and all(30<=u<=32 for u in c['after_ceilings'])
              and all(q['rate']<=r['bound'] for r in reference if r['probe'] and r['action']!='refuse'
                      for q in reference[r['t']+1:min(N,r['t']+r['delay'])+1]),
        'A7': n['undetected']>=100 and n['longest_undetected']>=10 and n['total_cost']<c['total_cost'],
        'A8': audit_ok,
    }
    summary = {'controllers':counts,'predictions':predictions,'audit_issues':issues,
               'trace_sha256':{name:hashlib.sha256((out/f'{name}.csv').read_bytes()).hexdigest() for name in rows}}
    with (out/'summary.json').open('x') as f:
        json.dump(summary,f,indent=2); f.write('\n')
    with (out/'REPORT.md').open('x') as f:
        f.write(render(summary))
    return summary
