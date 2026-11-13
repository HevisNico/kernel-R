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
                final_reserve=rows[-1]['post'])


def audit(name, rows):
    issues = []
    def check(condition, t, message):
        if not condition:
            issues.append(f'{name} t={t}: {message}')
    check(len(rows) == N+1, -1, 'trace length')
    last_post, last_command, due, alarm, anchor = 440, 0, 0, 0, None
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
            lower = min(660, lower_before+220) if r['delivery'] else lower_before
            check(r['lower'] == lower and lower <= r['post'], t, 'sound propagated lower')
            if lower >= 100:
                alarm = 0
            if name == 'contract':
                center = r['rate_report']
                if anchor is None:
                    anchor = center
                reopen = abs(center-anchor) >= 7  # two radius-1 intervals, gap >=5
                if reopen:
                    anchor = center
                check(r['anchor'] == anchor and r['reopened'] == int(reopen), t, 'interval memory')
                if lower < 122 or lower > 660:
                    kind, delay = 'refuse', 0
                else:
                    spacing = min(40, (lower-122)//22)
                    kind, delay = ('wait', spacing) if spacing > 0 else ('write', 1)
            else:
                kind = 'write' if lower < 144 else 'wait'
                delay = 1 if kind == 'write' or name == 'prudent' or lower_before < 100 else 40
                check(r['reopened'] == 0 and r['anchor'] is None, t, 'baseline has no contract anchor')
            check((r['action'], r['delay']) == (kind, delay), t, 'registered decision rule')
            check(r['refused'] == int(kind == 'refuse'), t, 'refusal accounting')
            command = int(kind == 'write' and t < N)
            check(r['command'] == command, t, 'charged command / terminal stop')
            due = None if t == N or kind == 'refuse' else t+delay
        else:
            check(all(r[k] is None for k in ('reserve_report', 'rate_report', 'lower', 'delay', 'anchor')),
                  t, 'no uncharged measurement or decision')
            check(not r['action'] and not r['command'] and not r['reopened'] and not r['refused'],
                  t, 'no unobserved controller action')
            check(r['alarm_detected'] == alarm, t, 'unobserved alarm retained')
        check(r['alarm_after'] == alarm and r['due'] == due, t, 'post-detection state / schedule')
        last_post, last_command = r['post'], r['command']
    if name == 'contract':
        for r in rows:
            t = r['t']
            if not r['probe'] or t == N or r['action'] == 'refuse':
                continue
            lower = r['lower']
            check(122 <= lower <= 660, t, 'ready guard')
            if r['action'] == 'wait':
                delay = r['delay']
                check(0 < delay <= 40 and 22*delay+122 <= lower, t, 'wait certificate')
                for q in rows[t+1:min(N, t+delay)+1]:
                    check(q['rate'] <= 22 and q['pre'] >= lower-22*(q['t']-t), q['t'], 'wait lower law')
                    check(q['pre'] >= 100 and q['post'] >= 100, q['t'], 'wait substep service')
            else:
                q = rows[t+1]
                check(q['pre'] >= lower-22 and q['pre'] >= 100, t+1, 'repair-time buffer')
                check(q['post'] >= min(660, lower-22+220), t+1, 'delayed dose lower law')
    return issues


def render(summary):
    lines = ['# Discrete refresh v1 — unedited generated report', '',
             'One registered invocation, three fixed controller trajectories. No parameter sweep.',
             'Protocol: `ca8645502588339c43e836b7319c6348dbebcfd2`.',
             'Dependency: frozen #111 at `ba978af1edaf51572aa0af9d1bfc83e309438d3d`.', '',
             '| Controller | Probes | Writes | Probe cost | Write cost | Total | Pre unsafe | Post unsafe | Undetected | Longest undetected | Reopenings | Refusals | Final reserve |',
             '|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|']
    keys = ('probes', 'writes', 'probe_cost', 'write_cost', 'total_cost', 'pre_unsafe',
            'post_unsafe', 'undetected', 'longest_undetected', 'reopenings', 'refusals', 'final_reserve')
    for name, m in summary['controllers'].items():
        lines.append('| '+name+' | '+' | '.join(str(m[k]) for k in keys)+' |')
    lines += ['', '## Registered predictions', '', '| ID | Verdict |', '|---|---|']
    for key, value in summary['predictions'].items():
        lines.append(f'| {key} | {"PASS" if value else "FAIL"} |')
    c, p = summary['controllers']['contract'], summary['controllers']['prudent']
    lines += ['', f'Contract/prudent cost ratio: {c["total_cost"]}/{p["total_cost"]} '
              f'= {c["total_cost"]/p["total_cost"]:.6f}.',
              f'Contract reopening timestamps: {c["reopening_times"]}; first post-jump probe: '
              f'{c["first_post_jump_probe"]}; reopening delay: {c["reopening_delay"]} periods.',
              f'Sampled true-rate variation: {c["sampled_rate_variation"]}; '
              f'5 × reopenings = {5*c["reopenings"]}.', '', '## Integrity and deviations', '',
              f'Trace audit issues: {len(summary["audit_issues"])}.']
    lines += [f'- {issue}' for issue in summary['audit_issues']]
    lines += ['', 'The audit checks chronology, all sensor reports, every paid probe and command,',
              'baseline rules, interval memory, and each contract wait/write lower-bound law.',
              'Contract actions were returned by the Lean process executing #111 definitions;',
              'the independent numeric trace audit also checks their prescribed decision rule.',
              'No protocol parameter or prediction was revised after publication. A failed',
              'prediction is retained above; no run was repeated to improve its outcome.', '',
              '## Limits', '',
              'This is one deterministic model comparison, not statistical or transistor evidence.',
              'The 22-period calibration does not prove a physical R adapter. The supervisor',
              'uses a known hard ceiling covering the jump; its rate sensor only drives reopening',
              'memory in this trial. It does not learn a tighter safe future bound.',
              'The wrapper is not a newly proved end-to-end OfferFactory instance. Prices are',
              'declared units, measurement latency is absent, and the two-channel sensor is assumed.',
              'Unsafe exposure counts discrete pre-write samples, not a continuous-time integral.', '',
              'Raw CSVs, metadata, stdout/stderr and SHA-256 hashes accompany this report.', '']
    return '\n'.join(lines)


def evaluate(out):
    rows = {name: load_rows(out/f'{name}.csv') for name in ('naive', 'prudent', 'contract')}
    counts = {name: metrics(trace) for name, trace in rows.items()}
    issues = [issue for name, trace in rows.items() for issue in audit(name, trace)]
    n, p, c = (counts[name] for name in ('naive', 'prudent', 'contract'))
    zero = lambda m: m['pre_unsafe'] == m['post_unsafe'] == m['undetected'] == 0
    predictions = {
        'P1': p['probes'] == 1321 and 88 <= p['writes'] <= 92 and zero(p),
        'P2': c['refusals'] == 0 and zero(c),
        'P3': 150 <= c['probes'] <= 600 and 88 <= c['writes'] <= 92 and 4*c['total_cost'] <= 3*p['total_cost'],
        'P4': c['reopenings'] == 1 and c['reopening_times'][0] == c['first_post_jump_probe']
              and 0 <= c['reopening_delay'] <= 40 and 5*c['reopenings'] <= c['sampled_rate_variation'] == 10,
        'P5': n['undetected'] >= 100 and n['longest_undetected'] >= 10 and 80 <= n['writes'] <= 100,
        'P6': n['total_cost'] < c['total_cost'],
        'P7': not any(issue.startswith('contract ') for issue in issues),
    }
    summary = {'controllers': counts, 'predictions': predictions, 'audit_issues': issues,
               'trace_sha256': {name: hashlib.sha256((out/f'{name}.csv').read_bytes()).hexdigest() for name in rows}}
    # Do not overwrite existing evaluations or revise a generated report.
    with (out/'summary.json').open('x') as f:
        json.dump(summary, f, indent=2); f.write('\n')
    with (out/'REPORT.md').open('x') as f:
        f.write(render(summary))
    return summary
