"""Independent arithmetic audit of saved v4 rows; never runs a trajectory.

The audit checks the recorded decisions and evidence, not another instance of
the controller. All quantities below are computed from the immutable trace.
"""
import csv
import hashlib
import json
from pathlib import Path
import subprocess

from schema import (FIELDS, TEXT, PROTOCOL, DEPENDENCY, N, JUMP, AUTHORIZE,
                    INITIAL, SERVICE, CAPACITY, DOSE, BOUND, EXPIRY,
                    REPAIR_BUDGET, PHASE_BUDGET, PHASE_SIZE, chain_hash)

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parent.parent
JUSTIFICATION = 'RecoveryV4.root_ceiling_from_registered_plant'


def load_rows(path):
    with path.open(newline='') as stream:
        reader = csv.DictReader(stream)
        if tuple(reader.fieldnames or ()) != FIELDS:
            raise ValueError('Noncanonical v4 CSV fields')
        rows = []
        for row in reader:
            if None in row or any(value is None for value in row.values()):
                raise ValueError('Truncated or extra CSV fields')
            rows.append({k: v if k in TEXT else int(v) if v else None for k, v in row.items()})
        return rows


def root_event():
    return dict(kind='root', time=AUTHORIZE, issued=AUTHORIZE, expires=EXPIRY,
                bound=BOUND, service=SERVICE, dose=DOSE, capacity=CAPACITY,
                latency=1, justification=JUSTIFICATION)


def token_event(t, generation):
    return dict(kind='token', time=t, generation=generation, issued=t,
                expires=EXPIRY, bound=BOUND, decisions=PHASE_SIZE)


def active_action(lower, now, permit, remaining, rate_report, generation):
    if (permit is None or permit['generation'] != generation or permit['issued'] > now
            or remaining <= 0 or remaining > permit['decisions']
            or not 0 < permit['decisions'] <= PHASE_SIZE
            or max(0, rate_report - 1) > permit['bound']
            or not SERVICE + permit['bound'] <= lower <= CAPACITY
            or permit['bound'] >= DOSE or SERVICE + 2*permit['bound'] > CAPACITY):
        return 'refuse', 0
    bound = permit['bound']
    delay = min(40, (lower - SERVICE - bound)//bound) if bound else 40
    kind, delay = ('wait', delay) if delay > 0 else ('write', 1)
    return (kind, delay) if now + delay <= permit['expires'] else ('refuse', 0)


def audit(rows):
    issues = []
    def check(ok, t, message):
        if not ok:
            issues.append(f't={t}: {message}')
    check(len(rows) == N + 1, -1, 'complete registered horizon')
    for index, row in enumerate(rows):
        if set(row) != set(FIELDS) or not isinstance(row.get('t'), int):
            issues.append(f'row={index}: malformed schema or time')
            return issues
    previous_hash = '0'*64
    post, previous_command, due, alarm = INITIAL, 0, 0, 0
    anchor, last_legacy = None, None
    legacy_active, legacy_u, legacy_expiry = False, None, None
    mode, generation, fuel, phases, remaining, permit = 'legacy', None, None, None, None, None
    guaranteed_after, origin = False, ''
    probes = writes = roots = tokens = 0
    for index, r in enumerate(rows):
        t = r['t']
        check(t == index, t, 'chronological row')
        check(r['chain_previous'] == previous_hash, t, 'append-chain predecessor')
        check(r['row_hash'] == chain_hash(previous_hash, r), t, 'unchanged emitted row')
        previous_hash = r['row_hash']
        rate = 10 if t < JUMP else 140
        pre = INITIAL if t == 0 else post - rate
        delivery = previous_command
        post = min(CAPACITY, pre + DOSE) if delivery else pre
        probing = due == t or t == N
        incoming_guarantee = bool(guaranteed_after and due is not None and t <= due and t <= EXPIRY)
        incoming_legacy = bool(legacy_active and legacy_expiry is not None and t <= legacy_expiry)
        check((r['rate'], r['pre'], r['post'], r['delivery']) == (rate, pre, post, delivery),
              t, 'registered loss, signed reserve and delayed saturated delivery')
        check(r['probe'] == int(probing), t, 'paid calendar and terminal readout')
        check(r['terminal'] == int(t == N), t, 'terminal boundary')
        check(r['alarm_before'] == alarm, t, 'alarm memory')
        check(r['legacy_contract_pre'] == int(incoming_legacy), t, 'incoming old lease status')
        check(r['guaranteed_pre'] == int(incoming_guarantee), t, 'new guarantee uses incoming pre boundary')
        root = int(t == AUTHORIZE)
        roots += root
        check(r['root_issued'] == root, t, 'fixed external root date')
        command, token, invalidated = 0, 0, 0
        kind, delay, lower = '', None, None
        legacy = dict(action='', bound=None, carried=None, old_bound=None, invalidated=0,
                      ambiguous=0, anchor=None, reopened=0, lease_end=None, delay=None, lower=None)
        if probing:
            probes += 1
            ex, er = (7*t + 1) % 5 - 2, (5*t + 2) % 3 - 1
            check((r['reserve_error'], r['rate_error']) == (ex, er), t, 'registered sensor errors')
            check((r['reserve_report'], r['rate_report']) == (pre + ex, rate + er),
                  t, 'honest report provenance')
            report = r['reserve_report'] if isinstance(r['reserve_report'], int) else pre + ex
            rate_report = r['rate_report'] if isinstance(r['rate_report'], int) else rate + er
            raw = report - 2
            fresh = min(CAPACITY, raw + DOSE) if delivery else raw
            check(r['sampled_safe_pre'] == int(raw >= SERVICE), t, 'fresh pre-instant declaration')
            alarm = int(bool(alarm or raw < SERVICE))
            check(r['alarm_detected'] == alarm, t, 'alarm detection before delivery')
            if fresh >= SERVICE:
                alarm = 0
            if t == N:
                kind, delay, lower = 'terminal', 0, fresh
                due = None
                guaranteed_after = incoming_guarantee
            else:
                if mode == 'legacy':
                    bound, carried, old_bound = rate_report + 11, None, None
                    invalid, ambiguous = False, False
                    if last_legacy is not None:
                        old_bound = last_legacy['bound']
                        check(t == last_legacy['t'] + last_legacy['delay'] and
                              t <= last_legacy['lease_end'], t, 'legacy action endpoint and expiry')
                        carried = (last_legacy['lower'] - old_bound*last_legacy['delay']
                                   if last_legacy['action'] == 'wait'
                                   else min(CAPACITY, last_legacy['lower'] + DOSE - old_bound))
                        invalid = max(0, rate_report - 1) > old_bound
                        ambiguous = not invalid and rate_report + 1 > old_bound
                    legacy_lower = fresh if invalid or carried is None else max(fresh, carried)
                    if anchor is None:
                        anchor = rate_report
                    reopened = abs(rate_report - anchor) >= 7
                    if reopened:
                        anchor = rate_report
                    if invalid or not SERVICE + bound <= legacy_lower <= CAPACITY or bound >= DOSE or SERVICE + 2*bound > CAPACITY:
                        legacy_kind, legacy_delay = 'refuse', 0
                    else:
                        d = min(40, (legacy_lower - SERVICE - bound - 12)//bound)
                        legacy_kind, legacy_delay = ('wait', d) if d > 0 else ('write', 1)
                    legacy = dict(action=legacy_kind, bound=bound, carried=carried, old_bound=old_bound,
                                  invalidated=int(invalid), ambiguous=int(ambiguous), anchor=anchor,
                                  reopened=int(reopened), lease_end=t+41, delay=legacy_delay, lower=legacy_lower)
                    last_legacy = dict(t=t, **legacy)
                    if legacy_kind == 'refuse':
                        legacy_active, legacy_u, legacy_expiry = False, None, None
                        mode = 'recovery-unguaranteed'
                        generation, fuel, phases, remaining, permit = 1, REPAIR_BUDGET, PHASE_BUDGET, 0, None
                    else:
                        legacy_active, legacy_u, legacy_expiry = True, bound, t+41
                        kind, delay, lower = legacy_kind, legacy_delay, legacy_lower
                        command = int(kind == 'write')
                        due = t + delay
                if mode != 'legacy':
                    lower = fresh
                    request_generation = (generation if mode == 'recovery-unguaranteed'
                                          else generation + 1 if remaining == 0 else None)
                    supplied = None
                    if t >= AUTHORIZE and request_generation is not None and tokens < PHASE_BUDGET:
                        token, supplied = 1, token_event(t, request_generation)
                        tokens += 1
                    if mode == 'authorized-conditional':
                        kind, delay = active_action(fresh, t, permit, remaining, rate_report, generation)
                        if kind == 'refuse':
                            invalidated = int(max(0, rate_report - 1) > permit['bound'])
                            generation += 1
                            permit, remaining, mode = None, 0, 'recovery-unguaranteed'
                    if mode == 'recovery-unguaranteed':
                        accepted = (supplied is not None and phases > 0 and
                                    supplied['generation'] == generation and supplied['issued'] == t
                                    and SERVICE + BOUND <= fresh <= CAPACITY
                                    and t + PHASE_SIZE*40 <= EXPIRY)
                        if accepted:
                            permit, remaining, mode = supplied, PHASE_SIZE, 'authorized-conditional'
                            phases -= 1
                            kind, delay = active_action(fresh, t, permit, remaining, rate_report, generation)
                            if not origin:
                                origin = f'post:{t}'
                        else:
                            kind, delay = ('repair', 1) if fuel > 0 else ('exhausted', 0)
                    if kind == 'repair':
                        fuel -= 1
                    elif kind in ('write', 'wait'):
                        remaining -= 1
                    else:
                        mode = kind + '-unguaranteed'
                        permit = None
                    command = int(kind in ('repair', 'write'))
                    due = t + delay if delay > 0 else None
                    guaranteed_after = bool(mode == 'authorized-conditional' and due is not None and due <= EXPIRY)
        else:
            check(r['alarm_detected'] == alarm, t, 'no unobserved alarm detection')
            check(r['sampled_safe_pre'] == 0, t, 'no unobserved safety declaration')
            check(all(r[k] is None for k in ('reserve_error', 'rate_error', 'reserve_report',
                                             'rate_report', 'lower', 'delay')), t, 'no free report or decision')
            guaranteed_after = incoming_guarantee
        writes += command
        check((r['action'], r['delay'], r['lower'], r['command'], r['due']) ==
              (kind, delay, lower, command, due), t, 'recorded decision, command and next observation')
        check(r['mode'] == mode, t, 'explicit controller mode')
        check((r['generation'], r['fuel'], r['phases_left'], r['remaining']) ==
              (generation, fuel, phases, remaining), t, 'no credit refill; exact generation/phase accounting')
        expected_permit = ((None,)*5 if permit is None else
                           (permit['generation'], permit['issued'], permit['expires'], permit['bound'], permit['decisions']))
        check(tuple(r[k] for k in ('permit_generation', 'permit_issue', 'permit_expiry', 'permit_bound', 'permit_decisions'))
              == expected_permit, t, 'external permit identity, time and scope')
        check((r['token_issued'], r['new_invalidated']) == (token, invalidated), t, 'token issuance versus demonstrated rupture')
        for key, value in legacy.items():
            check(r['legacy_' + key] == value, t, 'legacy decision provenance: ' + key)
        after_legacy = bool(legacy_active and legacy_expiry is not None and t <= legacy_expiry)
        check((r['legacy_contract_after'], r['legacy_ceiling'], r['legacy_expires']) ==
              (int(after_legacy), legacy_u, legacy_expiry), t, 'old lease revoked before post status')
        check((r['guaranteed_post'], r['guarantee_origin']) == (int(guaranteed_after), origin),
              t, 'post-delivery authorization boundary')
        check(r['alarm_after'] == alarm, t, 'alarm clearance uses fresh post-delivery evidence')
        check(tuple(r[k] for k in ('cost_probes', 'cost_writes', 'cost_root', 'cost_tokens')) ==
              (probes, 10*writes, roots, tokens), t, 'cumulative complete cost ledger')
        truth = (int(t > 0 and pre < SERVICE), int(t > 0 and post < SERVICE),
                 int(t > 0 and pre < SERVICE and not r['alarm_detected']),
                 int(bool(r['sampled_safe_pre']) and pre < SERVICE),
                 int(bool(r['guaranteed_pre']) and pre < SERVICE),
                 int(bool(r['guaranteed_post']) and post < SERVICE))
        check(tuple(r[k] for k in ('truth_unsafe_pre', 'truth_unsafe_post', 'truth_undetected',
                                  'truth_false_sample', 'truth_false_guarantee_pre', 'truth_false_guarantee_post'))
              == truth, t, 'uncensored phase-correct scorer flags')
        previous_command = command
    check(previous_command == 0, N, 'no outstanding physical dose beyond horizon')
    return issues


def metrics(rows):
    scored = [r for r in rows if r['t'] > 0]
    times = lambda pred: [r['t'] for r in rows if pred(r)]
    refusals = times(lambda r: r['legacy_action'] == 'refuse')
    admitted = times(lambda r: r['guaranteed_post'] and not r['guaranteed_pre'])
    detection = refusals[0] if refusals else None
    returned = admitted[0] if admitted else None
    recovery = times(lambda r: r['action'] == 'repair' and r['command'])
    recovered_deliveries = [r['t'] for i, r in enumerate(rows) if i > 0 and r['delivery'] and rows[i-1]['action'] == 'repair']
    probe_times = times(lambda r: r['probe'])
    tokens = times(lambda r: r['token_issued'])
    roots = times(lambda r: r['root_issued'])
    commands = sum(r['command'] for r in rows)
    boundary_probes = [t for t in probe_times if detection is not None and returned is not None and detection <= t <= returned]
    unsafe_pre = [r['t'] for r in scored if r['pre'] < SERVICE]
    unsafe_post = [r['t'] for r in scored if r['post'] < SERVICE]
    false_sample = times(lambda r: r['sampled_safe_pre'] and r['pre'] < SERVICE)
    false_pre = times(lambda r: r['guaranteed_pre'] and r['pre'] < SERVICE)
    false_post = times(lambda r: r['guaranteed_post'] and r['post'] < SERVICE)
    recovered_safe = times(lambda r: r['t'] >= JUMP and r['sampled_safe_pre'])
    return dict(detection_time=detection, guaranteed_post_origin=returned,
                guaranteed_pre_first=next((r['t'] for r in rows if r['guaranteed_pre']), None),
                first_recovered_sampled_safe=recovered_safe[0] if recovered_safe else None,
                legacy_invalidations=times(lambda r: r['legacy_invalidated']),
                legacy_ambiguities=times(lambda r: r['legacy_ambiguous']),
                new_invalidations=times(lambda r: r['new_invalidated']),
                failed_supervisor_visits=times(lambda r: r['action'] in ('fault', 'exhausted', 'refuse')),
                recovery_commands=recovery, recovery_deliveries=recovered_deliveries,
                recovery_boundary_probes=boundary_probes,
                recovery_boundary_cost=len(boundary_probes) + 10*len(recovery),
                probe_times=probe_times, probes=len(probe_times), commands=commands,
                deliveries=sum(r['delivery'] for r in rows),
                legacy_writes=sum(r['command'] for r in rows if r['mode'] == 'legacy'),
                recovery_writes=len(recovery), authorized_writes=sum(r['command'] for r in rows if r['mode'] == 'authorized-conditional'),
                token_times=tokens, tokens=len(tokens), root_times=roots, roots=len(roots),
                probe_write_cost=len(probe_times) + 10*commands,
                complete_cost=len(probe_times) + 10*commands + len(tokens) + len(roots),
                pre_unsafe_times=unsafe_pre, post_unsafe_times=unsafe_post,
                undetected_times=times(lambda r: r['t'] > 0 and r['pre'] < SERVICE and not r['alarm_detected']),
                false_sample_times=false_sample, false_guaranteed_pre_times=false_pre, false_guaranteed_post_times=false_post,
                true_sample_claims=sum(bool(r['sampled_safe_pre']) and r['pre'] >= SERVICE for r in rows),
                true_guaranteed_pre=sum(bool(r['guaranteed_pre']) and r['pre'] >= SERVICE for r in rows),
                true_guaranteed_post=sum(bool(r['guaranteed_post']) and r['post'] >= SERVICE for r in rows),
                old_incoming_unsafe=times(lambda r: r['t'] > 0 and r['legacy_contract_pre'] and r['pre'] < SERVICE),
                old_after_detection_unsafe=times(lambda r: r['t'] > 0 and r['legacy_contract_after'] and r['pre'] < SERVICE),
                final_pre=rows[-1]['pre'] if rows else None,
                final_post=rows[-1]['post'] if rows else None)


def prefix_check(rows):
    archive = ROOT.parent/'refresh-contract-rupture/run-v3/adaptive.csv'
    with archive.open(newline='') as stream:
        old = [{k: v if k in ('action', 'chain_previous', 'row_hash') else int(v) if v else None
                for k, v in r.items()} for r in csv.DictReader(stream)]
    shared = ('t', 'rate', 'pre', 'post', 'probe', 'reserve_error', 'rate_error', 'reserve_report',
              'rate_report', 'delivery', 'command', 'due', 'alarm_before', 'alarm_detected', 'alarm_after')
    legacy_map = {'legacy_action': 'action', 'legacy_bound': 'bound', 'legacy_carried': 'carried',
                  'legacy_old_bound': 'old_bound', 'legacy_invalidated': 'invalidated',
                  'legacy_ambiguous': 'ambiguous', 'legacy_anchor': 'anchor', 'legacy_reopened': 'reopened',
                  'legacy_lease_end': 'lease_end', 'legacy_delay': 'delay', 'legacy_lower': 'lower'}
    issues = []
    if len(rows) <= 662:
        return ['v4 prefix incomplete']
    for t in range(662):
        for key in shared:
            if rows[t][key] != old[t][key]:
                issues.append(f'v3 shared prefix differs t={t} field={key}')
        if rows[t]['sampled_safe_pre'] != old[t]['measured_safe_pre']:
            issues.append(f'v3 sampled claim differs t={t}')
    for t in range(663):
        for new, previous in legacy_map.items():
            if rows[t][new] != old[t][previous]:
                issues.append(f'v3 legacy decision differs t={t} field={new}')
    for key in ('rate', 'pre', 'post', 'probe', 'reserve_report', 'rate_report', 'delivery'):
        if rows[662][key] != old[662][key]:
            issues.append(f'v3 refusal boundary differs field={key}')
    return issues


def sidecar_issues(out, rows):
    expected = []
    for r in rows:
        if r['root_issued']:
            expected.append(root_event())
        if r['token_issued']:
            expected.append(token_event(r['t'], r['generation']))
    recorded = [json.loads(line) for line in (out/'authority-events.jsonl').read_text().splitlines()]
    authority = json.loads((out/'authority.json').read_text())
    issues = []
    if recorded != expected:
        issues.append('authority event log differs from paid trace events')
    expected_authority = {'root': next((e for e in expected if e['kind'] == 'root'), None),
                          'tokens': [e for e in expected if e['kind'] == 'token']}
    if authority != expected_authority:
        issues.append('final authority snapshot differs from issued event journal')
    return issues


def source_issues(out):
    issues = []
    meta = json.loads((out/'metadata.json').read_text())
    if meta.get('protocol_commit') != PROTOCOL or meta.get('dependency_commit') != DEPENDENCY:
        issues.append('protocol/dependency identity differs from preregistration')
    if meta.get('git_status_before_run') != '':
        issues.append('registered source snapshot was not clean')
    hashes = meta.get('sha256', {})
    expected_names = {p.name for p in ROOT.iterdir() if p.is_file() and
                      (p.suffix in ('.py', '.lean') or p.name == 'PREDICTION.md')}
    if not isinstance(hashes, dict) or set(hashes) != expected_names:
        issues.append('source hash inventory is incomplete or unexpected')
        hashes = hashes if isinstance(hashes, dict) else {}
    for name, expected in hashes.items():
        if name not in expected_names:
            continue
        path = ROOT/name
        if hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            issues.append('source hash differs: ' + name)
        rel = path.relative_to(REPO).as_posix()
        recorded = subprocess.check_output(['git', 'show', meta['code_commit'] + ':' + rel], cwd=REPO)
        if recorded != path.read_bytes():
            issues.append('executed commit/source differs: ' + name)
        implemented = subprocess.check_output(['git', 'show', meta['implementation_commit'] + ':' + rel], cwd=REPO)
        if implemented != path.read_bytes():
            issues.append('published implementation/source differs: ' + name)
    for name, key in (('CI_GATE.json', 'gate_sha256'), ('RUN_ATTEMPT.json', 'marker_sha256')):
        if hashlib.sha256((ROOT/name).read_bytes()).hexdigest() != meta.get(key):
            issues.append('published gate/attempt identity differs: ' + name)
        published = subprocess.check_output(['git', 'show', meta['code_commit'] +
                    ':research/recovery-v4/' + name], cwd=REPO)
        if published != (ROOT/name).read_bytes():
            issues.append('gate/attempt differs from executed published commit: ' + name)
    marker = json.loads((ROOT/'RUN_ATTEMPT.json').read_text())
    if (marker.get('attempt') != 1 or marker.get('protocol_commit') != PROTOCOL
            or marker.get('implementation_commit') != meta.get('implementation_commit')):
        issues.append('persistent first-attempt marker differs')
    gate = json.loads((ROOT/'CI_GATE.json').read_text())
    required = {'Refusal recovery proofs', 'R research checks', 'Kernel R Lean proofs',
                'Robust birth and latency evidence', 'Circuit simulation analysis'}
    runs = gate.get('runs', [])
    if (gate.get('head_sha') != DEPENDENCY or gate.get('pr_head_sha') != DEPENDENCY
            or not required <= {r['name'] for r in runs}):
        issues.append('prerequisite workflow inventory/head differs')
    for run in runs:
        if (run['head_sha'] != DEPENDENCY or run['status'] != 'completed'
                or run['conclusion'] != 'success' or run.get('run_attempt', 0) < 1
                or not run.get('jobs') or any(j['status'] != 'completed' or
                       j['conclusion'] != 'success' for j in run['jobs'])):
            issues.append('prerequisite workflow or latest-attempt job did not succeed')
    validation = json.loads((ROOT/'validation.json').read_text())
    if validation.get('sha256') != hashes:
        issues.append('pre-execution validated source hashes differ')
    protocol = subprocess.check_output(['git', 'show', PROTOCOL + ':research/recovery-v4/PREDICTION.md'], cwd=REPO)
    if protocol != (ROOT/'PREDICTION.md').read_bytes():
        issues.append('published protocol changed')
    frozen = ['research/refusal-recovery', 'research/self-certifying-learning',
              'research/discrete-refresh-experiment', 'research/adaptive-refresh-experiment',
              'research/refresh-contract-rupture']
    if subprocess.check_output(['git', 'diff', DEPENDENCY, '--', *frozen], cwd=REPO):
        issues.append('frozen prerequisite changed')
    return issues


def render(summary):
    m = summary['metrics']
    lines = ['# V4 recovery demonstration — unedited generated report', '',
             'Evidence from the single registered discrete attempt; no prediction is revised by this scorer.',
             f'Protocol: `{PROTOCOL}`. Frozen R1: `{DEPENDENCY}`.', '',
             '**Scope:** the new ceiling is justified by the registered simulator (constant leakage 140',
             'after the jump, below ceiling 150), not measured on a transistor circuit or inferred from',
             'past samples. This is not an unconditional guarantee for an unknown future environment.', '',
             '## Rupture, recovery and the authorization boundary', '',
             f'Legacy refusal: t={m["detection_time"]}. Recovery commands: {m["recovery_commands"]}.',
             f'Recovery deliveries: {m["recovery_deliveries"]}. Boundary-inclusive recovery probe/write cost: {m["recovery_boundary_cost"]}.',
             f'New service origin: post-delivery t={m["guaranteed_post_origin"]}; first guaranteed pre-instant: t={m["guaranteed_pre_first"]}.',
             f'First recovered sampled-safe pre-instant: t={m["first_recovered_sampled_safe"]}.',
             'The pre-delivery and post-delivery statuses are separate. The registered post-authorization',
             'boundary at 666 does not make pre666 safe, and no earlier dangerous period is relabelled.', '',
             '## All exposure and false declarations', '',
             '| Quantity | Recorded result |', '|---|---:|',
             f'| Pre-delivery unsafe periods | {len(m["pre_unsafe_times"])} |',
             f'| Post-delivery unsafe periods | {len(m["post_unsafe_times"])} |',
             f'| Undetected pre-unsafe periods | {len(m["undetected_times"])} |',
             f'| False sampled-instant claims | {len(m["false_sample_times"])} |',
             f'| False new pre-guarantee claims | {len(m["false_guaranteed_pre_times"])} |',
             f'| False new post-guarantee claims | {len(m["false_guaranteed_post_times"])} |',
             f'| True sampled-instant claims | {m["true_sample_claims"]} |', '',
             f'Pre-unsafe timestamps: {m["pre_unsafe_times"]}. Post-unsafe timestamps: {m["post_unsafe_times"]}.',
             f'Undetected timestamps: {m["undetected_times"]}.',
             f'Old incoming lease unsafe timestamps: {m["old_incoming_unsafe"]}.',
             f'Old after-detection conditional status unsafe timestamps: {m["old_after_detection_unsafe"]}.',
             f'**Unconditional uninterrupted service over the whole run: {summary["unconditional_service_verdict"]}.**', '',
             '## Complete declared cost', '',
             f'Paid probes: {m["probes"]}; commanded/delivered writes: {m["commands"]}/{m["deliveries"]}.',
             f'Writes by stage: legacy {m["legacy_writes"]}, recovery {m["recovery_writes"]}, authorized {m["authorized_writes"]}.',
             f'External root events: {m["roots"]}; token instantiations: {m["tokens"]}.',
             f'Probe/write cost: {m["probe_write_cost"]}; complete cost including root/tokens: {m["complete_cost"]}.',
             f'Final pre/post reserve: {m["final_pre"]}/{m["final_post"]}.',
             'The shared refusal and exit observations are paid once. The final readout is paid,',
             'completes a pending delivery, and issues no next command. Prices are abstract accounting',
             'units, not measured energy or human certification effort. Ordinary token renewals are',
             'not new physical refutations.', '',
             '## Registered predictions', '', '| ID | Verdict |', '|---|---|']
    lines += [f'| {key} | {"PASS" if value else "FAIL"} |' for key, value in summary['predictions'].items()]
    lines += ['', f'Audit issues: {len(summary["audit_issues"])}.']
    lines += ['- ' + issue for issue in summary['audit_issues']]
    lines += ['', 'All rows and their original claims are retained with an append hash chain.',
              'The independent audit checks arithmetic and saved evidence; it does not run a second',
              'controller trajectory. Local Lean results and this checked execution do not constitute',
              'a new formal refinement proof of the complete Python runner.', '']
    return '\n'.join(lines)


def evaluate(out):
    out = Path(out)
    load_issues = []
    try:
        rows = load_rows(out/'adaptive.csv')
    except (OSError, ValueError, TypeError) as exc:
        rows = []
        load_issues.append('trace could not be decoded: ' + str(exc))
    issues = audit(rows)
    issues += load_issues
    def evidence_check(label, operation):
        try:
            return operation()
        except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as exc:
            return [label + ' could not be audited: ' + str(exc)]
    prefix_issues = evidence_check('v3 prefix', lambda: prefix_check(rows))
    issues += prefix_issues
    issues += evidence_check('authority evidence', lambda: sidecar_issues(out, rows))
    issues += evidence_check('source evidence', lambda: source_issues(out))
    m = metrics(rows)
    indexed = {r['t']: r for r in rows}
    refused, entry = indexed.get(662, {}), indexed.get(666, {})
    last_pre = [r for r in rows if r['probe'] and r['t'] < JUMP]
    predictions = {
        'V1': not prefix_issues and bool(last_pre) and last_pre[-1]['t'] == 656
              and m['detection_time'] == 662 and m['legacy_invalidations'] == [662]
              and not m['legacy_ambiguities'] and refused.get('legacy_carried') == 139
              and refused.get('legacy_old_bound') == 20 and refused.get('rate_report') == 139,
        'V2': m['recovery_commands'] == list(range(662, 666))
              and m['recovery_deliveries'] == list(range(663, 667))
              and m['recovery_boundary_probes'] == list(range(662, 667))
              and m['recovery_boundary_cost'] == 45 and refused.get('lower') == -64
              and entry.get('lower') == 259
              and all(not r['guaranteed_pre'] and not r['guaranteed_post'] for r in rows if r['action'] == 'repair'),
        'V3': m['root_times'] == [666] and bool(m['token_times']) and m['token_times'][0] == 666
              and entry.get('permit_generation') == 1 and entry.get('permit_bound') == 150
              and entry.get('mode') == 'authorized-conditional' and not m['new_invalidations']
              and not m['failed_supervisor_visits'],
        'V4': m['guaranteed_post_origin'] == 666 and m['guaranteed_pre_first'] == 667
              and not entry.get('guaranteed_pre') and bool(entry.get('guaranteed_post'))
              and m['first_recovered_sampled_safe'] == 667
              and all(r['guaranteed_pre'] and r['pre'] >= SERVICE for r in rows if r['t'] >= 667)
              and all(r['guaranteed_post'] and r['post'] >= SERVICE for r in rows if r['t'] >= 666),
        'V5': not m['false_sample_times'] and not m['false_guaranteed_pre_times'] and not m['false_guaranteed_post_times']
              and m['true_sample_claims'] > 0 and m['true_guaranteed_pre'] > 0 and m['true_guaranteed_post'] > 0
              and m['pre_unsafe_times'] == list(range(661, 667)) and m['post_unsafe_times'] == list(range(661, 664))
              and m['undetected_times'] == [661],
        'V6': (m['probes'], m['commands'], m['deliveries'], m['legacy_writes'], m['recovery_writes'], m['authorized_writes'],
               m['tokens'], m['roots'], m['probe_write_cost'], m['complete_cost'], m['final_post'])
              == (838, 450, 450, 29, 4, 417, 82, 1, 5338, 5421, 440),
        'V7': m['old_after_detection_unsafe'] == [661] and m['old_incoming_unsafe'] == [661, 662]
              and bool(m['pre_unsafe_times'] or m['post_unsafe_times']),
        'V8': not issues and indexed.get(N, {}).get('command') == 0
              and indexed.get(N, {}).get('action') == 'terminal' and m['commands'] == m['deliveries'],
    }
    summary = {'metrics': m, 'predictions': predictions, 'audit_issues': issues,
               'prefix_matches_v3': not prefix_issues,
               'unconditional_service_verdict': 'REFUTED' if m['pre_unsafe_times'] or m['post_unsafe_times'] else 'NOT REFUTED',
               'trace_sha256': (hashlib.sha256((out/'adaptive.csv').read_bytes()).hexdigest()
                                if (out/'adaptive.csv').exists() else None),
               'terminal_chain_hash': rows[-1]['row_hash'] if rows else None}
    with (out/'summary.json').open('x') as stream:
        json.dump(summary, stream, indent=2)
        stream.write('\n')
    with (out/'REPORT.md').open('x') as stream:
        stream.write(render(summary))
    return summary
