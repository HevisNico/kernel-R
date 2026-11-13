"""The single registered v4 trajectory. Never imported by CI or unit tests."""
import argparse
import contextlib
import csv
import hashlib
import json
from pathlib import Path
import platform
import subprocess
import sys
import traceback
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parent.parent
sys.path.insert(0, str(ROOT.parent / 'adaptive-refresh-experiment'))
from controllers import Contract, Observation as LegacyObservation
sys.path.insert(0, str(ROOT.parent / 'refusal-recovery'))
from controller import Supervisor, Observation
from authority import Authority
from boundary import truth_flags
from schema import (PROTOCOL, DEPENDENCY, N, JUMP, INITIAL, CAPACITY, DOSE,
                    REPAIR_BUDGET, PHASE_BUDGET, FIELDS, TEXT, chain_hash)


def git(*args):
    return subprocess.check_output(['git', *args], cwd=REPO, text=True).strip()


def source_hashes():
    return {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(ROOT.iterdir()) if p.is_file()
            and (p.suffix in ('.py', '.lean') or p.name == 'PREDICTION.md')}


def preflight(meta):
    if meta['git_status_before_run']:
        raise RuntimeError('Registered attempt requires a clean published snapshot')
    marker = json.loads((ROOT / 'RUN_ATTEMPT.json').read_text())
    if marker['attempt'] != 1 or marker['protocol_commit'] != PROTOCOL:
        raise RuntimeError('Unexpected persistent attempt marker')
    if marker['implementation_commit'] != meta['implementation_commit']:
        raise RuntimeError('Implementation marker mismatch')
    if git('show', PROTOCOL + ':research/recovery-v4/PREDICTION.md') != (ROOT / 'PREDICTION.md').read_text().strip():
        raise RuntimeError('Protocol differs from preregistration')
    for name in source_hashes():
        committed = subprocess.check_output(['git', 'show', marker['implementation_commit'] +
                                            ':research/recovery-v4/' + name], cwd=REPO)
        if committed != (ROOT / name).read_bytes():
            raise RuntimeError('Implementation changed after testing: ' + name)
    frozen = ['self-certifying-learning', 'discrete-refresh-experiment',
              'adaptive-refresh-experiment', 'refresh-contract-rupture', 'refusal-recovery']
    if git('diff', DEPENDENCY, '--', *['research/' + name for name in frozen]):
        raise RuntimeError('Frozen prerequisite changed')
    validation = json.loads((ROOT / 'validation.json').read_text())
    if validation['sha256'] != source_hashes():
        raise RuntimeError('Validated source hashes differ')
    gate = json.loads((ROOT / 'CI_GATE.json').read_text())
    required = {'Refusal recovery proofs', 'R research checks', 'Kernel R Lean proofs',
                'Robust birth and latency evidence', 'Circuit simulation analysis'}
    if gate['head_sha'] != DEPENDENCY or gate['pr_head_sha'] != DEPENDENCY:
        raise RuntimeError('Prerequisite CI is for a different head')
    if not required <= {r['name'] for r in gate['runs']}:
        raise RuntimeError('Missing prerequisite workflow')
    for run in gate['runs']:
        if run['head_sha'] != DEPENDENCY or run['status'] != 'completed' or run['conclusion'] != 'success':
            raise RuntimeError('Unfinished/failed prerequisite workflow')
        if not run['jobs'] or any(j['status'] != 'completed' or j['conclusion'] != 'success'
                                  for j in run['jobs']):
            raise RuntimeError('Unfinished/failed prerequisite job')


def metadata():
    marker = json.loads((ROOT / 'RUN_ATTEMPT.json').read_text())
    return dict(protocol_commit=PROTOCOL, dependency_commit=DEPENDENCY,
                implementation_commit=marker['implementation_commit'], code_commit=git('rev-parse', 'HEAD'),
                git_status_before_run=git('status', '--porcelain'),
                started_utc=datetime.now(timezone.utc).isoformat(), python=platform.python_version(),
                lean=subprocess.check_output(['lake', 'env', 'lean', '--version'],
                    cwd=ROOT.parent/'refusal-recovery', text=True).strip(), sha256=source_hashes(),
                command='python3 -B experiment.py --run-once',
                gate_sha256=hashlib.sha256((ROOT/'CI_GATE.json').read_bytes()).hexdigest(),
                marker_sha256=hashlib.sha256((ROOT/'RUN_ATTEMPT.json').read_bytes()).hexdigest())


def close_supervisor(supervisor, error_path):
    process = supervisor.process
    if process.poll() is None:
        process.stdin.close()
        try:
            process.wait(timeout=30)
        except subprocess.TimeoutExpired:
            process.kill()
            process.wait(timeout=10)
    errors = process.stderr.read()
    with error_path.open('a') as stream:
        stream.write(errors)
    supervisor.close()
    if process.returncode:
        raise RuntimeError('Recovery bridge exited with ' + str(process.returncode))


def trajectory(out):
    legacy, supervisor = None, None
    post, due, pending, alarm = INITIAL, 0, None, False
    legacy_u, legacy_expiry = None, None
    guaranteed, origin = False, ''
    totals = dict(cost_probes=0, cost_writes=0, cost_root=0, cost_tokens=0)
    previous_hash = '0' * 64
    try:
        with (out/'lean-stderr.txt').open('x') as errors, \
                (out/'authority-events.jsonl').open('x') as events, \
                (out/'adaptive.csv').open('x', newline='') as stream:
            legacy = Contract(errors)
            authority = Authority(events)
            writer = csv.DictWriter(stream, FIELDS)
            writer.writeheader()
            for t in range(N + 1):
                rate = 10 if t < JUMP else 140
                delivered = pending == t
                pre = post if t == 0 else post - rate
                post = min(CAPACITY, pre + DOSE) if delivered else pre
                if delivered:
                    pending = None
                probe = due == t or t == N
                old_pre = legacy_u is not None and t <= legacy_expiry
                guaranteed_pre = guaranteed and due is not None and t <= due
                row = {k: '' if k in TEXT else None for k in FIELDS}
                for name in ('command', 'root_issued', 'token_issued', 'legacy_invalidated',
                             'legacy_ambiguous', 'legacy_reopened', 'new_invalidated',
                             'sampled_safe_pre'):
                    row[name] = 0
                row.update(t=t, rate=rate, pre=pre, post=post, probe=int(probe),
                           delivery=int(delivered), alarm_before=int(alarm), terminal=int(t == N),
                           legacy_contract_pre=int(old_pre), guaranteed_pre=int(guaranteed_pre))
                root_event = authority.tick(t)
                row['root_issued'] = int(root_event)
                totals['cost_root'] += int(root_event)
                if probe:
                    totals['cost_probes'] += 1
                    ex, er = (7*t+1)%5-2, (5*t+2)%3-1
                    yr, yl = pre+ex, rate+er
                    lower_pre = yr-2
                    fresh = min(CAPACITY, lower_pre+DOSE) if delivered else lower_pre
                    row.update(reserve_error=ex, rate_error=er, reserve_report=yr, rate_report=yl,
                               sampled_safe_pre=int(lower_pre >= 100))
                    alarm = alarm or lower_pre < 100
                    row['alarm_detected'] = int(alarm)
                    if fresh >= 100:
                        alarm = False
                    if t == N:
                        row.update(action='terminal', delay=0, lower=fresh)
                        due = None
                    else:
                        if supervisor is None:
                            decision = legacy.decide(LegacyObservation(t, yr, yl, delivered))
                            row.update(legacy_action=decision.action, legacy_bound=decision.bound,
                                       legacy_carried=decision.carried, legacy_old_bound=decision.old_bound,
                                       legacy_invalidated=int(decision.invalidated),
                                       legacy_ambiguous=int(decision.ambiguous), legacy_anchor=decision.anchor,
                                       legacy_reopened=int(decision.reopened), legacy_lease_end=decision.lease_end,
                                       legacy_delay=decision.delay, legacy_lower=decision.lower)
                            if decision.action == 'refuse':
                                legacy_u, legacy_expiry = None, None
                                legacy.close()
                                legacy = None
                                supervisor = Supervisor(now=t, repair_budget=REPAIR_BUDGET,
                                                        phase_budget=PHASE_BUDGET, pending=delivered)
                            else:
                                legacy_u, legacy_expiry = decision.bound, decision.lease_end
                                row.update(action=decision.action, delay=decision.delay, lower=decision.lower)
                                due = t + decision.delay
                        if supervisor is not None:
                            offered = authority.offer(t, supervisor.generation, supervisor.mode, supervisor.remaining)
                            row['token_issued'] = int(offered is not None)
                            totals['cost_tokens'] += row['token_issued']
                            decision = supervisor.decide(Observation(t, yr, yl, delivered), offered)
                            row.update(action=decision.action, delay=decision.delay, lower=decision.lower,
                                       new_invalidated=int(decision.invalidated))
                            due = supervisor.due
                            guaranteed = (decision.mode == 'authorized-conditional' and
                                          supervisor.permit is not None and authority.root is not None)
                            if guaranteed and not origin:
                                origin = 'post:' + str(t)
                        if row['action'] in ('repair', 'write'):
                            if pending is not None or row['delay'] != 1:
                                raise RuntimeError('Overlapping or instantaneous command')
                            row['command'] = 1
                            pending = t+1
                            totals['cost_writes'] += 10
                else:
                    row['alarm_detected'] = int(alarm)
                row['mode'] = supervisor.mode if supervisor is not None else 'legacy'
                if supervisor is not None:
                    row.update(generation=supervisor.generation, fuel=supervisor.fuel,
                               phases_left=supervisor.permits_left, remaining=supervisor.remaining)
                    permit = supervisor.permit
                    if permit is not None:
                        row.update(permit_generation=permit.generation, permit_issue=permit.issued,
                                   permit_expiry=permit.expires, permit_bound=permit.bound,
                                   permit_decisions=permit.decisions)
                active_old = legacy_u is not None and t <= legacy_expiry
                row.update(due=due, alarm_after=int(alarm), legacy_contract_after=int(active_old),
                           legacy_ceiling=legacy_u, legacy_expires=legacy_expiry,
                           guaranteed_post=int(guaranteed), guarantee_origin=origin,
                           chain_previous=previous_hash, **totals)
                row.update(truth_flags(t, pre, post, row['alarm_detected'], row['sampled_safe_pre'],
                                       guaranteed_pre, guaranteed))
                row['row_hash'] = chain_hash(previous_hash, row)
                previous_hash = row['row_hash']
                writer.writerow(row)
                stream.flush()
            with (out/'authority.json').open('x') as f:
                json.dump(authority.snapshot(), f, indent=2)
                f.write('\n')
            if pending is not None:
                raise RuntimeError('Outstanding physical dose after terminal boundary')
            print('completed one registered v4 trajectory', flush=True)
            if supervisor is not None:
                print('Supervisor command/probe ledger:', supervisor.cost, flush=True)
    finally:
        if legacy is not None:
            legacy.close()
        if supervisor is not None:
            close_supervisor(supervisor, out/'lean-stderr.txt')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--run-once', action='store_true', required=True)
    parser.parse_args()
    out = ROOT/'run-v4'
    out.mkdir(exist_ok=False)
    status = 1
    try:
        meta = metadata()
        with (out/'metadata.json').open('x') as f:
            json.dump(meta, f, indent=2)
            f.write('\n')
        with (out/'stdout.txt').open('x') as stdout, (out/'stderr.txt').open('x') as stderr, \
                contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
            try:
                preflight(meta)
                trajectory(out)
                from score_v4 import evaluate
                summary = evaluate(out)
                print(json.dumps(summary, sort_keys=True), flush=True)
                status = int(bool(summary['audit_issues']) or not all(summary['predictions'].values()))
            except BaseException:
                (out/'FAILURE.txt').write_text(traceback.format_exc())
                traceback.print_exc()
    except BaseException:
        (out/'FAILURE.txt').write_text(traceback.format_exc())
        raise
    finally:
        (out/'exit-status.txt').write_text(str(status)+'\n')
    return status


if __name__ == '__main__':
    sys.exit(main())
