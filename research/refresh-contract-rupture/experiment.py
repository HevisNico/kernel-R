"""Single registered comparison. An exclusive output directory prevents retries.

Controllers receive Observation only. Truth stays in this plant and scorer.
"""
import argparse
import csv
import hashlib
import json
import platform
import subprocess
import sys
import traceback
from datetime import datetime, timezone
from pathlib import Path
ROOT = Path(__file__).resolve().parent
V2 = ROOT.parent / 'adaptive-refresh-experiment'
sys.path.insert(0, str(V2))
from controllers import Contract, Observation, DOSE, CAPACITY
from score_rupture import chain_hash

PREDICTION_COMMIT = '07caf3fdf22c1cd28f05a2159d40aceaa33af80b'
DEPENDENCY_COMMIT = 'ba978af1edaf51572aa0af9d1bfc83e309438d3d'
HORIZON, JUMP, INITIAL = 1320, 661, 440
FIELDS = ('t', 'rate', 'pre', 'post', 'probe', 'reserve_error', 'rate_error',
          'reserve_report', 'rate_report', 'alarm_before', 'alarm_detected',
          'alarm_after', 'delivery', 'command', 'due', 'lower', 'action',
          'delay', 'anchor', 'reopened', 'refused', 'bound', 'carried', 'old_bound',
          'lease_end', 'ambiguous', 'invalidated', 'measured_safe_pre',
          'conditional_contract_active', 'active_ceiling', 'active_expires', 'invalidation_latched',
          'truth_unsafe_pre', 'truth_unsafe_post', 'truth_undetected', 'truth_above_active_ceiling',
          'truth_unsafe_under_contract', 'chain_previous', 'row_hash')


def leakage(t):
    return 10 if t < JUMP else 140


def sense(t, reserve, rate):
    ex, er = (7 * t + 1) % 5 - 2, (5 * t + 2) % 3 - 1
    return reserve + ex, rate + er, ex, er


def plant_step(reserve, rate, delivery):
    pre = reserve - rate
    return pre, min(CAPACITY, pre + DOSE) if delivery else pre


def trajectory(controller, output):
    reserve, due, pending, alarm = INITIAL, 0, None, False
    active_ceiling, active_expires, invalidation = None, None, False
    previous_hash = '0' * 64
    with output.open('x', newline='') as stream:
        writer = csv.DictWriter(stream, FIELDS)
        writer.writeheader()
        for t in range(HORIZON + 1):
            rate = leakage(t)
            delivery = pending == t
            pre, post = ((reserve, reserve) if t == 0 else plant_step(reserve, rate, delivery))
            if delivery:
                pending = None
            row = dict.fromkeys(FIELDS, '')
            row.update(t=t, rate=rate, pre=pre, post=post, probe=int(due == t),
                       alarm_before=int(alarm), delivery=int(delivery), command=0,
                       reopened=0, refused=0, ambiguous=0, invalidated=0, measured_safe_pre=0)
            if due == t:
                yx, yl, ex, er = sense(t, pre, rate)
                obs = Observation(t, yx, yl, delivery)
                alarm = alarm or obs.lower_before < 100
                row.update(reserve_error=ex, rate_error=er, reserve_report=yx,
                           rate_report=yl, alarm_detected=int(alarm),
                           measured_safe_pre=int(obs.lower_before >= 100))
                # Detection precedes delivery; propagation uses the known dose,
                # not ground truth. The controller receives neither pre nor post.
                if obs.lower_after >= 100:
                    alarm = False
                decision = controller.decide(obs)
                row.update(lower=decision.lower, action=decision.action,
                           delay=decision.delay, anchor=decision.anchor,
                           reopened=int(decision.reopened),
                           refused=int(decision.action == 'refuse'), bound=decision.bound,
                           carried=decision.carried, old_bound=decision.old_bound,
                           lease_end=decision.lease_end, ambiguous=int(decision.ambiguous),
                           invalidated=int(decision.invalidated))
                invalidation = invalidation or decision.invalidated
                if decision.action == 'refuse':
                    active_ceiling, active_expires = None, None
                else:
                    active_ceiling, active_expires = decision.bound, decision.lease_end
                if t == HORIZON or decision.action == 'refuse':
                    due = None
                else:
                    if decision.delay <= 0:
                        raise RuntimeError('Nonpositive controller delay')
                    due = t + decision.delay
                    if decision.action == 'write':
                        if pending is not None or decision.delay != 1:
                            raise RuntimeError('Overlapping or instantaneous write')
                        pending = t + 1
                        row['command'] = 1
            else:
                row['alarm_detected'] = int(alarm)
            row.update(alarm_after=int(alarm), due=due)
            active = active_ceiling is not None and t <= active_expires and not invalidation
            row.update(conditional_contract_active=int(active), active_ceiling=active_ceiling,
                       active_expires=active_expires, invalidation_latched=int(invalidation),
                       truth_unsafe_pre=int(t>0 and pre<100), truth_unsafe_post=int(t>0 and post<100),
                       truth_undetected=int(t>0 and pre<100 and not row['alarm_detected']),
                       truth_above_active_ceiling=int(active and rate>active_ceiling),
                       truth_unsafe_under_contract=int(t>0 and active and pre<100),
                       chain_previous=previous_hash)
            # Claims are fixed now, appended once, never revised after later detection.
            row['row_hash'] = chain_hash(previous_hash, row)
            previous_hash = row['row_hash']
            writer.writerow(row)
            stream.flush()
            reserve = post


def metadata():
    files = [ROOT / name for name in
             ('PREDICTION.md', 'experiment.py', 'score_rupture.py', 'test_synthetic.py', 'check_evidence.py')]
    return {
        'protocol_commit': PREDICTION_COMMIT, 'dependency_commit': DEPENDENCY_COMMIT,
        'code_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
        'git_status_before_run': subprocess.check_output(['git', 'status', '--porcelain'], cwd=ROOT, text=True),
        'started_utc': datetime.now(timezone.utc).isoformat(),
        'python': platform.python_version(),
        'lean': subprocess.check_output(['lake', 'env', 'lean', '--version'],
                    cwd=ROOT.parent / 'self-certifying-learning', text=True).strip(),
        'command': 'python3 -B experiment.py --run-once',
        'sha256': {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
        'parameters': {'horizon': HORIZON, 'jump': JUMP, 'initial': INITIAL,
                       'dose': DOSE, 'capacity': CAPACITY, 'leak_before':10, 'leak_after':140},
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--run-once', action='store_true', required=True)
    parser.parse_args()
    # Preflight authenticates the published protocol and frozen dependency.
    published = subprocess.check_output(
        ['git', 'show', PREDICTION_COMMIT + ':research/refresh-contract-rupture/PREDICTION.md'], cwd=ROOT)
    if published != (ROOT / 'PREDICTION.md').read_bytes():
        raise RuntimeError('Protocol differs from published preregistration')
    base = ROOT.parent / 'self-certifying-learning'
    recorded = json.loads((base / 'validation.json').read_text())
    for path, expected in recorded['sha256'].items():
        if hashlib.sha256((base / path).read_bytes()).hexdigest() != expected:
            raise RuntimeError('Frozen dependency source mismatch: ' + path)
    changes = subprocess.check_output(
        ['git', 'diff', DEPENDENCY_COMMIT, '--', 'research/self-certifying-learning'], cwd=ROOT.parent.parent)
    if changes:
        raise RuntimeError('Dependency changed since frozen #111 commit')
    old = subprocess.check_output(['git', 'diff', 'ebaac53a49f2f904b9feb07e071c3b5af18746fa', '--',
        'research/discrete-refresh-experiment'], cwd=ROOT.parent.parent)
    if old:
        raise RuntimeError('Frozen v1 evidence changed')
    v2_changes = subprocess.check_output(['git','diff','09b8558fd41516de816544920b5c40315cf53a80','--',
        'research/adaptive-refresh-experiment'], cwd=ROOT.parent.parent)
    if v2_changes:
        raise RuntimeError('Frozen v2 changed')
    out = ROOT / 'run-v3'
    out.mkdir(exist_ok=False)
    contract = None
    try:
        (out / 'metadata.json').write_text(json.dumps(metadata(), indent=2) + '\n')
        with (out / 'lean-stderr.txt').open('x') as errors:
            contract = Contract(errors)
            for controller in [contract]:
                trajectory(controller, out / f'{controller.name}.csv')
                print(f'completed {controller.name}', flush=True)
            contract.close()
            contract = None
        from score_rupture import evaluate
        summary = evaluate(out)
        print(json.dumps(summary, sort_keys=True), flush=True)
    except BaseException:
        (out / 'FAILURE.txt').write_text(traceback.format_exc())
        print(traceback.format_exc(), file=sys.stderr, flush=True)
        raise
    finally:
        if contract is not None:
            contract.process.terminate()
            contract.process.wait(timeout=30)


if __name__ == '__main__':
    main()
