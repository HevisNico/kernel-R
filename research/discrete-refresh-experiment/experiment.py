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
from controllers import Baseline, Contract, Observation, ROOT, DOSE, CAPACITY

PREDICTION_COMMIT = 'ca8645502588339c43e836b7319c6348dbebcfd2'
DEPENDENCY_COMMIT = 'ba978af1edaf51572aa0af9d1bfc83e309438d3d'
HORIZON, JUMP, INITIAL = 1320, 661, 440
FIELDS = ('t', 'rate', 'pre', 'post', 'probe', 'reserve_error', 'rate_error',
          'reserve_report', 'rate_report', 'alarm_before', 'alarm_detected',
          'alarm_after', 'delivery', 'command', 'due', 'lower', 'action',
          'delay', 'anchor', 'reopened', 'refused')


def leakage(t):
    return 10 if t < JUMP else 20


def sense(t, reserve, rate):
    ex, er = (7 * t + 1) % 5 - 2, (5 * t + 2) % 3 - 1
    return reserve + ex, rate + er, ex, er


def plant_step(reserve, rate, delivery):
    pre = reserve - rate
    return pre, min(CAPACITY, pre + DOSE) if delivery else pre


def trajectory(controller, output):
    reserve, due, pending, alarm = INITIAL, 0, None, False
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
                       reopened=0, refused=0)
            if due == t:
                yx, yl, ex, er = sense(t, pre, rate)
                obs = Observation(t, yx, yl, delivery)
                alarm = alarm or obs.lower_before < 100
                row.update(reserve_error=ex, rate_error=er, reserve_report=yx,
                           rate_report=yl, alarm_detected=int(alarm))
                # Detection precedes delivery; propagation uses the known dose,
                # not ground truth. The controller receives neither pre nor post.
                if obs.lower_after >= 100:
                    alarm = False
                decision = controller.decide(obs)
                row.update(lower=decision.lower, action=decision.action,
                           delay=decision.delay, anchor=decision.anchor,
                           reopened=int(decision.reopened),
                           refused=int(decision.action == 'refuse'))
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
            writer.writerow(row)
            stream.flush()
            reserve = post


def metadata():
    files = [ROOT / name for name in
             ('PREDICTION.md', 'Bridge.lean', 'controllers.py', 'experiment.py',
              'evaluate.py', 'test_synthetic.py')]
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
                       'dose': DOSE, 'capacity': CAPACITY},
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--run-once', action='store_true', required=True)
    parser.parse_args()
    # Preflight authenticates the published protocol and frozen dependency.
    published = subprocess.check_output(
        ['git', 'show', PREDICTION_COMMIT + ':research/discrete-refresh-experiment/PREDICTION.md'], cwd=ROOT)
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
    out = ROOT / 'run-v1'
    out.mkdir(exist_ok=False)
    contract = None
    try:
        (out / 'metadata.json').write_text(json.dumps(metadata(), indent=2) + '\n')
        with (out / 'lean-stderr.txt').open('x') as errors:
            contract = Contract(errors)
            for controller in [Baseline('naive'), Baseline('prudent'), contract]:
                trajectory(controller, out / f'{controller.name}.csv')
                print(f'completed {controller.name}', flush=True)
            contract.close()
            contract = None
        from evaluate import evaluate
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
