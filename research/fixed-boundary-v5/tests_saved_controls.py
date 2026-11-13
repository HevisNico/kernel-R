"""Semantic mutations of saved v5 evidence, with valid replacement hash chains.

No registered evidence is read at import time. Only call after the single batch.
"""
from copy import deepcopy
import json
from pathlib import Path

from audit import audit_trace, load_rows
from common import chain_hash


def rechain(rows):
    previous = '0'*64
    for row in rows:
        row['chain_previous'] = previous
        row['row_hash'] = chain_hash(previous,row)
        previous = row['row_hash']


def overlong_wait(rows):
    row = next(r for r in rows if r['action']=='wait')
    row['delay'] = 3
    row['due'] = row['t']+3


def optimistic_carry(rows):
    row = next(r for r in rows if r['action'] in ('write','wait'))
    row['carry_after'] += 130


def omit_probe_charge(rows):
    for row in rows:
        row['probes'] -= 1


def instantaneous_dose(rows):
    row = next(r for r in rows if r['action']=='write' and not r['delivered'])
    row['delivered'] = 1
    row['post'] = min(660,row['pre']+220)


def terminal_command(rows):
    row = rows[-1]
    row.update(action='write',delay=1,due=row['t']+1)
    row['writes'] += 1


def ignore_hard_violation(rows):
    row = next(r for r in rows if r['action']=='refuse')
    row.update(action='wait',delay=1,due=row['t']+1,conditional_post=1,refused=0)


CONTROLS = (
    ('overlong_wait_without_latency_reserve','known',overlong_wait,'proved policy arithmetic and next calendar'),
    ('optimistic_carried_bound','known',optimistic_carry,'outgoing fixed-H carry'),
    ('omit_paid_initial_probe','known',omit_probe_charge,'complete cumulative ledger and dose saturation'),
    ('instantaneous_delivery','known',instantaneous_dose,'loss, signed reserve and delayed dose'),
    ('command_beyond_horizon','known',terminal_command,'proved policy arithmetic and next calendar'),
    ('ignore_measured_hard_violation','outside',ignore_hard_violation,'latched refusal without automatic restart'),
)


def run_saved_controls(out):
    out = Path(out)
    scenarios, traces = {}, {}
    for name in ('known','outside'):
        scenarios[name] = json.loads((out/'scenarios'/f'{name}.json').read_text())
        traces[name] = load_rows(out/'traces'/f'{name}-early.csv.gz')
        baseline = audit_trace(scenarios[name],'early',traces[name])
        if baseline:
            raise AssertionError('Positive saved trace failed: '+name+': '+repr(baseline))
    original = json.dumps(traces,sort_keys=True)
    passed = []
    for label,name,mutate,diagnostic in CONTROLS:
        changed = deepcopy(traces[name])
        mutate(changed)
        if changed == traces[name]:
            raise AssertionError('Inactive mutation: '+label)
        rechain(changed)
        issues = audit_trace(scenarios[name],'early',changed)
        if any('append-chain predecessor' in i or 'unchanged emitted row' in i for i in issues):
            raise AssertionError('Mutation relied on broken hash integrity: '+label)
        if not any(diagnostic in issue for issue in issues):
            raise AssertionError('Mutation escaped intended semantic check: '+label+': '+repr(issues))
        passed.append(label)
    if json.dumps(traces,sort_keys=True) != original:
        raise AssertionError('Controls changed original evidence')
    return passed
