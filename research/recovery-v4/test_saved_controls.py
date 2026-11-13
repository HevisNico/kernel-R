"""Semantic controls on saved evidence only; never generates a trajectory.

Importing this module does not read evidence. Call run_saved_controls after the
registered attempt. Mutations affect deep copies and receive valid new hash
chains, so rejection must come from the arithmetic/contract audit itself.
"""
import argparse
from copy import deepcopy
import json
from pathlib import Path

from schema import AUTHORIZE, N, REPAIR_BUDGET, chain_hash
from score_v4 import audit, load_rows


def rechain(rows):
    previous = '0' * 64
    for row in rows:
        row['chain_previous'] = previous
        row['row_hash'] = chain_hash(previous, row)
        previous = row['row_hash']


def claim_unsafe_pre_boundary(rows):
    row = rows[AUTHORIZE]
    row['guaranteed_pre'] = 1
    row['truth_false_guarantee_pre'] = int(row['pre'] < 100)


def omit_root_charge(rows):
    for row in rows[AUTHORIZE:]:
        row['cost_root'] -= 1


def omit_first_token_charge(rows):
    for row in rows[AUTHORIZE:]:
        row['cost_tokens'] -= 1


def retain_revoked_lease(rows):
    refusal = next(i for i, row in enumerate(rows) if row['legacy_action'] == 'refuse')
    row, previous = rows[refusal], rows[refusal - 1]
    row['legacy_contract_after'] = 1
    row['legacy_ceiling'] = previous['legacy_ceiling']
    row['legacy_expires'] = previous['legacy_expires']


def omit_terminal_delivery(rows):
    row = rows[N]
    row['delivery'] = 0
    row['post'] = row['pre']
    row['lower'] = row['reserve_report'] - 2
    row['truth_unsafe_post'] = int(row['post'] < 100)
    row['truth_false_guarantee_post'] = int(bool(row['guaranteed_post']) and row['post'] < 100)


def refill_repair_credit(rows):
    for row in rows[AUTHORIZE:]:
        row['fuel'] = REPAIR_BUDGET


CONTROLS = (
    ('claim_pre666_from_post_authorization', claim_unsafe_pre_boundary,
     'new guarantee uses incoming pre boundary'),
    ('omit_root_cost', omit_root_charge, 'cumulative complete cost ledger'),
    ('omit_first_token_cost', omit_first_token_charge, 'cumulative complete cost ledger'),
    ('retain_old_lease_at_refusal', retain_revoked_lease, 'old lease revoked before post status'),
    ('omit_last_delivery', omit_terminal_delivery, 'registered loss, signed reserve and delayed saturated delivery'),
    ('refund_recovery_credit', refill_repair_credit, 'no credit refill; exact generation/phase accounting'),
)


def run_saved_controls(rows):
    baseline = audit(rows)
    if baseline:
        raise AssertionError('Positive saved-evidence audit failed: ' + '\n'.join(baseline))
    if len(rows) != N + 1 or rows[N]['delivery'] != 1:
        raise AssertionError('Controls require the complete recorded terminal delivery')
    original = json.dumps(rows, sort_keys=True)
    passed = []
    for name, mutate, expected_diagnostic in CONTROLS:
        changed = deepcopy(rows)
        mutate(changed)
        if changed == rows:
            raise AssertionError('Mutation did not change recorded evidence: ' + name)
        rechain(changed)
        issues = audit(changed)
        if any('append-chain predecessor' in issue or 'unchanged emitted row' in issue for issue in issues):
            raise AssertionError('Control relied on broken hash integrity: ' + name)
        if not any(expected_diagnostic in issue for issue in issues):
            raise AssertionError('Semantic mutation escaped its intended check: ' + name + '\n' + '\n'.join(issues))
        passed.append(name)
    if json.dumps(rows, sort_keys=True) != original:
        raise AssertionError('A control modified original evidence')
    return passed


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--evidence', type=Path, required=True,
                        help='Existing adaptive.csv from the single registered attempt')
    args = parser.parse_args()
    passed = run_saved_controls(load_rows(args.evidence))
    print(json.dumps({'saved_semantic_controls': passed}, indent=2))


if __name__ == '__main__':
    main()
