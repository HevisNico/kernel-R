"""Frozen registered constants and canonical append-chain encoding."""
import hashlib
import json

PROTOCOL = '62c09e0409712467aa32466957bf06413c26887f'
DEPENDENCY = 'c6684f796d092b2324489cb9920f78a9fcca7a5a'
N, JUMP, AUTHORIZE = 1320, 661, 666
INITIAL, SERVICE, CAPACITY, DOSE, BOUND, EXPIRY = 440, 100, 660, 220, 150, 1640
REPAIR_BUDGET, PHASE_BUDGET, PHASE_SIZE = 8, 82, 8
FIELDS = ('t', 'rate', 'pre', 'post', 'probe', 'reserve_error', 'rate_error',
          'reserve_report', 'rate_report', 'delivery', 'command', 'mode', 'action',
          'delay', 'lower', 'due', 'generation', 'fuel', 'phases_left', 'remaining',
          'permit_generation', 'permit_issue', 'permit_expiry', 'permit_bound', 'permit_decisions',
          'root_issued', 'token_issued', 'legacy_action', 'legacy_bound', 'legacy_carried',
          'legacy_old_bound', 'legacy_invalidated', 'legacy_ambiguous', 'legacy_anchor',
          'legacy_reopened', 'legacy_lease_end', 'legacy_delay', 'legacy_lower',
          'alarm_before', 'alarm_detected', 'alarm_after', 'sampled_safe_pre',
          'legacy_contract_pre', 'legacy_contract_after', 'legacy_ceiling', 'legacy_expires',
          'guaranteed_pre', 'guaranteed_post', 'guarantee_origin', 'terminal',
          'new_invalidated', 'cost_probes', 'cost_writes', 'cost_root', 'cost_tokens',
          'truth_unsafe_pre', 'truth_unsafe_post', 'truth_undetected',
          'truth_false_sample', 'truth_false_guarantee_pre', 'truth_false_guarantee_post',
          'chain_previous', 'row_hash')
TEXT = {'mode', 'action', 'legacy_action', 'guarantee_origin', 'chain_previous', 'row_hash'}


def chain_hash(previous, row):
    payload = {k: '' if v is None else str(v) for k, v in row.items() if k != 'row_hash'}
    return hashlib.sha256((previous + '\n' + json.dumps(
        payload, sort_keys=True, separators=(',', ':'))).encode()).hexdigest()
