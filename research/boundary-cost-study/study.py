"""Exploratory cost study, not a preregistered v5 experiment or Lean proof.

Policies receive reports and certified carry only. The explicitly labelled
oracle separately uses the known scenario to compute a hindsight lower bound.
Historical experiment runners and evidence are never invoked or changed.
"""
from dataclasses import dataclass
from functools import lru_cache
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
BASE = '767f6ccece9cd2383d582fd884cc73afdf2f47f4'
N, INITIAL, SERVICE, DOSE, CAPACITY = 1320, 440, 100, 220, 660
POLICIES = ('prudent_hard', 'hard_max_wait', 'optimistic_shield', 'hard_fill')


def reserve_error(t):
    return (7*t+1) % 5 - 2


def rate_error(t):
    return (5*t+2) % 3 - 1


def leakage(t):
    return 10 if t < 661 else 140


def fresh_lower(report, delivered):
    return min(CAPACITY, report - 2 + DOSE) if delivered else report - 2


def next_lower(lower, hard, action, delay):
    return (min(CAPACITY, lower-hard+DOSE) if action == 'write'
            else lower-hard*delay)


def wait_limit(lower, hard):
    return min(40, max(0, (lower-SERVICE-hard)//hard))


@dataclass(frozen=True)
class Observation:
    time: int
    reserve_report: int
    rate_report: int
    delivered: bool


class Controller:
    def __init__(self, hard, policy):
        if policy not in POLICIES or hard not in (140, 150):
            raise ValueError('Unregistered exploratory policy/ceiling')
        self.hard, self.policy = hard, policy
        self.carry = None
        self.candidate = 'variation10'
        self.old_candidate_bound = None
        self.revisions = []
        self.clips = 0

    def decide(self, obs):
        lower = fresh_lower(obs.reserve_report, obs.delivered)
        if obs.rate_report - 1 > self.hard:
            self.carry = None
            return 'refuse', 0, lower
        if self.carry is not None:
            lower = max(lower, self.carry)
        if not SERVICE+self.hard <= lower <= CAPACITY:
            return 'refuse', 0, lower
        limit = wait_limit(lower, self.hard)
        action, delay = ('wait', limit) if limit else ('write', 1)
        if self.policy == 'prudent_hard':
            delay = 1
        elif self.policy == 'hard_fill':
            upper = (min(CAPACITY, obs.reserve_report+2+DOSE) if obs.delivered
                     else obs.reserve_report+2)
            if upper+DOSE <= CAPACITY:
                action, delay = 'write', 1
        elif self.policy == 'optimistic_shield':
            if (self.candidate == 'variation10' and self.old_candidate_bound is not None
                    and obs.rate_report-1 > self.old_candidate_bound):
                self.revisions.append(dict(time=obs.time, measured_lower=obs.rate_report-1,
                                           refuted_upper=self.old_candidate_bound))
                self.candidate = 'hard'
            if self.candidate == 'variation10':
                bound = min(self.hard, obs.rate_report+11)
                self.old_candidate_bound = bound
                proposed = min(40, max(0, (lower-SERVICE-bound-12)//bound))
                if proposed:
                    if proposed > limit:
                        self.clips += 1
                    action, delay = ('wait', min(proposed, limit)) if limit else ('write', 1)
                else:
                    action, delay = 'write', 1
        self.carry = next_lower(lower, self.hard, action, delay)
        return action, delay, lower


def simulate(hard, policy):
    controller = Controller(hard, policy)
    post, pending, due = INITIAL, None, 0
    probes = writes = deliveries = saturation = 0
    pre_unsafe, post_unsafe, refused, rows = [], [], [], []
    for t in range(N+1):
        rate = leakage(t)
        pre = post if t == 0 else post-rate
        delivered = pending == t
        post = min(CAPACITY, pre+DOSE) if delivered else pre
        if delivered:
            saturation += max(0, pre+DOSE-CAPACITY)
            deliveries += 1
            pending = None
        action, delay, lower = '', None, None
        probe = t == due or t == N
        if probe:
            probes += 1
            obs = Observation(t, pre+reserve_error(t), rate+rate_error(t), delivered)
            if t == N:
                action = 'terminal'
                lower = fresh_lower(obs.reserve_report, delivered)
                due = None
            else:
                action, delay, lower = controller.decide(obs)
                if action == 'refuse':
                    refused.append(t)
                    due = None
                else:
                    assert lower <= post
                    if action == 'wait':
                        assert lower-hard*delay >= SERVICE+hard
                    else:
                        assert lower-hard >= SERVICE
                        assert next_lower(lower, hard, action, delay) >= SERVICE+hard
                    due = t+delay
                    if action == 'write':
                        assert pending is None and delay == 1
                        writes += 1
                        pending = t+1
        if t and pre < SERVICE:
            pre_unsafe.append(t)
        if t and post < SERVICE:
            post_unsafe.append(t)
        rows.append(dict(t=t, pre=pre, post=post, probe=int(probe), delivery=int(delivered),
                         action=action, delay=delay, lower=lower, due=due))
    assert pending is None and writes == deliveries
    assert post == INITIAL - sum(leakage(t) for t in range(1, N+1)) + DOSE*deliveries - saturation
    return dict(H=hard, policy=policy, probes=probes, writes=writes, deliveries=deliveries,
                cost=probes+10*writes, unsafe_pre=pre_unsafe, unsafe_post=post_unsafe,
                refusals=refused, final_post=post, saturation_loss=saturation,
                revisions=controller.revisions, shield_clips=controller.clips,
                external_authorizations=0,
                prefix_probes=sum(r['probe'] for r in rows[:661]),
                prefix_writes=sum(r['action']=='write' for r in rows[:661]),
                min_pre=min(r['pre'] for r in rows[1:]),
                max_wait=max((r['delay'] or 0) for r in rows if r['action']=='wait'),
                trace_sha256=hashlib.sha256(json.dumps(rows, sort_keys=True).encode()).hexdigest()), rows


def legacy_prudent():
    path = ROOT.parent/'adaptive-refresh-experiment/controllers.py'
    spec = importlib.util.spec_from_file_location('frozen_v2_controllers', path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    controller = module.Baseline('prudent')
    post, pending, writes = INITIAL, False, 0
    unsafe, saturated = [], 0
    for t in range(N+1):
        pre = post if t == 0 else post-leakage(t)
        post = min(CAPACITY, pre+DOSE) if pending else pre
        saturated += max(0, pre+DOSE-CAPACITY) if pending else 0
        if t and pre < SERVICE:
            unsafe.append(t)
        delivered, pending = pending, False
        if t != N:
            d = controller.decide(module.Observation(t, pre+reserve_error(t),
                                                    leakage(t)+rate_error(t), delivered))
            pending = d.action == 'write'
            writes += pending
    return dict(policy='frozen_v2_prudent_on_v3_plant', probes=N+1, writes=writes,
                cost=N+1+10*writes, unsafe_pre=unsafe, final_post=post,
                saturation_loss=saturated, source_sha256=hashlib.sha256(path.read_bytes()).hexdigest())


def oracle(hard, horizon=N, rates=leakage, errors=reserve_error):
    """Exact finite DP within the stated hard-guard action family; uses future truth.

This is a hindsight comparator, not an autonomous controller or a general
physical lower bound. It may choose any certified wait, or an early write.
"""
    sys.setrecursionlimit(10000)
    prefix = [0]
    for t in range(1, horizon+1):
        prefix.append(prefix[-1]+rates(t))

    def transitions(t, post, lower):
        cap = min(wait_limit(lower, hard), horizon-t)
        for delay in range(1, cap+1):
            end = t+delay
            new_post = post-(prefix[end]-prefix[t])
            carried = lower-hard*delay
            fresh = new_post+errors(end)-2
            yield ('wait', delay, end, new_post, max(fresh, carried), 1)
        end = t+1
        pre = post-rates(end)
        new_post = min(CAPACITY, pre+DOSE)
        carried = min(CAPACITY, lower-hard+DOSE)
        fresh = min(CAPACITY, pre+errors(end)-2+DOSE)
        yield ('write', 1, end, new_post, max(fresh, carried), 11)

    @lru_cache(None)
    def best(t, post, lower):
        if t == horizon:
            return 1
        assert SERVICE+hard <= lower <= post <= CAPACITY
        return min(fee+best(end, new_post, new_lower)
                   for _, _, end, new_post, new_lower, fee in transitions(t, post, lower))

    initial_lower = INITIAL+errors(0)-2
    optimum = best(0, INITIAL, initial_lower)
    t, post, lower = 0, INITIAL, initial_lower
    probes, writes, min_pre, saturated = 1, 0, INITIAL, 0
    while t < horizon:
        edge = next(edge for edge in transitions(t, post, lower)
                    if edge[-1]+best(edge[2], edge[3], edge[4]) == best(t, post, lower))
        action, delay, end, new_post, new_lower, _ = edge
        pre = post-(prefix[end]-prefix[t])
        min_pre = min(min_pre, pre)
        if action == 'write':
            writes += 1
            saturated += max(0, pre+DOSE-CAPACITY)
        probes += 1
        t, post, lower = end, new_post, new_lower
    assert optimum == probes+10*writes and min_pre >= SERVICE
    return dict(H=hard, cost=optimum, probes=probes, writes=writes, min_pre=min_pre,
                final_post=post, saturation_loss=saturated, states=best.cache_info().currsize,
                scope='hindsight optimum in hard-guard action family; not deployable policy')


def main():
    results, traces = [], {}
    for hard in (140, 150):
        for policy in POLICIES:
            result, rows = simulate(hard, policy)
            results.append(result)
            traces[f'{hard}:{policy}'] = rows
    output = dict(status='EXPLORATORY; not preregistered v5 evidence', base_commit=BASE,
                  parameters=dict(horizon=N, initial=INITIAL, service=SERVICE, dose=DOSE,
                                  capacity=CAPACITY, jump=661, before=10, after=140,
                                  reserve_error=2, rate_error=1, probe_price=1, write_price=10),
                  conservation_lower_bound=dict(loss=99000, writes=449, write_cost=4490),
                  policies=results, legacy_prudent=legacy_prudent(),
                  oracle=[oracle(hard) for hard in (140,150)],
                  optimistic_actions_identical_to_hard={str(h):traces[f'{h}:optimistic_shield']==traces[f'{h}:hard_max_wait'] for h in (140,150)})
    (ROOT/'RESULTS.json').write_text(json.dumps(output, indent=2)+'\n')
    print(json.dumps(output, indent=2))


if __name__ == '__main__':
    main()
