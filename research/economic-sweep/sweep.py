"""Exploratory parameter grid; no v5/v6 trajectory or preregistered campaign.

The reference policies remain price-blind. The separate oracle knows the
future and optimizes each price on the fixed hard-ready action family.
"""
import argparse
import csv
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import traceback

ROOT = Path(__file__).resolve().parent
SOURCE_HASH = 'df390c631ce3bf9b77bd506b37343b912d02d8f1f49f9eccb3fb1568444a0e43'


def reference(path=None):
    if path is None:
        candidates = [ROOT.parent/'boundary-cost-study/study.py',
                      ROOT.parent/'kernel-R/research/boundary-cost-study/study.py']
        path = next((p for p in candidates if p.exists()), candidates[0])
    path = Path(path)
    if hashlib.sha256(path.read_bytes()).hexdigest() != SOURCE_HASH:
        raise RuntimeError('Reference source hash changed')
    spec = importlib.util.spec_from_file_location('frozen_boundary_study',path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def rate(scenario,t):
    if scenario == 'jump':
        return 10 if t<133 else 140
    if scenario == 'high':
        return 140
    raise ValueError(scenario)


def noise(t):
    return (7*t+1)%5-2


def simulate(ref, capacity, scenario, policy, horizon=264):
    ref.CAPACITY = capacity
    controller = ref.Controller(150,policy)
    post, due, pending = min(440,capacity), 0, None
    probes = writes = delivered_count = saturation = 0
    rows, unsafe_pre, unsafe_post, refusals = [],[],[],[]
    for t in range(horizon+1):
        pre = post if t==0 else post-rate(scenario,t)
        delivered = pending==t
        post = min(capacity,pre+220) if delivered else pre
        if delivered:
            pending = None
            delivered_count += 1
            saturation += max(0,pre+220-capacity)
        probe = due==t or t==horizon
        action,delay,lower = '',None,None
        if probe:
            probes += 1
            obs = ref.Observation(t,pre+noise(t),rate(scenario,t)+(5*t+2)%3-1,delivered)
            if t==horizon:
                action,due = 'terminal',None
                lower=ref.fresh_lower(obs.reserve_report,delivered)
            else:
                action,delay,lower = controller.decide(obs)
                if action=='refuse':
                    refusals.append(t)
                    due=None
                else:
                    assert 250 <= lower <= post <= capacity
                    assert action in ('wait','write') and delay>=1
                    if action=='wait':
                        assert lower-150*delay>=250
                    else:
                        assert lower-150>=100 and min(capacity,lower-150+220)>=250
                        assert pending is None and delay==1
                        writes += 1
                        pending=t+1
                    due=t+delay
        if t and pre<100:
            unsafe_pre.append(t)
        if t and post<100:
            unsafe_post.append(t)
        rows.append(dict(t=t,pre=pre,post=post,probe=int(probe),delivery=int(delivered),
                         action=action,delay=delay,lower=lower,due=due))
    assert pending is None and writes==delivered_count
    assert post==min(440,capacity)-sum(rate(scenario,t) for t in range(1,horizon+1))+220*writes-saturation
    return dict(probes=probes,writes=writes,final_reserve=post,saturation_loss=saturation,
                unsafe_pre=unsafe_pre,unsafe_post=unsafe_post,refusals=refusals,
                revisions=controller.revisions,clips=controller.clips,
                min_pre=min(r['pre'] for r in rows[1:]),
                trace_sha256=hashlib.sha256(json.dumps(rows,sort_keys=True).encode()).hexdigest()),rows


def action_difference(first,second):
    keys=('probe','action','delay','due')
    differing=[a['t'] for a,b in zip(first,second) if any(a[k]!=b[k] for k in keys)]
    return dict(differing_periods=len(differing),first_difference=differing[0] if differing else None)


def forward_oracle(capacity,scenario,prices,write_price=100,horizon=264):
    """Forward shortest paths with independent cost vectors for each price."""
    initial=min(440,capacity)
    layers=[{} for _ in range(horizon+1)]
    layers[0][(initial,initial+noise(0)-2)]=tuple(prices)
    loss=[0]
    for t in range(1,horizon+1):
        loss.append(loss[-1]+rate(scenario,t))
    states=0
    for t in range(horizon):
        current=layers[t]
        states+=len(current)
        for (post,lower),costs in current.items():
            assert 250<=lower<=post<=capacity
            maxwait=min(40,horizon-t,max(0,(lower-250)//150))
            edges=[]
            for delay in range(1,maxwait+1):
                end=t+delay
                true=post-(loss[end]-loss[t])
                bound=max(lower-150*delay,true+noise(end)-2)
                assert true>=100
                edges.append((end,true,bound,0))
            end=t+1
            pre=post-rate(scenario,end)
            true=min(capacity,pre+220)
            bound=max(min(capacity,lower-150+220),min(capacity,pre+noise(end)-2+220))
            assert pre>=100
            edges.append((end,true,bound,write_price))
            for end,true,bound,write_fee in edges:
                key=(true,bound)
                previous=layers[end].get(key)
                values=tuple(cost+price+write_fee for cost,price in zip(costs,prices))
                layers[end][key]=values if previous is None else tuple(min(x,y) for x,y in zip(values,previous))
        layers[t]={}
    states+=len(layers[-1])
    best=tuple(min(values[i] for values in layers[-1].values()) for i in range(len(prices)))
    return dict(costs=best,states=states,scope='hindsight optimum in fixed hard-ready action family')


def report(result):
    lines=['# Exploratory economic sweep', '',
           '**Not v5/v6 confirmatory evidence.** The finite grid and two scenarios were written',
           'before this calculation. No v5 scenario or seed was used.', '',
           'H=150, dose220, service100, horizon264, initial=min(440,capacity).',
           'The seven capacities are 300,440,660,1000,1500,3000,6600. Probe/write price',
           'ratios are .01,.1,1,10. The policies are price-blind; price reweights a fixed',
           'physical trace and does not cause a policy revision.', '',
           '| Scenario | Capacity | Different optimistic/fixed periods | Optimistic probes/writes | Fixed probes/writes |',
           '|---|---:|---:|---:|---:|']
    for c in result['cases']:
        a,b=c['policies']['optimistic_shield'],c['policies']['hard_max_wait']
        lines.append(f"| {c['scenario']} | {c['capacity']} | {c['action_difference']['differing_periods']} | {a['probes']}/{a['writes']} | {b['probes']}/{b['writes']} |")
    benefit=[c for c in result['cells'] if c['optimistic_cost']<c['fixed_cost'] and c['actions_differ']]
    worsened=[c for c in result['cells'] if c['optimistic_cost']>c['fixed_cost']]
    lines+=['',f"Across {len(result['cells'])} scenario/capacity/price cells, action-changing optimistic benefits: **{len(benefit)}**; higher-cost optimistic cells: **{len(worsened)}**.",
            '', 'Complete cells, oracle gaps and policy terminal inventories are retained in RESULTS.json',
            'and cells.csv; no unsuccessful or inconvenient cell is removed.', '',
            '## Economic opportunity not captured by this optimistic law', '',
            'For jump, capacity6600 (capacity/H=44) and probe/write price10, the fixed',
            'and optimistic policies cost255000 integer units, versus oracle105000:',
            'a 142.86% oracle gap. Early refill costs119400, a 13.71% gap. These costs',
            'use write price100 and probe price1000. Thus the present optimistic law',
            'finds no economic benefit, but substantial policy-optimization room exists.',
            'It would be incorrect to infer that all possible learning is useless.', '',
            'Early refill ends that case at reserve3520 versus440 for fixed/optimistic;',
            'unused terminal stock has no value in this objective. Future comparisons',
            'must keep that endpoint convention explicit and must not credit this',
            'fixed heuristic improvement to learning.', '',
            '## Interpretation', '',
            'The jump scenario tests low leakage followed by a refutation. The high scenario',
            'starts at constant140 so the variation candidate need not be refuted: its extra',
            '12-unit planning margin can alter waits/writes. A benefit there is an economic',
            'effect of a fixed margin/threshold, not evidence that a learned rule improved.',
            'No policy here learns a new law, and no universal conclusion follows from this grid.', '',
            'The oracle knows every future loss and sensor error and may deliberately trade',
            'saturation for probes. It explores only one-write / hard-ready-at-next-probe actions,',
            'with maximum wait40 and no terminal inventory value. It is neither a deployable',
            'controller nor a global physical optimum. Reported policy gaps are relative to',
            'that comparator and can reflect different final inventories.', '',
            'Safety checks retain all unsafe pre/post periods and refusals. This sweep contains',
            'no new Lean proof or transistor evidence. It is repeatable exploratory computation.', '']
    return '\n'.join(lines)


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--source',type=Path)
    args=parser.parse_args()
    grid=json.loads((ROOT/'grid.json').read_text())
    ref=reference(args.source)
    cases,cells=[],[]
    for scenario in grid['scenarios']:
        for capacity in grid['capacities']:
            policies,traces={},{}
            for policy in grid['policies']:
                policies[policy],traces[policy]=simulate(ref,capacity,scenario,policy,grid['horizon'])
            oracle=forward_oracle(capacity,scenario,grid['probe_prices'],grid['write_price'],grid['horizon'])
            diff=action_difference(traces['hard_max_wait'],traces['optimistic_shield'])
            cases.append(dict(scenario=scenario,capacity=capacity,policies=policies,oracle=oracle,action_difference=diff))
            for i,price in enumerate(grid['probe_prices']):
                costs={name:price*v['probes']+grid['write_price']*v['writes'] for name,v in policies.items()}
                assert all(cost>=oracle['costs'][i] for cost in costs.values())
                cells.append(dict(scenario=scenario,capacity=capacity,capacity_over_H=capacity/150,
                    probe_over_write=price/grid['write_price'],oracle_cost=oracle['costs'][i],
                    fixed_cost=costs['hard_max_wait'],optimistic_cost=costs['optimistic_shield'],
                    fill_cost=costs['hard_fill'],actions_differ=bool(diff['differing_periods']),
                    fixed_gap=(costs['hard_max_wait']-oracle['costs'][i])/oracle['costs'][i],
                    optimistic_gap=(costs['optimistic_shield']-oracle['costs'][i])/oracle['costs'][i],
                    fill_gap=(costs['hard_fill']-oracle['costs'][i])/oracle['costs'][i]))
            print(f"completed {scenario} capacity={capacity}, states={oracle['states']}",flush=True)
    result=dict(status='EXPLORATORY ONLY',grid=grid,reference_sha256=SOURCE_HASH,
                plan_sha256=hashlib.sha256((ROOT/'PLAN.md').read_bytes()).hexdigest(),cases=cases,cells=cells)
    (ROOT/'RESULTS.json').write_text(json.dumps(result,indent=2)+'\n')
    with (ROOT/'cells.csv').open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=list(cells[0]))
        writer.writeheader();writer.writerows(cells)
    (ROOT/'REPORT.md').write_text(report(result))
    print('completed exploratory grid',flush=True)


if __name__=='__main__':
    try:
        main()
    except BaseException:
        with (ROOT/'FAILURES.log').open('a') as log:
            log.write(datetime.now(timezone.utc).isoformat()+'\n'+traceback.format_exc()+'\n')
        raise
