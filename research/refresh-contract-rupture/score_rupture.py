"""Read-only scoring and independent decision audit of recorded v3 evidence.
No controller or plant trajectory is run here.
"""
import csv
import hashlib
import json
from pathlib import Path

N, JUMP, FLOOR = 1320, 661, 100
TEXT = {'action','chain_previous','row_hash'}


def chain_hash(previous, row):
    payload = {k: '' if v is None else str(v) for k,v in row.items() if k != 'row_hash'}
    return hashlib.sha256((previous+'\n'+json.dumps(payload,sort_keys=True,separators=(',',':'))).encode()).hexdigest()


def load_rows(path):
    with path.open(newline='') as f:
        return [{k: v if k in TEXT else int(v) if v else None for k,v in row.items()}
                for row in csv.DictReader(f)]


def metrics(rows):
    scored=[r for r in rows if r['t']>0]
    invalid=[r['t'] for r in rows if r['invalidated']]
    detection=invalid[0] if invalid else None
    post_probes=[r['t'] for r in rows if r['probe'] and r['t']>=JUMP]
    unsafe=[r for r in scored if r['pre']<100]
    hidden=[r for r in unsafe if not r['alarm_detected']]
    conditional=[r['t'] for r in unsafe if r['conditional_contract_active']]
    false_claims=[r['t'] for r in rows if r['measured_safe_pre'] and r['pre']<100]
    before=[r['t'] for r in rows if r['probe'] and r['t']<JUMP]
    last=next((r for r in reversed(rows) if r['probe'] and r['t']<JUMP),None)
    first_law_breach=None
    for i,r in enumerate(rows):
        if any(r['rate']>p['rate']+10 for p in rows[max(0,i-41):i+1]):
            first_law_breach=r['t']; break
    writes=sum(r['command'] for r in rows); probes=sum(r['probe'] for r in rows)
    return dict(probes=probes,writes=writes,delivered=sum(r['delivery'] for r in rows),
                probe_cost=probes,write_cost=10*writes,total_cost=probes+10*writes,
                detection_time=detection,first_post_jump_probe=post_probes[0] if post_probes else None,
                last_pre_jump_probe=before[-1] if before else None,
                active_spacing=last['delay'] if last else None,
                detection_delay=detection-JUMP if detection is not None else None,
                invalidations=len(invalid),ambiguous=sum(r['ambiguous'] for r in rows),
                refusals=sum(r['refused'] for r in rows),
                pre_unsafe=len(unsafe),post_unsafe=sum(r['post']<100 for r in scored),
                unsafe_before_detection=sum(r['t']<detection for r in unsafe) if detection is not None else len(unsafe),
                unsafe_at_detection=sum(r['t']==detection for r in unsafe),
                unsafe_after_detection=sum(r['t']>detection for r in unsafe) if detection is not None else 0,
                undetected=len(hidden),undetected_times=[r['t'] for r in hidden],
                unsafe_with_active_conditional_contract=len(conditional),conditional_unsafe_times=conditional,
                false_measured_safe=len(false_claims),false_measured_safe_times=false_claims,
                true_measured_safe=sum(r['measured_safe_pre'] and r['pre']>=100 for r in rows),
                probes_after_refusal=sum(r['probe'] for r in rows if detection is not None and r['t']>detection),
                commands_at_or_after_refusal=sum(r['command'] for r in rows if detection is not None and r['t']>=detection),
                active_periods_at_or_after_refusal=sum(r['conditional_contract_active'] for r in rows if detection is not None and r['t']>=detection),
                final_reserve=rows[-1]['post'],first_physical_law_breach=first_law_breach,
                global_variation_premise_satisfied=first_law_breach is None)


def audit(rows):
    issues=[]
    def check(condition,t,msg):
        if not condition: issues.append(f't={t}: {msg}')
    check(len(rows)==N+1,-1,'complete scored horizon, including after refusal')
    previous_hash='0'*64
    post,previous_command,due,alarm=440,0,0,0
    anchor,old_decision=None,None
    active_u,expiry,latched=None,None,False
    for index,r in enumerate(rows):
        t=r['t']; check(t==index,t,'chronological row index')
        check(r['chain_previous']==previous_hash,t,'append chain predecessor')
        check(r['row_hash']==chain_hash(previous_hash,r),t,'row unchanged since chain emission')
        previous_hash=r['row_hash']
        rate=10 if t<JUMP else 140
        check(r['rate']==rate,t,'registered leakage')
        pre=440 if t==0 else post-rate
        check(r['pre']==pre,t,'loss before sensing')
        check(r['delivery']==previous_command,t,'one-period delayed dose')
        post=min(660,pre+220) if previous_command else pre
        check(r['post']==post,t,'physical step, no floor clipping')
        check(r['probe']==int(due==t),t,'paid probe schedule')
        check(r['alarm_before']==alarm,t,'service-alarm memory')
        if r['probe']:
            ex,ey=(7*t+1)%5-2,(5*t+2)%3-1
            check((r['reserve_error'],r['rate_error'])==(ex,ey),t,'registered noise')
            check((r['reserve_report'],r['rate_report'])==(pre+ex,rate+ey),t,'bounded-error reports')
            raw_lower=r['reserve_report']-2
            check(r['measured_safe_pre']==int(raw_lower>=100),t,'sample-only safety assertion')
            alarm=int(bool(alarm or raw_lower<100))
            check(r['alarm_detected']==alarm,t,'alarm before dose')
            fresh=min(660,raw_lower+220) if previous_command else raw_lower
            if fresh>=100: alarm=0
            u=r['rate_report']+11
            old_u,carried,invalid,ambiguous=None,None,False,False
            if old_decision is not None:
                old=old_decision; old_u=old['bound']
                check(t==old['t']+old['delay'] and t<=old['lease_end'],t,'old lease covers probe')
                carried=(old['lower']-old_u*old['delay'] if old['action']=='wait'
                         else min(660,old['lower']+220-old_u))
                invalid=max(0,r['rate_report']-1)>old_u
                ambiguous=not invalid and r['rate_report']+1>old_u
            lower=fresh if invalid or carried is None else max(fresh,carried)
            check((r['bound'],r['old_bound'],r['carried'],r['lower'])==(u,old_u,carried,lower),t,'bound/carry provenance; discard on violation')
            check((r['invalidated'],r['ambiguous'])==(int(invalid),int(ambiguous)),t,'demonstrated versus ambiguous violation')
            center=r['rate_report']
            if anchor is None: anchor=center
            reopen=abs(center-anchor)>=7
            if reopen: anchor=center
            check(r['anchor']==anchor and r['reopened']==int(reopen),t,'anchor hysteresis')
            if invalid or lower<100+u or lower>660 or u>=220 or 100+2*u>660:
                kind,delay='refuse',0
            else:
                delay=min(40,(lower-100-u-12)//u) if lower>=100+u+12 else 0
                kind,delay=('wait',delay) if delay>0 else ('write',1)
            check((r['action'],r['delay'])==(kind,delay),t,'unchanged Lean policy decision')
            check(r['refused']==int(kind=='refuse') and r['lease_end']==t+41,t,'refusal and diagnostic horizon')
            latched=latched or invalid
            if kind=='refuse': active_u,expiry=None,None
            else: active_u,expiry=u,t+41
            command=int(kind=='write' and t<N)
            check(r['command']==command,t,'command accounting')
            due=None if t==N or kind=='refuse' else t+delay
            old_decision=r
        else:
            check(r['alarm_detected']==alarm,t,'no unobserved detection')
            check(not r['measured_safe_pre'] and not r['command'] and not r['invalidated']
                  and not r['refused'] and not r['action'],t,'no unobserved control or safe claim')
            check(all(r[k] is None for k in ('reserve_report','rate_report','lower','bound','delay')),t,'no free observations')
        active=active_u is not None and t<=expiry and not latched
        check(r['alarm_after']==alarm and r['due']==due,t,'alarm/scheduling state')
        check((r['conditional_contract_active'],r['active_ceiling'],r['active_expires'],r['invalidation_latched'])
              ==(int(active),active_u,expiry,int(latched)),t,'accepted lease status, not diagnostic ceiling')
        truth=(int(t>0 and pre<100),int(t>0 and post<100),int(t>0 and pre<100 and not r['alarm_detected']),
               int(active and rate>active_u),int(t>0 and active and pre<100))
        check(tuple(r[k] for k in ('truth_unsafe_pre','truth_unsafe_post','truth_undetected',
                                  'truth_above_active_ceiling','truth_unsafe_under_contract'))==truth,t,'uncensored scorer flags')
        previous_command=r['command']
    return issues


def render(summary):
    m=summary['metrics']
    lines=['# V3 contract rupture — unedited generated report','',
           'One preregistered negative-test trajectory. V2 and V1 were not rerun or modified.',
           'Protocol: `07caf3fdf22c1cd28f05a2159d40aceaa33af80b`.','',
           '## Detection and blocked stop','',
           f'Last pre-jump probe: {m["last_pre_jump_probe"]}; spacing: {m["active_spacing"]} periods.',
           f'First post-jump probe and invalidation: {m["detection_time"]}; delay: {m["detection_delay"]} period(s).',
           f'Demonstrated invalidations: {m["invalidations"]}; ambiguous exceedances: {m["ambiguous"]}; refusals: {m["refusals"]}.',
           f'After refusal: {m["probes_after_refusal"]} probes, {m["commands_at_or_after_refusal"]} commands, '
           f'{m["active_periods_at_or_after_refusal"]} active-contract periods.',
           'The record distinguishes the new diagnostic ceiling from an accepted contract.', '',
           '## Unsafe exposure — including after refusal','',
           '| Quantity | Periods |','|---|---:|',
           f'| Dangerous strictly before detection | {m["unsafe_before_detection"]} |',
           f'| Dangerous at detection | {m["unsafe_at_detection"]} |',
           f'| Dangerous after detection | {m["unsafe_after_detection"]} |',
           f'| All pre-write unsafe | {m["pre_unsafe"]} |',
           f'| All post-write unsafe | {m["post_unsafe"]} |',
           f'| Undetected unsafe | {m["undetected"]} |',
           f'| Unsafe with active conditional contract | {m["unsafe_with_active_conditional_contract"]} |',
           f'| False sampled-instant safety declarations | {m["false_measured_safe"]} |','',
           f'True sampled-instant safety declarations: {m["true_measured_safe"]}.',
           f'Undetected unsafe timestamps: {m["undetected_times"]}.',
           f'Unsafe conditional-contract timestamps: {m["conditional_unsafe_times"]}.',
           f'First physical B/H breach: {m["first_physical_law_breach"]}; global variation premise satisfied: '
           f'{m["global_variation_premise_satisfied"]}.','',
           '**Unconditional uninterrupted service: '+summary['unconditional_service_verdict']+'.**',
           'A conditional contract was still active during the unseen jump. Its past period',
           'is not relabeled safe after detection. Sampled safety claims use only fresh',
           'sensor lower bounds and never extend to an unobserved interval.','',
           '## Repair power and cost','',
           'Dose 220 > 140 × latency 1; physical net gain would be 80 per commanded write.',
           'Thus the refusal is not an actuator-power impossibility. At detection, the old',
           'contract is contradicted and the fresh entry lower is below the ready guard.',
           'The preregistered policy is blocked stop, not emergency recovery.',
           f'Probes: {m["probes"]}; commands/deliveries: {m["writes"]}/{m["delivered"]}; '
           f'cost: {m["probe_cost"]}+{m["write_cost"]}={m["total_cost"]}.',
           f'Final signed reserve: {m["final_reserve"]}.','',
           '## Registered predictions','', '| ID | Verdict |','|---|---|']
    lines += [f'| {k} | {"PASS" if v else "FAIL"} |' for k,v in summary['predictions'].items()]
    lines += ['',f'Trace audit issues: {len(summary["audit_issues"])}.']
    lines += ['- '+i for i in summary['audit_issues']]
    lines += ['', 'No parameter or prediction was changed after publication; no registered run was repeated.',
              'Rows were appended and hash-chained at emission; no retrospective label update is performed.',
              'All 1320 physical periods are counted even though control stops at refusal.',
              'This is a deliberately selected counterexample using the published v2 prefix,',
              'not a probabilistic guarantee or a physical transistor validation.', '']
    return '\n'.join(lines)


def evaluate(out):
    rows=load_rows(out/'adaptive.csv'); issues=audit(rows); m=metrics(rows)
    v2=out.parent.parent/'adaptive-refresh-experiment'/'run-v2'/'adaptive.csv'
    # On a copied evidence directory the caller supplies the original prefix path.
    if not v2.exists():
        v2=Path(__file__).resolve().parent.parent/'adaptive-refresh-experiment/run-v2/adaptive.csv'
    with v2.open(newline='') as f: original=list(csv.DictReader(f))
    with (out/'adaptive.csv').open(newline='') as f: current=list(csv.DictReader(f))
    prefix=all(all(current[t][k]==value for k,value in original[t].items()) for t in range(661))
    detection=next((r for r in rows if r['invalidated']),None)
    d=detection or {}
    predictions={
        'R1': m['last_pre_jump_probe']==656 and m['active_spacing']==6 and m['first_post_jump_probe']==m['detection_time']==662
              and m['detection_delay']==1 and m['detection_delay']<=m['active_spacing']
              and d.get('rate_report')==139 and d.get('old_bound')==20 and m['invalidations']==1 and m['ambiguous']==0,
        'R2': d.get('action')=='refuse' and d.get('lower')==-64 and d.get('carried')==139
              and m['probes_after_refusal']==m['commands_at_or_after_refusal']==m['active_periods_at_or_after_refusal']==0,
        'R3': m['false_measured_safe']==0 and m['true_measured_safe']>0
              and not any('chain' in i or 'safety assertion' in i or 'unobserved' in i for i in issues),
        'R4': m['unsafe_before_detection']==1 and m['unsafe_before_detection']<=m['active_spacing']
              and m['unsafe_at_detection']==1 and m['unsafe_after_detection']==658
              and m['pre_unsafe']==m['post_unsafe']==660 and m['undetected']==1,
        'R5': m['conditional_unsafe_times']==[661],
        'R6': prefix and m['first_physical_law_breach']==661 and m['final_reserve']==-92180
              and all(not r['invalidated'] and not r['refused'] for r in rows if r['t']<661),
        'R7': not issues and not m['global_variation_premise_satisfied'],
    }
    summary={'metrics':m,'predictions':predictions,'prefix_matches_v2':prefix,'audit_issues':issues,
             'unconditional_service_verdict':'REFUTED' if m['pre_unsafe'] else 'NOT REFUTED',
             'trace_sha256':hashlib.sha256((out/'adaptive.csv').read_bytes()).hexdigest(),
             'terminal_chain_hash':rows[-1]['row_hash']}
    with (out/'summary.json').open('x') as f: json.dump(summary,f,indent=2);f.write('\n')
    with (out/'REPORT.md').open('x') as f: f.write(render(summary))
    return summary
