#!/usr/bin/env python3
"""Guard the actual third wire, protected B preparation and original birth trace."""
from pathlib import Path
import subprocess
import tempfile

from lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[1]
PREFIX = 'import KernelR.HybridFirstCoupledPreparedPair\nopen KernelR.Hybrid\n'


def cases():
    factory = """example {{θ fresh ε born}} (hs : @BirthState 1 born)
    (hb : @PhysicalBox 2 (extendParameters θ fresh) ε)
    (ha : ∀ p, born.aux 0 p = .ready)
    (hq : born.pending = sourceTrain 0 0 0 8 {count} ++ sourceTrain 0 0 160 8 16)
    (newborn : Newborn) (forward backward : ℝ → ℝ)
    (hd : ∀ time, (3/10:ℝ)≤forward time ∧ forward time≤2/5) :
    ∃ c : ConstructedBirthPreparation θ born,
      ∃ b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources,
        ∃ r : FirstWiredArrival b, ∃ s : FirstInterleavedPair r, ∃ w : SecondWiredArrival s,
          ∃ f : FirstReceiverFire w, ∃ g : FirstReceiverFastEnd f, ∃ v : FirstPostReceiverPair g,
            ∃ t : ThirdWiredArrival v, ∃ u : FirstCoupledPreparedPair t,
              CompleteThrough u.staged.after 184 ∧ u.final.pending.length=44 := by
  obtain ⟨c,b,r,s,w,f,g,v,t,u,hc,hp,_,_⟩ := birth_protocol_first_coupled_prepared_pair_exists hs hb ha hq newborn forward backward hd
  exact ⟨c,b,r,s,w,f,g,v,t,u,hc,hp⟩
"""
    ctx = """example {{θ born fresh newborn forward backward}}
    {{c : ConstructedBirthPreparation θ born}}
    {{b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}}
    {{r : FirstWiredArrival b}} {{s : FirstInterleavedPair r}} {{w : SecondWiredArrival s}}
    {{f : FirstReceiverFire w}} {{g : FirstReceiverFastEnd f}} {{v : FirstPostReceiverPair g}}
    (t : ThirdWiredArrival v) """
    end_ctx = ctx + """(u : FirstCoupledPreparedPair t) """
    delay = """(hd : ∀ time, (3/10:ℝ)≤forward time ∧ forward time≤2/5) """
    outcome = end_ctx + """{{ε}} (hb : @PhysicalBox 2 (extendParameters θ fresh) ε) """ + delay
    old_pending = ctx + """: v.final.pending.length={count} := by exact v.pending_length
"""
    old_mode = ctx + """: v.final.main 1=.{mode} := by exact v.b_main_slow
"""
    old_clock = ctx + """: v.final.x 1 .q=(1/4:ℝ)*Real.exp (-{recovery}*(176-g.fastB.final.time)) := by
  exact v.b_clock
"""
    issued = ctx + """: t.fire.final.pending.length={count} := by exact t.fire.pending_length
"""
    fire_gap = ctx + """: t.fire.final.time=w.fire.final.time+{gap} := by exact t.fire.firing_gap
"""
    new_delay = ctx + """: t.final.time=t.fire.final.time+{value} := by exact t.date
"""
    received_gap = ctx + delay + """: {lower}≤t.final.time-w.final.time ∧
    t.final.time-w.final.time≤81/10 := by exact t.received_gap hd
"""
    third_raw = ctx + """: t.final.raw 1 1=some {origin} := by exact t.raw_active
"""
    third_mode = ctx + """: t.final.main 1=.{mode} := by exact t.receiver_main_slow
"""
    third_charge = ctx + """: (7/50:ℝ)<t.final.x 1 .q ∧ t.final.x 1 .q<{upper} := by
  exact t.receiver_charge
"""
    third_recovery = ctx + """: t.final.x 1 .b={value} := by exact t.receiver_recovery
"""
    unissued = ctx + """: t.fire.before.pending={queue} := by rw [t.fire.product_before]; rfl
"""
    final_pending = end_ctx + """: u.final.pending.length={count} := by exact u.pending_length
"""
    all_ready = end_ctx + """: ∀ j, u.final.main j=.{mode} := by
  intro j
  exact (u.prepared j).ready
"""
    charge_a = end_ctx + """: u.final.x 0 .q={value} := by exact u.charge 0
"""
    charge_b = end_ctx + """: u.final.x 1 .q={value} := by exact u.charge 1
"""
    raw_a = end_ctx + """: u.final.raw 0 0=some {origin} := by exact u.raw_active
"""
    raw_b = end_ctx + """(p : Port) : u.final.raw 1 p={value} := by
  exact u.raw_other 1 p (Or.inl (by decide))
"""
    gain_b = outcome + """: u.final.x 1 (.z 1)={base}+3/5 := by
  exact u.b_gain_target hb hd
"""
    recovery_b = end_ctx + """: u.final.x 1 .b={value} := by exact u.b_recovery_own
"""
    other_gain_b = end_ctx + """(p : Port) (hp : p≠1) : u.final.x 1 (.z p)=newborn.x (.z p){extra} := by
  exact u.b_gain_other p hp
"""
    mark = end_ctx + """: u.execution.ledger.mark 1 1={dose} := by exact u.b_mark_dose
"""
    error = end_ctx + """(p : Port) : u.execution.ledger.error 1 p={dose} := by exact u.b_error_zero p
"""
    deliveries = end_ctx + """: u.staged.after.deliveries={value} := by exact u.staged_deliveries
"""
    emissions = end_ctx + """: u.staged.after.ledger.emissions={value} := by exact u.staged_emissions
"""
    complete = end_ctx + """: CompleteThrough u.staged.after {time} := by exact u.staged_complete
"""
    actual_a = ctx + """: t.final.x 0=t.cutA.state.x 0 ∧ t.final.main 0={mode} := by
  exact ⟨t.sender_values,t.sender_main⟩
"""
    gain_a = end_ctx + """(p : Port) : u.final.x 0 (.z p)=b.final.x 0 (.z p){extra} := by
  exact u.a_gains p
"""
    append_wire = ctx + """: t.fire.final.pending=firstPostReceiverPending++
    [⟨1,{port},t.fire.final.time+forward t.fire.final.time⟩] := by exact t.fire.protocol_pending
"""
    actual_deliveries = '[⟨0,0,160⟩,⟨1,1,r.final.time⟩,⟨0,0,168⟩,⟨1,1,w.final.time⟩,⟨0,0,176⟩,⟨1,1,t.final.time⟩,⟨0,0,184⟩]'
    false_deliveries = '[⟨0,0,160⟩,⟨1,1,r.final.time⟩,⟨0,0,168⟩,⟨1,1,w.final.time⟩,⟨0,0,176⟩,⟨1,1,t.final.time⟩]'
    actual_emissions = '[(0,r.fire.final.time),(0,w.fire.final.time),(1,f.final.time),(0,t.fire.final.time)]'
    false_emissions = '[(0,r.fire.final.time),(0,w.fire.final.time),(1,f.final.time),(0,t.fire.final.time),(1,184)]'
    return [
        ('original BirthState and all32 sources construct the coupled184 endpoint', factory.format(count='16'), factory.format(count='15')),
        ('the preceding real A176 arrival retains forty-five external sources', old_pending.format(count='45'), old_pending.format(count='44')),
        ('B remains physically SLOW at the intermediate clock176', old_mode.format(mode='slow'), old_mode.format(mode='ready')),
        ('the intermediate B charge retains its own newborn recovery clock', old_clock.format(recovery='newborn.x .b'), old_clock.format(recovery='(9/50:ℝ)')),
        ('the third real A FIRE adds exactly one wire token', issued.format(count='46'), issued.format(count='45')),
        ('the next actual A FIRE retains the own-root eight-gap identity', fire_gap.format(gap='8'), fire_gap.format(gap='79/10')),
        ('the third wire samples its delay at the third actual FIRE', new_delay.format(value='forward t.fire.final.time'), new_delay.format(value='forward w.fire.final.time')),
        ('the third receiving gap retains both fresh independent delays', received_gap.format(lower='79/10'), received_gap.format(lower='8')),
        ('the third wire has its own fresh receiving RAW origin', third_raw.format(origin='t.final.time'), third_raw.format(origin='w.final.time')),
        ('the third received input still meets a genuine SLOW cell', third_mode.format(mode='slow'), third_mode.format(mode='ready')),
        ('the third received charge is derived rather than replaced by rest', third_charge.format(upper='4/25'), third_charge.format(upper='7/50')),
        ('B still has its own low recovery before the protected MARK', third_recovery.format(value='newborn.x .b'), third_recovery.format(value='newborn.x .b+1/10')),
        ('the third pre-FIRE queue contains no unissued contact token', unissued.format(queue='firstPostReceiverPending'), unissued.format(queue='firstPostReceiverPending++[⟨1,1,t.final.time⟩]')),
        ('the actual A184 delivery leaves forty-four external source tokens', final_pending.format(count='44'), final_pending.format(count='45')),
        ('both cells have actually returned to their prepared READY modes', all_ready.format(mode='ready'), all_ready.format(mode='slow')),
        ('A carries the true resting charge after its constructed return', charge_a.format(value='1/10'), charge_a.format(value='1/4')),
        ('B carries the true resting charge after the protected return', charge_b.format(value='1/10'), charge_b.format(value='1/4')),
        ('the next actual A source has RAW origin184 rather than176', raw_a.format(origin='184'), raw_a.format(origin='176')),
        ('all B raw slots have genuinely expired at clock184', raw_b.format(value='none'), raw_b.format(value='some t.final.time')),
        ('the prepared B gain retains its own perturbed one-dose value', gain_b.format(base='newborn.x (.z 1)'), gain_b.format(base='Real.log (6/5)')),
        ('the protected B MARK adds one tenth to its own recovery', recovery_b.format(value='newborn.x .b+1/10'), recovery_b.format(value='newborn.x .b')),
        ('other B ports keep their own unchanged gains', other_gain_b.format(extra=''), other_gain_b.format(extra='+3/5')),
        ('the actual protected extension contributes precisely MARK one tenth', mark.format(dose='1/10'), mark.format(dose='1/5')),
        ('the actual protected extension adds no ERROR on any B port', error.format(dose='0'), error.format(dose='3/5')),
        ('the post-birth trace contains the seven real deliveries through184', deliveries.format(value=actual_deliveries), deliveries.format(value=false_deliveries)),
        ('the protected input invents no fifth post-birth output', emissions.format(value=actual_emissions), emissions.format(value=false_emissions)),
        ('terminal saturation is proved at184 rather than the next source', complete.format(time='184'), complete.format(time='192')),
        ('A at the third wire retains its exact maximal-cut physical state', actual_a.format(mode='t.cutA.state.main 0'), actual_a.format(mode='.ready')),
        ('B learning does not reset or retrain A own gains', gain_a.format(extra=''), gain_a.format(extra='+3/5')),
        ('the new contact token is issued to B port1 only by the actual FIRE', append_wire.format(port='1'), append_wire.format(port='2')),
    ]


def main():
    controls = cases()
    with tempfile.TemporaryDirectory(prefix='hybrid-coupled-preparation-negative-', dir=ROOT) as tmp:
        path = Path(tmp) / 'Check.lean'
        command = lean_check_command(tmp)

        def check(source, expected, name):
            path.write_text(PREFIX + source)
            result = subprocess.run([*command, str(path)], cwd=ROOT, text=True,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=180)
            if (result.returncode == 0) != expected:
                raise SystemExit(f'{name}: unexpected result:\n{result.stdout}')
            if not expected and 'error:' not in result.stdout:
                raise SystemExit(f'{name}: failed without a Lean diagnostic:\n{result.stdout}')

        check('\n'.join(good for _, good, _ in controls), True, 'valid coupled preparation controls')
        for name, _, bad in controls:
            check(bad, False, name)
            print(f'{name}: physical conclusion accepted; altered claim rejected.', flush=True)


if __name__ == '__main__':
    main()
