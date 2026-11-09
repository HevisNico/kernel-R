#!/usr/bin/env python3
"""Guard the constructed first B output, actual FAST exit and exact birth trace."""
from pathlib import Path
import subprocess
import tempfile

from scripts.lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[2]
PREFIX = 'import KernelR.HybridConstructedReceiverFire\nimport KernelR.HybridFirstReceiverFastEnd\nopen KernelR.Hybrid\n'


def cases():
    factory = """example {{θ fresh ε born}} (hs : @BirthState 1 born)
    (hb : @PhysicalBox 2 (extendParameters θ fresh) ε)
    (ha : ∀ p, born.aux 0 p = .ready)
    (hq : born.pending = sourceTrain 0 0 0 8 {count} ++ sourceTrain 0 0 160 8 16)
    (newborn : Newborn) (forward backward : ℝ → ℝ)
    (hd : ∀ t, (3/10:ℝ)≤forward t ∧ forward t≤2/5) :
    ∃ c : ConstructedBirthPreparation θ born,
      ∃ b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources,
        ∃ r : FirstWiredArrival b, ∃ s : FirstInterleavedPair r, ∃ w : SecondWiredArrival s,
          ∃ f : FirstReceiverFire w,
            CompleteThrough f.staged.after f.final.time ∧ f.final.pending.length=46 := by
  exact birth_protocol_first_receiver_fire_exists hs hb ha hq newborn forward backward hd
"""
    ctx = """example {{θ born fresh newborn forward backward}}
    {{c : ConstructedBirthPreparation θ born}}
    {{b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}}
    {{r : FirstWiredArrival b}} {{s : FirstInterleavedPair r}} {{w : SecondWiredArrival s}}
    (f : FirstReceiverFire w) """
    fast_ctx = ctx + """(v : FirstReceiverFastEnd f) """
    outcome = ctx + """{{ε}} (hb : @PhysicalBox 2 (extendParameters θ fresh) ε)
    (hd : ∀ t, (3/10:ℝ)≤forward t ∧ forward t≤2/5) """
    singleton = ctx + """: f.execution.ledger.emissions = [({cell},f.final.time)] := by
  exact f.emissions
"""
    route = ctx + """: reciprocalEntryRouter forward backward 1 f.final.time = {value} := by
  exact f.route_closed
"""
    fire_pending = ctx + """: f.final.pending.length = {count} := by exact f.pending_length
"""
    gain = outcome + """: f.final.x 1 (.z 1) = {base}+3/5 := by
  exact f.receiver_gain_target hb hd
"""
    recovery = ctx + """: f.final.x 1 .b = {value} := by exact f.receiver_recovery
"""
    gain_bounds = outcome + """: 9/5≤Real.exp (f.final.x 1 (.z 1)) ∧
    Real.exp (f.final.x 1 (.z 1))≤{upper} := by
  have hz := newborn.gain (1 : Port)
  simp only [nominalGain,ite_true] at hz
  have hown := f.receiver_gain_target hb hd
  have hg : 9/5≤Real.exp (f.final.x 1 (.z 1)) ∧ Real.exp (f.final.x 1 (.z 1))≤11/5 :=
    fast_learned_gain_sharp_bounds (by rw [hown]; linarith [hz.1])
      (by rw [hown]; linarith [hz.2])
  exact hg
"""
    raw_fire = ctx + """: f.final.raw 1 1 = some {value} := by exact f.raw_active
"""
    mode_fire = ctx + """: f.final.main 1 = .{mode} := by exact f.receiver_main_fast
"""
    charge_fire = ctx + """: f.final.x 1 .q = {value} := by exact f.receiver_charge
"""
    mode_fast = fast_ctx + """: v.final.main 1 = .{mode} := by exact v.b_main_slow
"""
    charge_fast = fast_ctx + """: v.final.x 1 .q = {value} := by exact v.b_charge
"""
    raw_fast = fast_ctx + """(p : Port) : v.final.raw 1 p = {value} := by exact v.b_raw_none p
"""
    actual_a = ctx + """: f.final.x 0 = f.cutA.state.x 0 ∧ f.final.main 0 = {mode} := by
  exact ⟨f.sender_values,f.sender_main⟩
"""
    complete = fast_ctx + """: CompleteThrough f.execution f.final.time ∧
    CompleteThrough v.execution {time} := by exact ⟨f.complete,v.complete⟩
"""
    staged_outputs = ctx + """: f.staged.after.ledger.emissions =
    [(0,r.fire.final.time),(0,w.fire.final.time),({cell},f.final.time)] := by
  exact f.staged_emissions
"""
    staged_deliveries = ctx + """: f.staged.after.deliveries = {value} := by
  exact f.staged_deliveries
"""
    date_bounds = ctx + """(hd : ∀ t, (3/10:ℝ)≤forward t ∧ forward t≤2/5) :
    (169+1/10:ℝ)<f.final.time ∧ f.final.time<{upper} := by exact f.date_bounds hd
"""
    fast_date = fast_ctx + """: v.final.time = f.final.time+{duration} := by exact v.date
"""
    fast_pending = fast_ctx + """: v.final.pending.length = {count} := by exact v.pending_length
"""
    delivered = '[⟨0,0,160⟩,⟨1,1,r.final.time⟩,⟨0,0,168⟩,⟨1,1,w.final.time⟩]'
    invented_delivery = '[⟨0,0,160⟩,⟨1,1,r.final.time⟩,⟨0,0,168⟩,⟨1,1,w.final.time⟩,⟨1,1,f.final.time⟩]'
    return [
        ('the original birth factory constructs the first real B firing', factory.format(count='16'), factory.format(count='15')),
        ('the actual first receiver output is a B emission', singleton.format(cell='1'), singleton.format(cell='0')),
        ('a closed reverse contact does not suppress the actual B firing', route.format(value='[]'), route.format(value='[⟨0,2,f.final.time+backward f.final.time⟩]')),
        ('B firing preserves all forty-six queued external sources', fire_pending.format(count='46'), fire_pending.format(count='45')),
        ('B firing retains its own perturbed learned gain', gain.format(base='newborn.x (.z 1)'), gain.format(base='Real.log (6/5)')),
        ('B recovery has not acquired a protected MARK dose yet', recovery.format(value='newborn.x .b'), recovery.format(value='9/50')),
        ('the once-trained fast port uses the proved sharp2.2 band', gain_bounds.format(upper='11/5'), gain_bounds.format(upper='2')),
        ('the B firing retains its actual second-wire raw origin', raw_fire.format(value='w.final.time'), raw_fire.format(value='f.final.time')),
        ('the actual receiver FIRE enters FAST', mode_fire.format(mode='fast'), mode_fire.format(mode='ready')),
        ('the actual receiver FIRE has threshold charge one', charge_fire.format(value='1'), charge_fire.format(value='1/4')),
        ('the actual receiver FAST exit enters SLOW', mode_fast.format(mode='slow'), mode_fast.format(mode='ready')),
        ('the actual receiver FAST exit reaches its one-quarter guard', charge_fast.format(value='1/4'), charge_fast.format(value='1/10')),
        ('the original second-wire raw has physically expired by FAST exit', raw_fast.format(value='none'), raw_fast.format(value='some w.final.time')),
        ('A retains its exact maximal-cut state without a READY substitution', actual_a.format(mode='f.cutA.state.main 0'), actual_a.format(mode='.ready')),
        ('both the actual B firing and FAST exit are terminally saturated', complete.format(time='v.final.time'), complete.format(time='f.final.time')),
        ('the post-birth ledger keeps both A firings and the real B firing', staged_outputs.format(cell='1'), staged_outputs.format(cell='0')),
        ('the actual B FIRE does not invent another wire delivery', staged_deliveries.format(value=delivered), staged_deliveries.format(value=invented_delivery)),
        ('the real B firing uses the physical response-plus-wire bracket', date_bounds.format(upper='170+1/5'), date_bounds.format(upper='169')),
        ('B FAST completion preserves its actual one-unit duration', fast_date.format(duration='1'), fast_date.format(duration='1/2')),
        ('the interleaved FAST suffix does not append or lose source tokens', fast_pending.format(count='46'), fast_pending.format(count='47')),
    ]


def main():
    controls = cases()
    with tempfile.TemporaryDirectory(prefix='hybrid-receiver-fire-negative-', dir=ROOT) as tmp:
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

        check('\n'.join(good for _, good, _ in controls), True, 'valid first receiver fire controls')
        for name, _, bad in controls:
            check(bad, False, name)
            print(f'{name}: physical conclusion accepted; altered claim rejected.', flush=True)


if __name__ == '__main__':
    main()
