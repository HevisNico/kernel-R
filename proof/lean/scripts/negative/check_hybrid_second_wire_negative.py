#!/usr/bin/env python3
"""Guard the second real A firing, independent jitter and B's learned entry."""
from pathlib import Path
import subprocess
import tempfile

from scripts.lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[2]
PREFIX = 'import KernelR.HybridSecondWiredArrival\nopen KernelR.Hybrid\n'


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
          CompleteThrough w.staged.after w.final.time ∧ w.final.pending.length=46 := by
  exact birth_protocol_second_wired_arrival_exists hs hb ha hq newborn forward backward hd
"""
    ctx = """example {{θ born fresh newborn forward backward}}
    {{c : ConstructedBirthPreparation θ born}}
    {{b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}}
    {{r : FirstWiredArrival b}} {{s : FirstInterleavedPair r}} (w : SecondWiredArrival s) """
    bounds = ctx + """(hd : ∀ t, (3/10:ℝ)≤forward t ∧ forward t≤2/5) :
    (168+7/10:ℝ)<w.final.time ∧ w.final.time<168+{value} := by exact w.date_bounds hd
"""
    firing_gap = ctx + """: w.fire.final.time = r.fire.final.time+{value} := by exact w.fire.firing_gap
"""
    gap = ctx + """(hd : ∀ t, (3/10:ℝ)≤forward t ∧ forward t≤2/5) :
    {lower}≤w.final.time-r.final.time ∧ w.final.time-r.final.time≤81/10 := by exact w.received_gap hd
"""
    date = ctx + """: w.final.time = w.fire.final.time+{value} := by exact w.date
"""
    raw = ctx + """: w.final.raw 1 1 = some {value} := by exact w.raw_receiver
"""
    pending = ctx + """: w.final.pending.length = {value} := by exact w.pending_length
"""
    issued = ctx + """: w.fire.final.pending.length = {value} := by exact w.fire.pending_length
"""
    deliveries = ctx + """: w.execution.deliveries = [⟨1,{port},w.final.time⟩] := by exact w.deliveries
"""
    outputs = ctx + """: w.execution.ledger.emissions = [⟨{cell},w.fire.final.time⟩] := by exact w.emissions
"""
    outcome = ctx + """{{ε}} (hb : @PhysicalBox 2 (extendParameters θ fresh) ε)
    (hd : ∀ t, (3/10:ℝ)≤forward t ∧ forward t≤2/5) """
    gain = outcome + """: w.final.x 1 (.z 1) = {base}+3/5 := by exact w.receiver_gain_target hb hd
"""
    gain_bound = outcome + """: 9/5≤Real.exp (w.final.x 1 (.z 1)) ∧ Real.exp (w.final.x 1 (.z 1))≤{upper} := by
  exact w.receiver_gain_bounds hb hd
"""
    recovery = ctx + """: w.final.x 1 .b = {value} := by exact w.receiver_recovery
"""
    main = ctx + """: w.final.main 1 = .{value} := by exact w.receiver_ready.ready
"""
    sender_raw = ctx + """: w.fire.final.raw 0 0 = some {value} := by exact w.fire.raw_active
"""
    other = ctx + """(p : Port) (hp : p≠1) : w.final.raw 1 p = {value} := by exact w.raw_receiver_other p hp
"""
    complete = ctx + """: CompleteThrough w.staged.after {value} := by exact w.staged_complete
"""
    before = ctx + """: w.fire.before.pending = {value} := by rw [w.fire.product_before]; rfl
"""
    same = """example {{n θ route s t i p}} (f : @FirstLearnedFire n θ route s i p)
    (g : FirstLearnedFire θ route t i p) (hs : s.x i .q=1/10) (ht : t.x i .q=1/10)
    (hz : s.x i (.z p)=t.x i (.z p)) : f.latency=g.latency {extra} := by
  exact f.latency_eq_of_rest_gain g hs ht hz
"""
    charge = ctx + """: w.fire.final.x 1 .q≤{value} := by exact w.fire.b_ready.charge.2
"""
    return [
        ('the original birth factory constructs the second real wire receipt', factory.format(count='16'), factory.format(count='15')),
        ('the second receipt keeps its actual response-plus-delay bounds', bounds.format(value='13/10'), bounds.format(value='1')),
        ('equal own rest roots make the actual A firings eight apart', firing_gap.format(value='8'), firing_gap.format(value='79/10')),
        ('received gaps retain fresh independent jitter', gap.format(lower='79/10'), gap.format(lower='8')),
        ('the new delay is sampled at the new actual FIRE', date.format(value='forward w.fire.final.time'), date.format(value='forward r.fire.final.time')),
        ('the new raw origin is the new receipt clock', raw.format(value='w.final.time'), raw.format(value='r.final.time')),
        ('both receipts retain the forty-six future external sources', pending.format(value='46'), pending.format(value='47')),
        ('the second real FIRE first appends one wire token', issued.format(value='47'), issued.format(value='46')),
        ('the second actual wire still targets B port1', deliveries.format(port='1'), deliveries.format(port='2')),
        ('only A emits in the second wire extension', outputs.format(cell='0'), outputs.format(cell='1')),
        ('the learned B entry keeps its own perturbed birth gain', gain.format(base='newborn.x (.z 1)'), gain.format(base='Real.log (6/5)')),
        ('the actual learned B gain uses its true2.2 cap', gain_bound.format(upper='11/5'), gain_bound.format(upper='2')),
        ('B recovery is still its own low newborn value', recovery.format(value='newborn.x .b'), recovery.format(value='9/50')),
        ('the second B wire arrives to a genuine READY entry', main.format(value='ready'), main.format(value='slow')),
        ('A retains source168 rather than the previous raw origin', sender_raw.format(value='168'), sender_raw.format(value='160')),
        ('no other receiver port gains a raw input', other.format(value='none'), other.format(value='some w.final.time')),
        ('saturation is after the actual receipt rather than its FIRE', complete.format(value='w.final.time'), complete.format(value='w.fire.final.time')),
        ('the pre-FIRE global queue excludes its unissued token', before.format(value='firstInterleavedPending'), before.format(value='firstInterleavedPending++[⟨1,1,w.final.time⟩]')),
        ('equal own root equations determine equal real latencies', same.format(extra=''), same.format(extra='+1/1000')),
        ('READY charge at FIRE is recovered from the real weak return', charge.format(value='7/50'), charge.format(value='1/10')),
    ]


def main():
    controls = cases()
    with tempfile.TemporaryDirectory(prefix='hybrid-second-wire-negative-', dir=ROOT) as tmp:
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

        check('\n'.join(good for _, good, _ in controls), True, 'valid second-wire controls')
        for name, _, bad in controls:
            check(bad, False, name)
            print(f'{name}: physical conclusion accepted; altered claim rejected.', flush=True)


if __name__ == '__main__':
    main()
