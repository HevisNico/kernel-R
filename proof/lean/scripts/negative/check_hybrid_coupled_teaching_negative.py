#!/usr/bin/env python3
"""Guard the constructed coupled train, original birth witness and issued contacts."""
from pathlib import Path
import subprocess
import tempfile

from scripts.lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[2]
PREFIX = 'import KernelR.HybridFirstCoupledTeaching\nopen KernelR.Hybrid\n'


def cases():
    cycle = '''example {θ fresh forward backward source}
    (k : CoupledLearnedCycle θ fresh forward backward source) '''
    train = '''example {θ fresh forward backward source count later}
    (k : CoupledLearnedTrain θ fresh forward backward source count later) '''
    ctx = '''example {θ born fresh newborn forward backward}
    {c : ConstructedBirthPreparation θ born}
    {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
    {r : FirstWiredArrival b} {s : FirstInterleavedPair r} {w : SecondWiredArrival s}
    {f : FirstReceiverFire w} {g : FirstReceiverFastEnd f} {v : FirstPostReceiverPair g}
    {t : ThirdWiredArrival v} {x : FirstCoupledPreparedPair t}
    (z : FirstCoupledTeaching x) '''
    hb_old = '{ε} (hb : PhysicalBox θ ε) '
    hb_new = '{ε} (hb : @PhysicalBox 2 (extendParameters θ fresh) ε) '
    delay = '(hd : ∀ time, (3/10:ℝ)≤forward time ∧ forward time≤2/5) '

    factory = '''example {θ fresh ε born} (hs : @BirthState 1 born)
    (hb : @PhysicalBox 2 (extendParameters θ fresh) ε)
    (ha : ∀ p, born.aux 0 p = .ready)
    (hq : born.pending = sourceTrain 0 0 0 8 16 ++ sourceTrain 0 0 160 8 16)
    (newborn : Newborn) (forward backward : ℝ → ℝ)
    (hd : ∀ time, (3/10:ℝ)≤forward time ∧ forward time≤2/5) :
    ∃ c : ConstructedBirthPreparation θ born,
      ∃ b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources,
        ∃ r : FirstWiredArrival b, ∃ s : FirstInterleavedPair r, ∃ w : SecondWiredArrival s,
          ∃ f : FirstReceiverFire w, ∃ g : FirstReceiverFastEnd f, ∃ v : FirstPostReceiverPair g,
            ∃ t : ThirdWiredArrival v, ∃ x : FirstCoupledPreparedPair t, ∃ z : FirstCoupledTeaching x,
              CompleteThrough z.staged.after (3199/10) ∧ z.final.pending.length=32 ∧
                (z.staged.before.emissionTimes 0 ++ z.staged.after.emissionTimes 0).length=@v@ ∧
                (z.staged.after.emissionTimes 1).length=14 := by
  exact birth_protocol_first_coupled_teaching_exists hs hb ha hq newborn forward backward hd
'''
    cycle_factory = '''example {θ fresh ε}
    (hb : @PhysicalBox 2 (extendParameters θ fresh) ε) (source : Snapshot 2)
    (hf : PhysicalInvariant (extendParameters θ fresh) source) (hv : RawValid source)
    (ht : 184≤source.time ∧ source.time≤280)
    (hs : ∀ i, PreparedSection source i) (hq : ∀ i, source.x i .q=1/10)
    (hGA : 9/5≤Real.exp (source.x 0 (.z 0)) ∧ Real.exp (source.x 0 (.z 0))≤2)
    (hGB : 9/5≤Real.exp (source.x 1 (.z 1)) ∧ Real.exp (source.x 1 (.z 1))≤11/5)
    (hr : source.raw 0 0=some source.time)
    (ho : ∀ i p, i≠0 ∨ p≠0 → source.raw i p=none)
    (hp : ∀ d∈source.pending, source.time+8≤d.due)
    (forward backward : ℝ → ℝ)
    (hd : ∀ time, (3/10:ℝ)≤forward time ∧ forward time≤2/5) :
    ∃ k : CoupledLearnedCycle θ fresh forward backward source,
      k.final.time=source.time+@v@ := by
  obtain ⟨k⟩ := coupled_learned_cycle_exists hb source hf hv ht hs hq hGA hGB hr ho hp forward backward hd
  exact ⟨k,k.date⟩
'''
    window = cycle + ': (184:ℝ)≤source.time ∧ source.time≤@v@ := by exact k.source_window\n'
    outputs = cycle + ''': k.execution.ledger.emissions=@v@ := by exact k.emissions
'''
    receipt = cycle + ''': k.execution.deliveries=[⟨1,@v@,k.cutH.state.time⟩] := by exact k.deliveries
'''
    wire = cycle + ''': k.wireTime=k.fireA+forward @v@ := by exact k.wire_date
'''
    queue = cycle + ''': k.final.pending=@v@ := by exact k.pending
'''
    strict = cycle + '''(hstrict : ∀ d∈source.pending, source.time+8<d.due) :
    CompleteThrough k.execution (source.time+@v@) := by exact k.complete hstrict
'''
    train_counts = train + ''': (k.execution.emissionTimes 0).length=@v@ ∧
    (k.execution.emissionTimes 1).length=count+1 := by
  exact ⟨k.a_emission_count,k.b_emission_count⟩
'''
    suffix_counts = ctx + ''': (z.execution.emissionTimes 0).length=@v@ ∧
    (z.execution.emissionTimes 1).length=13 := by
  exact ⟨z.a_emission_count,z.b_emission_count⟩
'''
    external = train + ''': k.execution.cellDeliveries 0=sourceTrain 0 0 (@v@) 8 count := by
  exact k.a_deliveries
'''
    incoming = train + ''': k.execution.cellDeliveries 1=
    k.wireTimes.map (fun time => (⟨1,@v@,time⟩ : Delivery 2)) := by exact k.b_deliveries
'''
    provenance = train + '''(time : ℝ) (ht : time∈k.wireTimes) :
    ∃ F∈k.execution.emissionTimes 0, time=F+forward @v@ := by exact k.wire_provenance time ht
'''
    tail = train + ''': k.final.pending=@v@ := by exact k.pending
'''
    error = train + '''(i : Fin 2) (p : Port) : k.execution.ledger.error i p=@v@ := by
  exact k.error_zero i p
'''
    mark = train + '''(i : Fin 2) (p : Port) : k.execution.ledger.mark i p=@v@ := by
  exact k.mark_zero i p
'''
    ready = ctx + ''': ∀ i, z.final.main i=.@v@ := by
  intro i
  exact (z.prepared i).ready
'''
    charge = ctx + ''': ∀ i, z.final.x i .q=@v@ := by exact z.charge
'''
    raw = ctx + ''': ∀ i p, z.final.raw i p=@v@ := by exact z.raw_none
'''
    pending = ctx + ''': z.final.pending=sourceTrain 1 @v@ 320 8 16 ++ sourceTrain 1 2 480 8 16 := by
  exact z.pending
'''
    pending_count = ctx + ''': z.final.pending.length=@v@ := by exact z.pending_length
'''
    terminal = ctx + ''': z.final.time=@v@ ∧ CompleteThrough z.staged.after (@v@) := by
  exact ⟨z.date,z.staged_complete⟩
'''
    gain_a = ctx + hb_old + ''': z.final.x 0 (.z 0)=@v@+9/5 := by
  exact z.a_gain_target hb
'''
    gain_b = ctx + hb_new + delay + ''': z.final.x 1 (.z 1)=@v@+3/5 := by
  exact z.b_gain_target hb hd
'''
    recovery_a = ctx + hb_old + ''': z.final.x 0 .b=born.x 0 .b+@v@ := by
  exact z.a_recovery_own hb
'''
    recovery_b = ctx + ''': z.final.x 1 .b=newborn.x .b+@v@ := by exact z.b_recovery_own
'''
    other = ctx + hb_old + '''(p q : Port) (hp : p≠0) (hq : q≠1) :
    z.final.x 0 (.z p)=born.x 0 (.z p) ∧ z.final.x 1 (.z q)=newborn.x (.z q)@v@ := by
  exact ⟨z.a_gain_other hb p hp,z.b_gain_other q hq⟩
'''
    staged_counts = ctx + ''': (z.staged.after.emissionTimes 0).length=16 ∧
    (z.staged.after.emissionTimes 1).length=@v@ := by exact ⟨z.staged_a_count,z.staged_b_count⟩
'''
    before = ctx + hb_old + ''': (z.staged.before.emissionTimes 0).length=@v@ := by
  exact x.before_birth_a_count hb
'''
    staged_external = ctx + ''': z.staged.after.cellDeliveries 0=sourceTrain 0 0 160 8 @v@ := by
  exact z.staged_a_deliveries
'''

    def pair(label, template, good, bad):
        assert template.count('@v@') >= 1
        return label, template.replace('@v@', good), template.replace('@v@', bad)

    return [
        pair('original BirthState and32 sources construct319.9 with Q32 and cumulative A28/B14', factory, '28', '27'),
        pair('generic coupled cycle constructs its true period-eight endpoint', cycle_factory, '8', '15/2'),
        pair('actual coupled source retains the physical forward-contact window', window, '280', '279'),
        pair('two actual global FIRE outputs remain in A then B order', outputs, '[(0,k.senderFire.final.time),(1,k.receiverCycle.fire.final.time)]', '[(0,k.senderFire.final.time)]'),
        pair('only the actual Bport1 wire is delivered inside one cycle', receipt, '1', '2'),
        pair('fresh wire delay is evaluated at the actual A FIRE clock', wire, 'k.fireA', 'source.time'),
        pair('the consumed actual wire leaves the original global queue unchanged', queue, 'source.pending', 'source.pending++[⟨1,1,k.wireTime⟩]'),
        pair('cycle saturation uses strict future queue at its exact terminal time', strict, '8', '16'),
        pair('n future external sources plus active RAW give nplus1 constructed outputs on each cell', train_counts, 'count+1', 'count'),
        pair('the teaching suffix constructs13 actual outputs on each cell', suffix_counts, '13', '12'),
        pair('external A delivery calendar starts at Splus8 and does not redeliver active RAW', external, 'source.time+8', 'source.time'),
        pair('every actual received wire targets Bport1 rather than Bport2', incoming, '1', '2'),
        pair('wire provenance selects an actual own A FIRE and its independently sampled delay', provenance, 'F', 'source.time'),
        pair('train endpoint retains exact later queue without shadowing the initial source queue', tail, 'later', 'source.pending'),
        pair('the learned train suffix contributes zero ERROR on all actual ports', error, '0', '3/5'),
        pair('the learned train suffix contributes zero MARK on all actual ports', mark, '0', '1/10'),
        pair('both cells genuinely end READY rather than SLOW at319.9', ready, 'ready', 'slow'),
        pair('both own terminal charges are exact resting one tenth', charge, '1/10', '1/4'),
        pair('all actual RAW origins have expired before319.9', raw, 'none', 'some (184:ℝ)'),
        pair('both original Bport2 source trains320 and480 remain with multiplicity16 each', pending, '2', '1'),
        pair('terminal global queue contains exactly32 retained B external sources', pending_count, '32', '31'),
        pair('terminal saturation is319.9 and does not silently consume source320', terminal, '3199/10', '320'),
        pair('A gain retains its own birth perturbation plus three ERROR doses', gain_a, 'born.x 0 (.z 0)', 'Real.log (3/10)'),
        pair('B gain retains its own independent newborn perturbation plus one ERROR dose', gain_b, 'newborn.x (.z 1)', 'Real.log (6/5)'),
        pair('A recovery keeps its own birth value plus its protected MARK', recovery_a, '1/10', '0'),
        pair('B recovery keeps its independent newborn value plus one protected MARK', recovery_b, '1/10', '1/5'),
        pair('both cells preserve their own other-port gains without inherited learning', other, '', '+3/5'),
        pair('postbirth counts are A16 and B14 before adding the prebirth preparation', staged_counts, '14', '13'),
        pair('prebirth A preparation contributes twelve outputs without an output-count premise', before, '12', '11'),
        pair('postbirth actual A arrivals consume all sixteen queued160through280 sources', staged_external, '16', '15'),
    ]


def main():
    controls = cases()
    with tempfile.TemporaryDirectory(prefix='hybrid-coupled-teaching-negative-', dir=ROOT) as tmp:
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

        check('\n'.join(good for _, good, _ in controls), True, 'valid coupled teaching controls')
        for name, _, bad in controls:
            check(bad, False, name)
            print(f'{name}: physical conclusion accepted; altered claim rejected.', flush=True)


if __name__ == '__main__':
    main()
