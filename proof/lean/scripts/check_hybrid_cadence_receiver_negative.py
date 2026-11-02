#!/usr/bin/env python3
"""Paired actual packet receivers and causally coupled B/C contracts."""
from pathlib import Path
import subprocess
import tempfile

from lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[1]
PREFIX = '''import KernelR.HybridConstructedCadenceBC
open KernelR.Hybrid
noncomputable section
'''


def pair(label, template, good, bad):
    assert '@v@' in template and good != bad
    return label, template.replace('@v@', good), template.replace('@v@', bad)


def strong_factory(gap):
    return f'''example {{θ ε}} (hb : PhysicalBox θ ε) (s : Snapshot 1) (p : Port)
    (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (hs : CadenceReadyCoordinates s 0 (3/10)) (hq : s.x 0 .q=1/10)
    (hz : Real.log (3/10)+9/5-1/100000≤s.x 0 (.z p) ∧
      s.x 0 (.z p)≤Real.log (3/10)+9/5+1/100000)
    (hB : 17999/100000≤s.x 0 .b ∧ s.x 0 .b≤18001/100000)
    (hr : s.raw 0 p=some s.time) (ho : ∀ q,q≠p→s.raw 0 q=none)
    (hqueue : s.pending=[⟨0,p,s.time+{gap}⟩]) :
    ∃ r : CadenceFirstStrongJitterNextSource θ s p (s.time+{gap}) [],
      r.final.time=s.time+@v@ ∧ r.final.main 0=.slow := by
  obtain ⟨r⟩ := cadence_first_strong_jitter_next_source_exists hb s p (s.time+{gap}) []
    hf hv hs hq hz hB hr ho hqueue (by constructor <;> linarith) (by simp)
  exact ⟨r,r.date,r.main_slow⟩
'''


def cases():
    rec = '''example {θ s p m L J} {packet : KernelR.Chain.Packet m L J} {T}
    (r : LocalCadenceReceiver θ s p packet T) '''
    bc = '''example {θ born freshB freshC newbornB newbornC forward backward delay cascadeForward cascadeBackward}
    {c : ConstructedCadenceFirstMarkReturn θ born freshB freshC newbornB newbornC
      forward backward delay cascadeForward cascadeBackward} (bc : ConstructedBCadence c) '''
    factory = '''example {θ born freshB freshC newbornB newbornC forward backward delay cascadeForward cascadeBackward ε}
    (c : ConstructedCadenceFirstMarkReturn θ born freshB freshC newbornB newbornC
      forward backward delay cascadeForward cascadeBackward)
    (hb : @PhysicalBox 3 (extendParameters (extendParameters θ freshB) freshC) ε)
    (hd : ∀ t,(3/10:ℝ)≤cascadeForward t ∧ cascadeForward t≤2/5) :
    ∃ bc : ConstructedBCadence c,
      bc.final.time=@v@ ∧ bc.final.pending=[] ∧
      CompleteThrough bc.execution (7899/10) ∧
      (bc.execution.emissionTimes 0).length=18 ∧ (bc.execution.emissionTimes 1).length=20 := by
  obtain ⟨bc⟩ := constructed_b_cadence_exists c hb hd
  exact ⟨bc,bc.date,bc.pending,bc.complete,bc.b_emission_count,bc.c_emission_count⟩
'''
    return [
        pair('receiver consumes every actual incoming token at its original date', rec +
             ''': r.execution.deliveries=List.ofFn (fun i : Fin (m+L) =>
    (⟨0,p,packet.actual @v@⟩ : Delivery 1)) := by exact r.deliveries
''', 'i.val', '(i.val+1)'),
        pair('receiver produces exactly the constructed output count', rec +
             ': (r.execution.emissionTimes 0).length=@v@ := by exact r.emission_count\n',
             'm+L-2', 'm+L-1'),
        pair('output packet is tied to the full actual FIRE ledger', rec +
             ''': r.execution.emissionTimes 0=List.ofFn (fun i : Fin ((m+2)+(L-4)) =>
    r.outputPacket.@v@ i.val) := by exact r.output_packet_calendar
''', 'actual', 'ideal'),
        pair('relay packet retains rather than resets the incoming phase errors', rec +
             '''(i : ℕ) : r.outputPacket.phase i=@v@ := by rfl
''', 'packet.phase (KernelR.Chain.relayIndex m i)', '0'),
        pair('relay packet keeps the same jitter budget and its exact prefix and tail sizes', rec +
             ''': KernelR.Chain.Packet (m+2) (L-4) @v@ := r.outputPacket
''', 'J', '0'),
        pair('the terminal receiver charge is the actual exact rest value', rec +
             ': r.final.x 0 .q=@v@ := by exact r.charge\n', '1/10', '1/4'),
        pair('the terminal receiver is physically READY', rec +
             ': r.final.main 0=.@v@ := by exact (r.ready 0).ready\n', 'ready', 'slow'),
        pair('no residual RAW clock remains at the terminal receiver', rec +
             '(q : Port) : r.final.raw 0 q=@v@ := by exact r.raw_none 0 q\n', 'none', 'some T'),
        pair('the receiver learns exactly its own additional ERROR dose', rec +
             ': r.final.x 0 (.z p)=s.x 0 (.z p)+@v@ := by exact r.gain_target\n', '3/5', '6/5'),
        pair('the two real MARK responses increment own recovery by two tenths', rec +
             ': r.final.x 0 .b=s.x 0 .b+@v@ := by exact r.recovery_gain\n', '1/5', '1/10'),
        pair('unaddressed port gains retain their own starting coordinate', rec +
             '(q : Port) (hq : q≠p) : r.final.x 0 (.z q)=s.x 0 (.z @v@) := by exact r.gain_other q hq\n',
             'q', 'p'),
        pair('first high latency retains the actual carried-charge threshold', rec +
             ': r.firstHighLatency=@v@ := by rfl\n', 'r.high.first.latency', 'r.restHighLatency'),
        pair('following high responses use the own exact-rest root rather than the first carried root', rec +
             ''': r.high.execution.emissionTimes 0=r.high.first.final.time ::
    (cadenceDates packet.actual (m+4) (L-4)).map (fun H => H+@v@) := by
  rw [r.high.calendar,r.high_gain_source]
  rfl
''', 'r.restHighLatency', 'r.firstHighLatency'),
        pair('three-dose rest latency uses the own original learned gain', rec +
             ': r.lowLatency=restLatency (Real.exp (s.x 0 (.z p)@v@)) := by rfl\n', '', '+3/5'),
        pair('high exact-rest latency uses the own gain after the mixed ERROR', rec +
             ': r.restHighLatency=highRestLatency (Real.exp (s.x 0 (.z p)@v@)) := by rfl\n', '+3/5', ''),
        pair('receiver terminal energy is the retained actual high path energy', rec +
             ': r.final.x 0 .energy=@v@ := by rfl\n', 'r.high.final.x 0 .energy', '100'),
        pair('the minimum received gap of3.8 has an actual strong-response constructor',
             strong_factory('19/5'), '19/5', '4'),
        pair('the first transition gap of4.3 has an actual strong-response constructor',
             strong_factory('43/10'), '43/10', '4'),
        pair('the coupled BC factory requires no supplied reaching execution', factory, '7899/10', '790'),
        pair('the coupled physical source starts at the actual teaching boundary', bc +
             ': bc.source.time=@v@ := by exact bc.source_date\n', '6399/10', '660'),
        pair('the shared initial queue contains only the twenty-five external C sources', bc +
             ': bc.source.pending=sourceTrain @v@ 0 640 4 25 := by exact bc.source_pending\n',
             '(1 : Fin 2)', '(0 : Fin 2)'),
        pair('the true coupled BC path has eighteen B and twenty C outputs', bc +
             ''': ((bc.execution.emissionTimes 0).length,(bc.execution.emissionTimes 1).length)=@v@ := by
  exact Prod.ext bc.b_emission_count bc.c_emission_count
''', '(18,20)', '(20,20)'),
        pair('twenty B input tokens are issued by actual coupled C FIREs', bc +
             ': (bc.execution.issuedTo 0).length=@v@ := by exact bc.issued_b_count\n', '20', '21'),
        pair('actual issued B tokens retain the complete received packet dates', bc +
             ''': bc.execution.issuedTo 0=List.ofFn (fun i : Fin 20 =>
    (⟨0,2,bc.bPacket.@v@ i.val⟩ : Delivery 2)) := by exact bc.issued_b_tokens
''', 'actual', 'ideal'),
        pair('each final learned gain retains the corresponding own newborn memory', bc +
             ''': (bc.final.x 0 (.z 2),bc.final.x 1 (.z 0))=
    (@v@+12/5,newbornC.x (.z 0)+12/5) := by
  exact Prod.ext bc.b_gain_target bc.c_gain_target
''', 'newbornB.x (.z 2)', 'newbornC.x (.z 2)'),
        pair('each final recovery retains the corresponding own newborn memory', bc +
             ''': (bc.final.x 0 .b,bc.final.x 1 .b)=(newbornB.x .b+3/10,@v@+3/10) := by
  exact Prod.ext bc.b_recovery bc.c_recovery
''', 'newbornC.x .b', 'newbornB.x .b'),
        pair('the two endpoint energies are the actual separately retained paths', bc +
             ''': (bc.final.x 0 .energy,bc.final.x 1 .energy)=@v@ := by
  exact Prod.ext bc.b_energy_actual bc.c_energy_actual
''', '(bc.bRun.final.x 0 .energy,bc.fullC.final.x 0 .energy)', '(100,100)'),
        pair('the coupled endpoint contains no leftover or preloaded wire token', bc +
             ': bc.final.pending=@v@ := by exact bc.pending\n', '[]', '[⟨0,2,7899/10⟩]'),
        pair('both coupled cells reach READY rest with every RAW clock absent', bc +
             ''': (∀ i,bc.final.main i=.@v@) ∧ (∀ i,bc.final.x i .q=1/10) ∧
    (∀ i q,bc.final.raw i q=none) := by
  exact ⟨fun i => (bc.ready i).ready,bc.charge,bc.raw_none⟩
''', 'ready', 'slow'),
        pair('the physical B output retains its exact5-plus13 packet shape', bc +
             ': KernelR.Chain.Packet 5 @v@ (1/20) := bc.outputPacket\n', '13', '14'),
    ]


def main():
    controls = cases()
    assert len(controls) == 30
    with tempfile.TemporaryDirectory(prefix='hybrid-cadence-receiver-', dir=ROOT) as tmp:
        path = Path(tmp) / 'Check.lean'
        command = lean_check_command(tmp)

        def check(source, expected, name):
            path.write_text(PREFIX + source)
            result = subprocess.run([*command, str(path)], cwd=ROOT, text=True,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=240)
            if (result.returncode == 0) != expected:
                raise SystemExit(f'{name}: unexpected result:\n{result.stdout}')
            if not expected and 'error:' not in result.stdout:
                raise SystemExit(f'{name}: failed without a Lean diagnostic:\n{result.stdout}')

        check('\n'.join(good for _, good, _ in controls), True, 'all positive actual receiver and coupled BC contracts')
        print('All30 positive actual receiver and coupled BC contracts accepted.', flush=True)
        for name, _, bad in controls:
            check(bad, False, name)
            print(f'{name}: physical conclusion accepted; altered claim rejected.', flush=True)
        print(f'{len(controls)} paired actual receiver and coupled BC controls passed.', flush=True)


if __name__ == '__main__':
    main()
