#!/usr/bin/env python3
"""Paired full-budget physical packet receiver contracts."""
from pathlib import Path
import subprocess
import tempfile

from lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[1]
PREFIX = '''import KernelR.HybridLocalCadenceBudgetReceiverPacket
open KernelR.Hybrid
noncomputable section
'''


def pair(label, template, good, bad):
    assert '@v@' in template and good != bad
    return label, template.replace('@v@', good), template.replace('@v@', bad)


def cases():
    rec = '''example {θ s p m L J} {packet : KernelR.Chain.Packet m L J} {T}
    (r : LocalCadenceBudgetReceiver θ s p packet T) '''
    factory = '''example {θ ε} (hb : PhysicalBox θ ε) (s : Snapshot 1) (p : Port)
    (packet : KernelR.Chain.Packet 1 5 (3/20))
    (hf : PhysicalInvariant θ s) (hv : RawValid s) (hs : PreparedSection s 0)
    (hq : s.x 0 .q=1/10) (hr : ∀ q,s.raw 0 q=none)
    (hz : Real.log (3/10)+9/5-1/100000≤s.x 0 (.z p) ∧
      s.x 0 (.z p)≤Real.log (3/10)+9/5+1/100000)
    (hqueue : s.pending=List.ofFn (fun i : Fin 6 => (⟨0,p,packet.actual i.val⟩ : Delivery 1)))
    (hfirst : s.time<packet.actual 0) :
    ∃ r : LocalCadenceBudgetReceiver θ s p packet (packet.actual 5+37/10),
      (r.execution.emissionTimes 0).length=@v@ ∧ CompleteThrough r.execution (packet.actual 5+37/10) := by
  obtain ⟨r⟩ := local_cadence_budget_receiver_exists hb s p packet (packet.actual 5+37/10)
    (by norm_num) (by norm_num) hf hv hs hq hr hz hqueue hfirst (by norm_num)
  exact ⟨r,r.emission_count,r.complete⟩
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
        pair('actual receiver factory constructs the smallest full-budget packet at J=.15',
             factory, '4', '5'),
        pair('full-budget receiver retains its explicit permitted jitter budget', rec +
             ': J≤@v@ := by exact r.jitter_bound\n', '3/20', '1/10'),
        pair('actual receiver endpoint is complete at its chosen terminal date', rec +
             ': CompleteThrough r.execution @v@ := by exact r.complete\n', 'T', 'packet.actual 0'),
    ]


def main():
    controls = cases()
    assert len(controls) == 19
    with tempfile.TemporaryDirectory(prefix='hybrid-cadence-budget-receiver-', dir=ROOT) as tmp:
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

        check('\n'.join(good for _, good, _ in controls), True, 'all positive full-budget receiver contracts')
        print('All19 positive full-budget receiver contracts accepted.', flush=True)
        for name, _, bad in controls:
            check(bad, False, name)
            print(f'{name}: physical conclusion accepted; altered claim rejected.', flush=True)
        print(f'{len(controls)} paired full-budget receiver controls passed.', flush=True)


if __name__ == '__main__':
    main()
