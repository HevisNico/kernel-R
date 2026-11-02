#!/usr/bin/env python3
"""Actual independently jittered high-source contracts, including port2."""
from pathlib import Path
import subprocess
import tempfile
from lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[1]
PREFIX = '''import KernelR.HybridLocalCadenceHighJitterTrain
open KernelR.Hybrid
noncomputable section
'''


def pair(name, template, good, bad):
    assert '@v@' in template and good != bad
    return name, template.replace('@v@', good), template.replace('@v@', bad)


def cases():
    ready = '''example {θ s p H future} (r : CadenceHighJitterReadyAt θ s p H future) '''
    entry = '''example {θ s p H later} (r : CadenceHighJitterNextSource θ s p H later) '''
    train = '''example {θ s p dates T} (t : LocalCadenceHighJitterTrain θ s p dates T) '''
    return [
        pair('ready endpoint uses the requested actual date', ready+
             ': r.final.time=@v@ := by exact r.date\n', 'H', 's.time+4'),
        pair('ready endpoint retains the exact framed future queue', ready+
             ': r.final.pending=@v@ := by exact r.pending\n', 'future', '[]'),
        pair('framing retains the actual complete physical ledger', ready+
             ': r.execution.ledger=@v@ := by exact r.framed_ledger\n', 'r.offline.ledger', 'Ledger.zero'),
        pair('ready endpoint energy is the genuine quiet continuation energy', ready+
             ''': r.final.x 0 .energy=@v@ := by
  simpa only [appendPending] using congrArg (fun u : Snapshot 1 => u.x 0 .energy) r.final_state
''', '(quietAt r.completion.returned.returnState H).x 0 .energy', '100'),
        pair('jittered high response emits one actual FIRE', entry+
             ': r.execution.ledger.emissions=@v@ := by exact r.emissions\n', '[(0,r.readyAt.fire.final.time)]', '[]'),
        pair('actual arrival consumes the generic destination port', entry+
             ': r.execution.deliveries=[⟨0,@v@,H⟩] := by exact r.deliveries\n', 'p', '0'),
        pair('actual arrival RAW origin is its delivery date', entry+
             ': r.final.raw 0 p=some (@v@) := by exact r.raw_active\n', 'H', 's.time'),
        pair('next source inherits the exact reopened rest charge', entry+
             ': r.final.x 0 .q=@v@ := by exact r.charge\n', '1/10', '8/25'),
        pair('next source preserves each own gain memory', entry+
             '(q : Port) : r.final.x 0 (.z q)=s.x 0 (.z q)@v@ := by exact r.gains 0 q\n', '', '+3/5'),
        pair('next source preserves the carried recovery memory', entry+
             ': r.final.x 0 .b=s.x 0 .b@v@ := by exact r.recovery 0\n', '', '+1/10'),
        pair('train counts its active source plus actual queued dates', train+
             ': (t.execution.emissionTimes 0).length=@v@ := by exact t.emission_count\n', 'dates.length+1', 'dates.length'),
        pair('train first FIRE retains its actual carried latency', train+
             ''': t.execution.emissionTimes 0=(@v@) ::
      dates.map (fun H => H+highRestLatency (Real.exp (s.x 0 (.z p)))) := by exact t.calendar
''', 't.first.final.time', 's.time+highRestLatency (Real.exp (s.x 0 (.z p)))'),
        pair('later jittered FIREs use the same own rest root', train+
             ''': t.execution.emissionTimes 0=t.first.final.time ::
      dates.map (fun H => H+@v@) := by exact t.calendar
''', 'highRestLatency (Real.exp (s.x 0 (.z p)))', 't.first.latency'),
        pair('train deliveries preserve input occurrence order', train+
             ': t.execution.deliveries=(@v@).map (fun H => (⟨0,p,H⟩ : Delivery 1)) := by exact t.deliveries\n', 'dates', 'dates.reverse'),
        pair('train reaches its requested complete terminal horizon', train+
             ': CompleteThrough t.execution (@v@) := by exact t.complete\n', 'T', 'T+1'),
        pair('minimum gap is three point eight rather than a four-unit grid',
             '''example {S dates T} (h : CadenceHighJitterSchedule S dates T) :
    ∀ H∈dates, S+@v@≤H := by exact h.source_lower
''', '19/5', '4'),
        factory_case(),
    ]


def factory_case():
    return pair('port2 factory constructs a real next source already at gap3point8',
        '''example {θ ε} (hb : PhysicalBox θ ε) (s : Snapshot 1)
    (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (hs : CadenceReadyCoordinates s 0 (8/25)) (hq : 1/10≤s.x 0 .q)
    (hg : 16/5≤Real.exp (s.x 0 (.z 2)) ∧ Real.exp (s.x 0 (.z 2))≤7/2)
    (hB : 37999/100000≤s.x 0 .b ∧ s.x 0 .b≤38001/100000)
    (hr : s.raw 0 2=some s.time) (ho : ∀q, q≠2 → s.raw 0 q=none)
    (hqueue : s.pending=[⟨0,2,s.time+19/5⟩]) :
    ∃ r : CadenceHighJitterNextSource θ s 2 (s.time+19/5) [],
      r.final.time=s.time+@v@ ∧ r.final.pending=[] ∧
      r.execution.deliveries=[⟨0,2,s.time+19/5⟩] := by
  obtain ⟨r⟩ := cadence_high_jitter_next_source_exists hb s 2 (s.time+19/5) []
    hf hv hs hq hg hB hr ho hqueue le_rfl (by simp)
  exact ⟨r,r.date,r.pending,r.deliveries⟩
''', '19/5', '4')


def main():
    controls = cases()
    assert len(controls) == 17
    with tempfile.TemporaryDirectory(prefix='hybrid-high-jitter-', dir=ROOT) as tmp:
        path = Path(tmp)/'Check.lean'
        command = lean_check_command(tmp)
        def check(source, expected, name):
            path.write_text(PREFIX+source)
            result = subprocess.run([*command, str(path)], cwd=ROOT, text=True,
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=180)
            if (result.returncode == 0) != expected:
                raise SystemExit(f'{name}: unexpected result:\n{result.stdout}')
            if not expected and not any(m in result.stdout for m in ('error:', 'error(')):
                raise SystemExit(f'{name}: failed without a Lean diagnostic:\n{result.stdout}')
        check('\n'.join(good for _,good,_ in controls), True, 'valid high jitter controls')
        print(f'All {len(controls)} positive high jitter contracts accepted.', flush=True)
        for name,_,bad in controls:
            check(bad, False, name)
            print(f'{name}: physical conclusion accepted; altered claim rejected.', flush=True)
        print(f'{len(controls)} paired high jitter controls passed.', flush=True)


if __name__ == '__main__':
    main()
