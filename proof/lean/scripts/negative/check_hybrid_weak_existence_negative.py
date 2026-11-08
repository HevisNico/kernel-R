#!/usr/bin/env python3
"""Guard the constructed complete first weak cycle and exact ERROR restarts."""
from pathlib import Path
import subprocess
import tempfile

from scripts.lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[2]
PREFIX = '''import KernelR.HybridBirthFirstWeakCycle
open KernelR.Hybrid
'''


def cases():
    contract = """example {{θ ε route born}}
    (hs : @BirthState 1 born) (hb : PhysicalBox θ ε)
    (ha : ∀ p, born.aux 0 p = .ready)
    (hq : born.pending = sourceTrain 0 0 0 8 {count} ++ sourceTrain 0 0 160 8 16) :
    Nonempty (BirthFirstWeakCycle θ route born) := by
  exact birth_protocol_first_weak_cycle_exists hs hb ha hq
"""
    context = """example {{θ route born}} (c : BirthFirstWeakCycle θ route born) """
    date = context + """: c.final.time = {value} := by
  exact c.date
"""
    complete = context + """: CompleteThrough c.execution ({value}) := by
  exact c.complete
"""
    deliveries = context + """: c.execution.deliveries = [⟨0,0,{value}⟩] := by
  exact c.deliveries
"""
    outputs = context + """: c.execution.ledger.emissions = {value} := by
  exact c.emissions
"""
    dose = context + """: c.execution.ledger.error 0 0 = {value} := by
  exact c.error_dose
"""
    mark = context + """: c.execution.ledger.mark 0 0 = {value} := by
  exact c.mark_zero 0
"""
    gain = context + """: c.final.x 0 (.z 0) = born.x 0 (.z 0)+{value} := by
  have hg := c.gain_target
  linarith
"""
    recovery = context + """: c.final.x 0 .b = born.x 0 .b {extra} := by
  exact c.recovery_preserved
"""
    queue = context + """: c.final.pending = {value} := by
  exact c.pending
"""
    raw = context + """(p : Port) : c.final.raw 0 p = {value} := by
  exact c.pulse.raw_finished p
"""
    main = context + """: c.final.main 0 = .{value} := by
  exact c.pulse.coordinates.ready
"""
    auxiliary = context + """(p : Port) : c.final.aux 0 p = .{value} := by
  exact (c.pulse.coordinates.auxiliary p).1
"""
    remaining = """example {{n θ route s i p}} (c : @ErrorCompletion n θ route s i p) :
    c.execution.ledger.error i p = {value} := by
  exact c.error_dose
"""
    cut = """example {{n θ}} (s : Snapshot n) (i : Fin n) (p : Port)
    (raw : Option ℝ) (cut : ℝ) (hr : (θ i).le p ≠ 0) (hm : 0 < s.x i (.m p)) :
    let v := setRaw (errorTailEnd θ s i p raw cut) i p none
    v.time+errorTailDuration θ v i p = s.time+errorTailDuration θ s i p {extra} := by
  exact errorTail_cut_time s i p raw cut hr hm
"""
    work = """example {{n θ}} (s : Snapshot n) (i : Fin n) (p : Port) (raw : Option ℝ) (t : ℝ) :
    errorTailWork θ s i p raw t = {factor}*(θ i).le p*errorTailSensor θ s i p t +
      errorTailDrive θ s i p raw t := by
  rfl
"""
    return [
        ('the complete weak factory uses all original source occurrences', contract.format(count='16'), contract.format(count='15')),
        ('the constructed quiet horizon is before the next arrival', date.format(value='15/2'), date.format(value='8')),
        ('the full actual birth execution is saturated at its own horizon', complete.format(value='15/2'), complete.format(value='8')),
        ('exactly the real source-zero token is delivered', deliveries.format(value='0'), deliveries.format(value='8')),
        ('the constructed full weak cycle emits nothing', outputs.format(value='[]'), outputs.format(value='[(0,1)]')),
        ('the first actual cycle gives one ERROR dose rather than two', dose.format(value='3/5'), dose.format(value='6/5')),
        ('READY-main MARK has no protected recovery dose', mark.format(value='0'), mark.format(value='1/10')),
        ('own birth gain receives exactly one learning dose', gain.format(value='3/5'), gain.format(value='6/5')),
        ('own birth recovery survives the weak cycle', recovery.format(extra=''), recovery.format(extra='+1/10')),
        ('the two future source trains remain exactly queued', queue.format(value='sourceTrain 0 0 8 8 15 ++ sourceTrain 0 0 160 8 16'), queue.format(value='[]')),
        ('the full weak cycle completes the raw pulse', raw.format(value='none'), raw.format(value='some 0')),
        ('the main cell really returns READY', main.format(value='ready'), main.format(value='slow')),
        ('every auxiliary really returns READY', auxiliary.format(value='ready'), auxiliary.format(value='error')),
        ('an ERROR suffix retains its actual remaining dose', remaining.format(value='8*(s.x i (.m p)-1/40)'), remaining.format(value='3/5')),
        ('raw-expiry cuts preserve the original ERROR deadline', cut.format(extra=''), cut.format(extra='+3/20')),
        ('ERROR energy includes both auxiliary drain and learning work', work.format(factor='9'), work.format(factor='8')),
    ]


def main():
    controls = cases()
    with tempfile.TemporaryDirectory(prefix='hybrid-weak-existence-negative-', dir=ROOT) as tmp:
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

        check('\n'.join(good for _,good,_ in controls), True, 'valid complete weak-existence controls')
        for name,_,bad in controls:
            check(bad, False, name)
            print(f'{name}: physical conclusion accepted; altered claim rejected.', flush=True)


if __name__ == '__main__':
    main()
