#!/usr/bin/env python3
"""Guard actual weak-source iteration and the first constructed birth firing."""
from pathlib import Path
import subprocess
import tempfile

from lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[1]
PREFIX = '''import KernelR.HybridBirthFirstFire
open KernelR.Hybrid
'''


def cases():
    contract = """example {{θ ε born}}
    (hs : @BirthState 1 born) (hb : PhysicalBox θ ε)
    (ha : ∀ p, born.aux 0 p = .ready)
    (hq : born.pending = sourceTrain 0 0 0 8 {count} ++ sourceTrain 0 0 160 8 16) :
    ∃ c : BirthFirstFire θ (fun _ _ => []) born, CompleteThrough c.execution c.final.time := by
  exact birth_protocol_first_fire_complete_exists hs hb ha hq
"""
    weak = """example {{θ route born}} (w : BirthWeakPrefix θ route born) """
    first = """example {{θ route born}} (c : BirthFirstFire θ route born) """
    strict = first + """(hr : ∀ d ∈ route 0 c.final.time, c.final.time {cmp} d.due) :
    CompleteThrough c.execution c.final.time := by
  exact c.complete hr
"""
    date = weak + """: w.final.time = {value} := by exact w.date
"""
    dose = weak + """: w.execution.ledger.error 0 0 = {value} := by exact w.error_dose
"""
    delivered = weak + """: w.execution.deliveries = sourceTrain 0 0 0 8 {count} := by exact w.deliveries
"""
    pending = weak + """: w.final.pending = sourceTrain 0 0 32 8 {count} ++ sourceTrain 0 0 160 8 16 := by
  exact w.pending
"""
    raw = weak + """: w.final.raw 0 0 = {value} := by exact w.raw_active
"""
    ready = weak + """: w.final.main 0 = .{mode} := by exact (w.ready 0).ready
"""
    waiting = """example {{n θ route s d later}} (a : @QuietSourceArrival n θ route s d later) :
    a.final.x = {value} := by exact a.values
"""
    margin = """example {{initial amplitude start t : ℝ}} (hi : initial ≤ 7/50)
    (hg : amplitude ≤ {gain}) (ht : start ≤ t) : readyPulse initial amplitude start t ≤ 24/25 := by
  exact readyPulse_weak_input_error_margin hi hg ht
"""
    horizon = """example {{n θ route s i p}} (w : @WeakInputCycle n θ route s i p) :
    w.final.time = {value} := by exact w.date
"""
    firing_date = first + """: 243/10 < c.final.time ∧ c.final.time < {upper} := by exact c.date_bounds
"""
    output = first + """: c.execution.ledger.emissions = {value} := by exact c.emissions
"""
    fast = first + """: c.final.main 0 = .{mode} := by exact c.fire.main_fast
"""
    charge = first + """: c.final.x 0 .q = {value} := by exact c.fire.charge
"""
    routed = first + """: c.final.pending =
    (sourceTrain 0 0 32 8 12 ++ sourceTrain 0 0 160 8 16) {extra} := by exact c.pending
"""
    raw_origin = first + """: c.final.raw 0 0 = some {origin} := by
  have hr : c.final.raw 0 0 = some c.weak.final.time := c.fire.raw_active
  rw [c.weak.date] at hr
  exact hr
"""
    firing_error = first + """: c.execution.ledger.error 0 0 = {value} := by exact c.error_dose
"""
    recovery = first + """: c.final.x 0 .b = born.x 0 .b {extra} := by exact c.recovery
"""
    tail = """example {{n θ route s d later}} (a : @QuietSourceArrival n θ route s d later) :
    a.final.pending = {value} := by exact a.pending
"""
    return [
        ('the complete birth-to-first-fire factory retains the full source queue', contract.format(count='16'), contract.format(count='15')),
        ('saturation after FIRE requires strictly future routed tokens', strict.format(cmp='<'), strict.format(cmp='≤')),
        ('three weak cycles reach the fresh fourth source at twenty-four', date.format(value='24'), date.format(value='16')),
        ('four delivered sources contain only three completed ERROR cycles', dose.format(value='9/5'), dose.format(value='12/5')),
        ('all four actual input occurrences are delivered', delivered.format(count='4'), delivered.format(count='3')),
        ('all twenty-eight future source tokens remain before FIRE', pending.format(count='12'), pending.format(count='13')),
        ('the fourth input remains a fresh raw pulse', raw.format(value='some w.final.time'), raw.format(value='none')),
        ('the cell is still READY at the fourth delivery', ready.format(mode='ready'), ready.format(mode='fast')),
        ('waiting carries the actual relaxed residual coordinates', waiting.format(value='quietValues s d.due'), waiting.format(value='s.x')),
        ('the weak-input margin retains its justified gain bound', margin.format(gain='7/6'), margin.format(gain='4/3')),
        ('weak-cycle horizons move with the actual source origin', horizon.format(value='s.time+15/2'), horizon.format(value='15/2')),
        ('the first firing retains its physically constructed deadline', firing_date.format(upper='249/10'), firing_date.format(upper='243/10')),
        ('the complete constructed prefix has one actual emission', output.format(value='[(0,c.final.time)]'), output.format(value='[]')),
        ('the first main firing really enters FAST', fast.format(mode='fast'), fast.format(mode='ready')),
        ('the first main firing occurs at charge one', charge.format(value='1'), charge.format(value='1/4')),
        ('FIRE retains every issued route token', routed.format(extra='++ route 0 c.final.time'), routed.format(extra='')),
        ('FIRE retains the original input origin', raw_origin.format(origin='24'), raw_origin.format(origin='c.final.time')),
        ('the first output does not add a fourth ERROR dose', firing_error.format(value='9/5'), firing_error.format(value='12/5')),
        ('the first output retains its own birth recovery', recovery.format(extra=''), recovery.format(extra='+1/10')),
        ('the waiting arrival removes exactly its head source', tail.format(value='later'), tail.format(value='[]')),
    ]


def main():
    controls = cases()
    with tempfile.TemporaryDirectory(prefix='hybrid-first-fire-negative-', dir=ROOT) as tmp:
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

        check('\n'.join(good for _,good,_ in controls), True, 'valid source-to-first-fire controls')
        for name,_,bad in controls:
            check(bad, False, name)
            print(f'{name}: physical conclusion accepted; altered claim rejected.', flush=True)


if __name__ == '__main__':
    main()
