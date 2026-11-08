#!/usr/bin/env python3
"""Guard constructed FAST/SLOW continuation and the real protected MARK at32."""
from pathlib import Path
import subprocess
import tempfile

from scripts.lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[2]
PREFIX = '''import KernelR.HybridBirthProtectedMark
open KernelR.Hybrid
'''


def cases():
    contract = """example {{θ ε born}} (hs : @BirthState 1 born) (hb : PhysicalBox θ ε)
    (ha : ∀ p, born.aux 0 p = .ready)
    (hq : born.pending = sourceTrain 0 0 0 8 {count} ++ sourceTrain 0 0 160 8 16) :
    ∃ c : BirthProtectedMark θ born, CompleteThrough c.execution c.final.time := by
  obtain ⟨c⟩ := birth_protocol_protected_mark_exists hs hb ha hq
  exact ⟨c,c.complete⟩
"""
    ctx = """example {{θ born}} (c : BirthProtectedMark θ born) """
    fast_date = ctx + """: c.fast.final.time = c.first.final.time+{value} := by exact c.fast.date
"""
    fast_mode = ctx + """: c.fast.final.main 0 = .{value} := by exact c.fast.main_slow
"""
    fast_charge = ctx + """: c.fast.final.x 0 .q = {value} := by exact c.fast.charge
"""
    fast_raw = ctx + """: c.fast.final.raw 0 0 = {value} := by exact c.fast.raw_none 0 0
"""
    arrival_mode = ctx + """: c.arrival.final.main 0 = .{value} := by exact c.arrival.main_slow
"""
    arrival_q = ctx + """: 7/50 < c.arrival.final.x 0 .q ∧ c.arrival.final.x 0 .q < {upper} := by
  exact c.arrival.charge
"""
    arrival_b = ctx + """: c.arrival.final.x 0 .b = c.fast.final.x 0 .b {extra} := by
  exact c.arrival.recovery_preserved
"""
    mark = ctx + """: c.execution.ledger.mark 0 0 = {value} := by exact c.mark_dose
"""
    error = ctx + """: c.execution.ledger.error 0 0 = {value} := by exact c.error_dose
"""
    recovery = ctx + """: c.final.x 0 .b = {value} := by exact c.recovery
"""
    main = ctx + """: c.final.main 0 = .{value} := by exact c.mark.main_slow
"""
    aux = ctx + """: c.final.aux 0 0 = .{value} := by exact c.mark.aux_silent
"""
    m = ctx + """: c.final.x 0 (.m 0) = {value} := by exact c.mark.sensor_charge
"""
    raw = ctx + """: c.final.raw 0 0 = some {origin} := by
  have hr : c.final.raw 0 0 = some c.arrival.final.time := c.mark.raw_active
  rw [c.arrival.date] at hr
  exact hr
"""
    pending = ctx + """: c.final.pending = sourceTrain 0 0 40 8 {count} ++ sourceTrain 0 0 160 8 16 := by
  exact c.pending
"""
    deliveries = ctx + """: c.execution.deliveries = sourceTrain 0 0 0 8 {count} := by exact c.deliveries
"""
    outputs = ctx + """: c.execution.ledger.emissions = {value} := by exact c.emissions
"""
    q_ode = """example {{n θ}} (s : Snapshot n) (i : Fin n) (p : Port) (t : ℝ) :
    slowMarkMain θ s i p t = s.x i .q*Real.exp (-{integral}) := by rfl
"""
    energy = """example {{n θ}} (s : Snapshot n) (i : Fin n) (p : Port) (t : ℝ) :
    slowMarkWork θ s i p t = 11/10+{coeff}*(θ i).lm p*slowMarkSensor θ s i p t := by rfl
"""
    return [
        ('the actual birth-to-protected-MARK factory retains all sources', contract.format(count='16'), contract.format(count='15')),
        ('FAST really lasts one time unit after the actual FIRE', fast_date.format(value='1'), fast_date.format(value='1/2')),
        ('FAST exit really enters SLOW rather than READY', fast_mode.format(value='slow'), fast_mode.format(value='ready')),
        ('FAST exit has its physical quarter charge', fast_charge.format(value='1/4'), fast_charge.format(value='1/10')),
        ('the first pulse really expires before input32', fast_raw.format(value='none'), fast_raw.format(value='some 24')),
        ('source32 arrives while the main is still SLOW', arrival_mode.format(value='slow'), arrival_mode.format(value='ready')),
        ('the charge at32 keeps its real slow-decay bounds', arrival_q.format(upper='4/25'), arrival_q.format(upper='1/10')),
        ('recovery has not yet learned at the raw arrival', arrival_b.format(extra=''), arrival_b.format(extra='+1/10')),
        ('the protected input supplies one actual MARK dose', mark.format(value='1/10'), mark.format(value='0')),
        ('protected ERROR does not add learning to the first strong pulse', error.format(value='9/5'), error.format(value='12/5')),
        ('recovery starts from the own perturbed birth value', recovery.format(value='born.x 0 .b+1/10'), recovery.format(value='9/50')),
        ('the main remains SLOW after the short protected MARK', main.format(value='slow'), main.format(value='ready')),
        ('the auxiliary enters SILENT at the actual MARK endpoint', aux.format(value='silent'), aux.format(value='ready')),
        ('MARK ends at auxiliary charge four fifths', m.format(value='4/5'), m.format(value='1/40')),
        ('the protected pulse retains raw origin32', raw.format(origin='32'), raw.format(origin='c.final.time')),
        ('all twenty-seven future tokens remain exactly queued', pending.format(count='11'), pending.format(count='12')),
        ('the five source occurrences are really delivered', deliveries.format(count='5'), deliveries.format(count='4')),
        ('the protected input does not invent a second output', outputs.format(value='[(0,c.first.final.time)]'), outputs.format(value='[(0,c.first.final.time),(0,c.final.time)]')),
        ('main charge integrates the changing recovery inside MARK', q_ode.format(integral='slowMarkIntegral θ s i p t'), q_ode.format(integral='s.x i .b*(t-s.time)')),
        ('energy includes actual protected MARK work', energy.format(coeff='3/2'), energy.format(coeff='1')),
    ]


def main():
    controls = cases()
    with tempfile.TemporaryDirectory(prefix='hybrid-protected-mark-negative-', dir=ROOT) as tmp:
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

        check('\n'.join(good for _,good,_ in controls), True, 'valid constructed protected MARK controls')
        for name,_,bad in controls:
            check(bad, False, name)
            print(f'{name}: physical conclusion accepted; altered claim rejected.', flush=True)


if __name__ == '__main__':
    main()
