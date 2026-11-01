#!/usr/bin/env python3
"""Reject altered staged teaching contracts, counts, birth memories and guards."""
from pathlib import Path
import subprocess
import tempfile

from lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[1]
PREFIX = '''import KernelR.HybridStagedTeaching
open KernelR.Hybrid
'''


def cases():
    contract = """example {{θ fresh ε born u}} (forward backward : ℝ → ℝ)
    (e : @StagedExecution 1 θ fresh (fun _ _ => []) (reciprocalEntryRouter forward backward) born u)
    (hborn : BirthState born) (hb : PhysicalBox (extendParameters θ fresh) ε)
    (ha : ∀ p, born.aux 0 p = .ready)
    (hqueue : born.pending = sourceTrain 0 0 0 8 16 ++ {train})
    (hbirth : e.beforeBirth.time = {birth}) (hend : u.time = 3199/10)
    (hsources : ∀ d ∈ e.birth.sources, {future} ≤ d.due)
    (hf : ∀ t, 3/10 ≤ forward t ∧ forward t ≤ 2/5)
    (hbw : ∀ t, 3/10 ≤ backward t ∧ backward t ≤ 2/5) : Nonempty (StagedTeaching e) := by
  exact StagedExecution.reciprocal_teaching_epoch forward backward e hborn hb ha hqueue
    (by intro i t; rfl) hbirth hend hsources hf hbw
"""
    a_count = """example {{θ fresh rb ra born u}}
    {{e : @StagedExecution 1 θ fresh rb ra born u}} (h : StagedTeaching e) :
    (e.before.emissionTimes 0).length + (e.after.emissionTimes 0).length = {value} := by
  have hc := h.a_emissions
  omega
"""
    b_count = """example {{θ fresh rb ra born u}}
    {{e : @StagedExecution 1 θ fresh rb ra born u}} (h : StagedTeaching e) :
    (e.after.emissionTimes 1).length = {value} := by
  have hc := h.b_emissions
  omega
"""
    b_error = """example {{θ fresh rb ra born u}}
    {{e : @StagedExecution 1 θ fresh rb ra born u}} (h : StagedTeaching e) :
    e.after.ledger.error 1 1 = {value} := by
  have hd := h.teaching.b_phase.error_target
  linarith
"""
    b_mark = """example {{θ fresh rb ra born u}}
    {{e : @StagedExecution 1 θ fresh rb ra born u}} (h : StagedTeaching e) :
    e.after.ledger.mark 1 1 = {value} := by
  have hd := h.teaching.b_phase.mark_target
  linarith
"""
    a_gain = """example {{θ fresh rb ra born u}}
    {{e : @StagedExecution 1 θ fresh rb ra born u}} (h : StagedTeaching e) :
    u.x 0 (.z 0) = born.x 0 (.z 0) + {value} := by
  have hg := h.gain_a_target
  linarith
"""
    b_recovery = """example {{θ fresh rb ra born u}}
    {{e : @StagedExecution 1 θ fresh rb ra born u}} (h : StagedTeaching e) :
    u.x 1 .b = {value} := by
  exact h.recovery_b
"""
    b_ready = """example {{θ fresh rb ra born u}}
    {{e : @StagedExecution 1 θ fresh rb ra born u}} (h : StagedTeaching e) : u.main 1 = .{value} := by
  exact h.teaching.b_phase.prepared.ready
"""
    activation_gain = """example {{θ route s u}} {{e : @Execution 2 θ route s u}}
    (h : TeachingActivation e) : h.cut.afterArrival.x 1 (.z 1) = s.x 1 (.z 1) + {value} := by
  have hc := congrFun (congrFun h.coordinates 1) (.z 1)
  linarith
"""
    activation_queue = """example {{θ route s u}} {{e : @Execution 2 θ route s u}}
    (h : TeachingActivation e) : {value}.Perm (sourceTrain 0 0 168 8 15) := by
  exact h.queueA
"""
    terminal = """example {{n θ route s u}} (e : @Execution n θ route s u)
    (d : Delivery n) (later : List (Delivery n))
    (hq : s.pending.Perm (d :: later)) (ht : d.due = u.time)
    (hl : ∀ f ∈ later, u.time < f.due) (hraw : s.raw d.cell d.port = none)
    (hr : ∀ i t, route i t = []) :
    (u.raw d.cell d.port = none ∧ u.pending.Perm ({value})) ∨
      (u.raw d.cell d.port = some u.time ∧ u.pending.Perm later) := by
  exact e.terminal_source_queue d later hq ht hl hraw hr
"""
    reverse = """example (forward backward : ℝ → ℝ) (i : Fin 2) {{t : ℝ}} (ht : t {relation} 320) :
    ∀ d ∈ reciprocalEntryRouter forward backward i t, d.cell ≠ 0 := by
  exact reciprocalEntryRouter.closed_to_a forward backward i ht
"""
    good = dict(train='sourceTrain 0 0 160 8 16',birth='160',future='320')
    return [
        ('the complete source queue retains source 160', contract.format(**good), contract.format(**dict(good,train='sourceTrain 0 0 168 8 15'))),
        ('B has no early external source during teaching', contract.format(**good), contract.format(**dict(good,future='160'))),
        ('the birth date is connected to the actual source boundary', contract.format(**good), contract.format(**dict(good,birth='168'))),
        ('the two actual phases give A exactly twenty-eight outputs', a_count.format(value='28'), a_count.format(value='29')),
        ('B gives exactly fourteen outputs after its fresh birth', b_count.format(value='14'), b_count.format(value='15')),
        ('B learns its own single ERROR dose', b_error.format(value='3/5'), b_error.format(value='9/5')),
        ('B receives one protected MARK dose', b_mark.format(value='1/10'), b_mark.format(value='1/5')),
        ('A gains no extra learning during teaching', a_gain.format(value='9/5'), a_gain.format(value='12/5')),
        ('B recovery starts at its own newborn memory', b_recovery.format(value='e.birth.newborn.x .b + 1/10'), b_recovery.format(value='e.afterBirth.x 0 .b + 1/10')),
        ('B is prepared READY at the terminal date', b_ready.format(value='ready'), b_ready.format(value='slow')),
        ('source activation does not teach B instantaneously', activation_gain.format(value='0'), activation_gain.format(value='3/5')),
        ('source activation retains B future pending tokens', activation_queue.format(value='(h.cut.afterArrival.pending.filter (fun d => d.cell = 0))'), activation_queue.format(value='h.cut.afterArrival.pending')),
        ('raw absence retains the unconsumed boundary source', terminal.format(value='d :: later'), terminal.format(value='later')),
        ('the reverse contact is allowed to open at 320', reverse.format(relation='<'), reverse.format(relation='≤')),
    ]


def main():
    controls = cases()
    with tempfile.TemporaryDirectory(prefix='hybrid-teaching-negative-', dir=ROOT) as tmp:
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

        check('\n'.join(good for _, good, _ in controls), True, 'valid teaching controls')
        for name, _, bad in controls:
            check(bad, False, name)
            print(f'{name}: physical conclusion accepted; altered claim rejected.', flush=True)


if __name__ == '__main__':
    main()
