#!/usr/bin/env python3
"""Reject altered C birth, physical counts, inherited memories and lost sources."""
from pathlib import Path
import subprocess
import tempfile

from lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[1]
PREFIX = '''import KernelR.HybridCEntry
open KernelR.Hybrid
'''


def cases():
    contract = """example {{θ freshB freshC ε born s u v}} (forward backward delay : ℝ → ℝ)
    (teaching : @StagedExecution 1 θ freshB (fun _ _ => []) (reciprocalEntryRouter forward backward) born s)
    (following : Execution (extendParameters θ freshB) (reciprocalEntryRouter forward backward) s u)
    (introduction : @StagedExecution 2 (extendParameters θ freshB) freshC
      (reciprocalEntryRouter forward backward) (cTeachingRouter delay) u v)
    (hborn : BirthState born) (hb : PhysicalBox (extendParameters (extendParameters θ freshB) freshC) ε)
    (ha : ∀ p, born.aux 0 p = .ready)
    (hqueue : born.pending = sourceTrain 0 0 0 8 16 ++ sourceTrain 0 0 160 8 16)
    (hbirthB : teaching.beforeBirth.time = 160) (hteaching : s.time = 3199/10)
    (hreturn : u.time = 4599/10) (hbirthC : introduction.beforeBirth.time = {birth})
    (hend : v.time = {end})
    (hsourcesB : teaching.birth.sources = sourceTrain 1 2 320 8 16 ++ sourceTrain 1 2 480 8 {count})
    (hsourcesC : ∀ d ∈ introduction.birth.sources, 640 ≤ d.due)
    (hf : ∀ t, 3/10 ≤ forward t ∧ forward t ≤ 2/5)
    (hback : ∀ t, 3/10 ≤ backward t ∧ backward t ≤ 2/5)
    (hd : ∀ t, 3/10 ≤ delay t ∧ delay t ≤ 2/5) :
    Nonempty (CEntry forward backward delay teaching following introduction) := by
  exact StagedExecution.reciprocal_c_entry forward backward delay teaching following introduction
    hborn hb ha hqueue (by intro i t; rfl) hbirthB hteaching hreturn hbirthC hend hsourcesB hsourcesC hf hback hd
"""
    context = """example {{θ freshB freshC rb born s u v forward backward delay}}
    {{teaching : @StagedExecution 1 θ freshB rb (reciprocalEntryRouter forward backward) born s}}
    {{following : Execution (extendParameters θ freshB) (reciprocalEntryRouter forward backward) s u}}
    {{introduction : @StagedExecution 2 (extendParameters θ freshB) freshC
      (reciprocalEntryRouter forward backward) (cTeachingRouter delay) u v}}
    (entry : CEntry forward backward delay teaching following introduction) :
"""
    a_count = context + """    (teaching.before.emissionTimes 0).length + (teaching.after.emissionTimes 0).length +
      (following.emissionTimes 0).length + (introduction.before.emissionTimes 0).length +
      (introduction.after.emissionTimes 0).length = {value} := by
  have h := entry.a_emissions
  omega
"""
    b_count = context + """    (teaching.after.emissionTimes 1).length + (following.emissionTimes 1).length +
      (introduction.before.emissionTimes 1).length + (introduction.after.emissionTimes 1).length = {value} := by
  have h := entry.b_emissions
  omega
"""
    c_count = context + """    (introduction.after.emissionTimes 2).length = {value} := by
  have h := entry.c_emissions
  omega
"""
    local_context = """example {{θ fresh s u forward backward delay}}
    {{e : @StagedExecution 2 θ fresh (reciprocalEntryRouter forward backward) (cTeachingRouter delay) s u}}
    (h : StagedCIntroduction forward backward delay e) :
"""
    c_error = local_context + """    e.after.ledger.error 2 1 = {value} := by
  have herror := h.phase.c_phase.error_target
  linarith
"""
    c_mark = local_context + """    e.after.ledger.mark 2 1 = {value} := by
  have hmark := h.phase.c_phase.mark_target
  linarith
"""
    c_recovery = local_context + """    u.x 2 .b = e.birth.newborn.x .b + {value} := by
  have hb := h.recovery_c
  linarith
"""
    b_memory = local_context + """    u.x 1 (.z 2) = s.x 1 (.z 2) + {value} := by
  have hz := h.gain_b 2
  linarith
"""
    c_memory = local_context + """    u.x 2 (.z 1) = {origin} + 3/5 := by
  exact h.gain_c_target
"""
    quiet = local_context + """    e.before.emissionTimes 1 = {value} := by
  exact h.boundary.b_idle.emissions
"""
    sources = """example {{θ fresh s u forward backward delay}}
    {{e : @StagedExecution 2 θ fresh (reciprocalEntryRouter forward backward) (cTeachingRouter delay) s u}}
    (h : StagedCIntroduction forward backward delay e)
    (hs : e.birth.sources = sourceTrain 2 0 640 4 25) :
    (u.pending.filter (fun d => d.cell = 2)).Perm (sourceTrain 2 0 640 4 {count}) := by
  simpa only [hs] using h.c_sources
"""
    good = dict(birth='480', end='6399/10', count='16')
    return [
        ('all sixteen B teaching sources survive the reciprocal handoff', contract.format(**good), contract.format(**dict(good, count='15'))),
        ('C is introduced at the actual source boundary', contract.format(**good), contract.format(**dict(good, birth='479'))),
        ('the endpoint follows the complete teaching train', contract.format(**good), contract.format(**dict(good, end='600'))),
        ('A remains at thirty-eight cumulative outputs', a_count.format(value='38'), a_count.format(value='39')),
        ('B reaches forty-three cumulative outputs', b_count.format(value='43'), b_count.format(value='44')),
        ('C produces fourteen physical teaching outputs', c_count.format(value='14'), c_count.format(value='15')),
        ('C receives exactly one ERROR dose', c_error.format(value='3/5'), c_error.format(value='6/5')),
        ('C receives its protected MARK dose', c_mark.format(value='1/10'), c_mark.format(value='0')),
        ('C recovery starts from its own newborn coordinates', c_recovery.format(value='1/10'), c_recovery.format(value='1/5')),
        ('B keeps its learned return gain during C teaching', b_memory.format(value='0'), b_memory.format(value='3/5')),
        ('C does not inherit B memories', c_memory.format(origin='e.birth.newborn.x (.z 1)'), c_memory.format(origin='s.x 1 (.z 1)')),
        ('B does not emit before the C birth', quiet.format(value='[]'), quiet.format(value='[480]')),
        ('all twenty-five future C inputs remain queued', sources.format(count='25'), sources.format(count='24')),
    ]


def main():
    controls = cases()
    with tempfile.TemporaryDirectory(prefix='hybrid-c-introduction-negative-', dir=ROOT) as tmp:
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

        check('\n'.join(good for _, good, _ in controls), True, 'valid C introduction controls')
        for name, _, bad in controls:
            check(bad, False, name)
            print(f'{name}: physical conclusion accepted; altered claim rejected.', flush=True)


if __name__ == '__main__':
    main()
