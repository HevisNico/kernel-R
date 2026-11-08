#!/usr/bin/env python3
"""Guard the complete source-to-cadence contract and physical cumulative results."""
from pathlib import Path
import subprocess
import tempfile

from scripts.lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[2]
PREFIX = '''import KernelR.HybridCadenceEntry
open KernelR.Hybrid
'''


def cases():
    contract = """example {{θ freshB freshC ε born s u v w}}
    (f b d nf nb : ℝ → ℝ)
    (teaching : @StagedExecution 1 θ freshB (fun _ _ => []) (reciprocalEntryRouter f b) born s)
    (following : Execution (extendParameters θ freshB) (reciprocalEntryRouter f b) s u)
    (introduction : @StagedExecution 2 (extendParameters θ freshB) freshC
      (reciprocalEntryRouter f b) (cTeachingRouter d) u v)
    (next : Execution (extendParameters (extendParameters θ freshB) freshC) (cadenceRouter nf nb) v w)
    (hborn : BirthState born) (hb : PhysicalBox (extendParameters (extendParameters θ freshB) freshC) ε)
    (ha : ∀ p, born.aux 0 p = .ready)
    (hqueue : born.pending = sourceTrain 0 0 0 8 16 ++ sourceTrain 0 0 160 8 16)
    (hbirthB : teaching.beforeBirth.time = 160) (hteaching : s.time = 3199/10)
    (hreturn : u.time = 4599/10) (hbirthC : introduction.beforeBirth.time = 480)
    (hintro : v.time = 6399/10) (hend : w.time = {end})
    (hsB : teaching.birth.sources = sourceTrain 1 2 320 8 16 ++ sourceTrain 1 2 480 8 16)
    (hsC : introduction.birth.sources = sourceTrain 2 0 640 4 {count})
    (hf : ∀ t, 3/10 ≤ f t ∧ f t ≤ 2/5) (hback : ∀ t, 3/10 ≤ b t ∧ b t ≤ 2/5)
    (hd : ∀ t, 3/10 ≤ d t ∧ d t ≤ 2/5)
    (hnf : ∀ t, 3/10 ≤ nf t ∧ nf t ≤ {upper}) (hnb : ∀ t, 3/10 ≤ nb t ∧ nb t ≤ 2/5) :
    ∃ entry : CEntry f b d teaching following introduction, CadenceEntry entry nf nb next := by
  exact StagedExecution.reciprocal_cadence_entry f b d nf nb teaching following introduction next
    hborn hb ha hqueue (by intro i t; rfl) hbirthB hteaching hreturn hbirthC hintro hend hsB hsC
    hf hback hd hnf hnb
"""
    context = """example {{θ freshB freshC rb born s u v w f b d nf nb}}
    {{teaching : @StagedExecution 1 θ freshB rb (reciprocalEntryRouter f b) born s}}
    {{following : Execution (extendParameters θ freshB) (reciprocalEntryRouter f b) s u}}
    {{introduction : @StagedExecution 2 (extendParameters θ freshB) freshC
      (reciprocalEntryRouter f b) (cTeachingRouter d) u v}}
    {{next : Execution (extendParameters (extendParameters θ freshB) freshC) (cadenceRouter nf nb) v w}}
    {{entry : CEntry f b d teaching following introduction}}
    (h : CadenceEntry entry nf nb next) :
"""
    a_total = context + """    (teaching.before.emissionTimes 0).length + (teaching.after.emissionTimes 0).length +
      (following.emissionTimes 0).length + (introduction.before.emissionTimes 0).length +
      (introduction.after.emissionTimes 0).length + (next.emissionTimes 0).length = {value} := by
  have hc := h.a_emissions
  omega
"""
    b_total = context + """    (teaching.after.emissionTimes 1).length + (following.emissionTimes 1).length +
      (introduction.before.emissionTimes 1).length + (introduction.after.emissionTimes 1).length +
      (next.emissionTimes 1).length = {value} := by
  have hc := h.b_emissions
  omega
"""
    c_total = context + """    (introduction.after.emissionTimes 2).length + (next.emissionTimes 2).length = {value} := by
  have hc := h.c_emissions
  omega
"""
    local = """example {{θ route s u}} {{e : @Execution 3 θ route s u}} (h : CadenceCascade e) :
"""
    local_count = local + """    (e.emissionTimes {cell}).length = {value} := by
  have hc := h.{field}
  omega
"""
    recovery = context + """    w.x 2 .b = introduction.birth.newborn.x .b+{value} := by
  have hb := h.recovery_c
  linarith
"""
    b_memory = context + """    w.x 1 (.z 2) = teaching.birth.newborn.x (.z 2)+{value} := by
  have hz := h.gain_b_return
  linarith
"""
    c_memory = context + """    w.x 2 (.z 0) = {origin}+12/5 := by
  exact h.gain_c_initial
"""
    queue = local + """    u.pending = {value} := by
  exact h.pending_empty
"""
    error = local + """    e.ledger.error 0 2 = {value} := by
  have hd := h.a_error
  linarith
"""
    mark = local + """    e.ledger.mark 1 2 = {value} := by
  have hd := h.b_mark
  linarith
"""
    rest = local + """    u.x 0 .q = {value} := by
  have hq := h.charge_rest 0
  linarith
"""
    good = dict(end='7899/10', count='25', upper='2/5')
    return [
        ('the full birth-to-cadence contract retains twenty-five C sources', contract.format(**good), contract.format(**dict(good,count='24'))),
        ('the full physical trace reaches its stated endpoint', contract.format(**good), contract.format(**dict(good,end='780'))),
        ('the full wire contract keeps its proved independent delay bound', contract.format(**good), contract.format(**dict(good,upper='1/2'))),
        ('A has fifty-four cumulative physical outputs', a_total.format(value='54'), a_total.format(value='55')),
        ('B has sixty-one cumulative physical outputs', b_total.format(value='61'), b_total.format(value='62')),
        ('C has thirty-four cumulative physical outputs', c_total.format(value='34'), c_total.format(value='35')),
        ('the A cascade has sixteen outputs', local_count.format(cell='0',field='a_emissions',value='16'), local_count.format(cell='0',field='a_emissions',value='18')),
        ('the B cascade has eighteen outputs', local_count.format(cell='1',field='b_emissions',value='18'), local_count.format(cell='1',field='b_emissions',value='20')),
        ('the C cascade has twenty outputs', local_count.format(cell='2',field='c_emissions',value='20'), local_count.format(cell='2',field='c_emissions',value='21')),
        ('final recovery starts from the own C newborn and includes three MARKs', recovery.format(value='3/10'), recovery.format(value='1/5')),
        ('B retains the fourth ERROR in its own return memory', b_memory.format(value='12/5'), b_memory.format(value='9/5')),
        ('C does not inherit B return-port memory', c_memory.format(origin='introduction.birth.newborn.x (.z 0)'), c_memory.format(origin='teaching.birth.newborn.x (.z 0)')),
        ('the final conserved queue is empty', queue.format(value='[]'), queue.format(value='[⟨0,2,800⟩]')),
        ('A receives one additional full ERROR dose', error.format(value='3/5'), error.format(value='0')),
        ('B receives two additional full MARK doses', mark.format(value='1/5'), mark.format(value='1/10')),
        ('all final returns restore physical resting charge', rest.format(value='1/10'), rest.format(value='1/5')),
    ]


def main():
    controls = cases()
    with tempfile.TemporaryDirectory(prefix='hybrid-cascade-negative-', dir=ROOT) as tmp:
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

        check('\n'.join(good for _,good,_ in controls), True, 'valid complete cascade controls')
        for name,_,bad in controls:
            check(bad, False, name)
            print(f'{name}: physical conclusion accepted; altered claim rejected.', flush=True)


if __name__ == '__main__':
    main()
