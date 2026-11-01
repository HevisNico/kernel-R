#!/usr/bin/env python3
"""Reject altered physical reciprocal entry, erased residuals and future queues."""
from pathlib import Path
import subprocess
import tempfile

from lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[1]
PREFIX = '''import KernelR.HybridReciprocalEntry
open KernelR.Hybrid
'''


def cases():
    contract = """example {{θ fresh ε born s u}} (forward backward : ℝ → ℝ)
    (e : @StagedExecution 1 θ fresh (fun _ _ => []) (reciprocalEntryRouter forward backward) born s)
    (following : Execution (extendParameters θ fresh) (reciprocalEntryRouter forward backward) s u)
    (hborn : BirthState born) (hb : PhysicalBox (extendParameters θ fresh) ε)
    (ha : ∀ p, born.aux 0 p = .ready)
    (hqueue : born.pending = sourceTrain 0 0 0 8 16 ++ sourceTrain 0 0 160 8 16)
    (hbirth : e.beforeBirth.time = 160) (hteaching : s.time = 3199/10) (hend : u.time = {end})
    (hsources : e.birth.sources = {sources} ++ sourceTrain 1 2 480 8 16)
    (hf : ∀ t, 3/10 ≤ forward t ∧ forward t ≤ 2/5)
    (hbw : ∀ t, 3/10 ≤ backward t ∧ backward t ≤ 2/5) :
    Nonempty (ReciprocalEntry forward backward e following) := by
  exact StagedExecution.reciprocal_entry_two_trains forward backward e following hborn hb ha hqueue
    (by intro i t; rfl) hbirth hteaching hend hsources hf hbw
"""
    a_count = """example {{θ fresh rb born s u forward backward}}
    {{e : @StagedExecution 1 θ fresh rb (reciprocalEntryRouter forward backward) born s}}
    {{following : Execution (extendParameters θ fresh) (reciprocalEntryRouter forward backward) s u}}
    (h : ReciprocalEntry forward backward e following) :
    (e.before.emissionTimes 0).length + (e.after.emissionTimes 0).length +
      (following.emissionTimes 0).length = {value} := by
  have hc := h.a_emissions
  omega
"""
    b_count = """example {{θ fresh rb born s u forward backward}}
    {{e : @StagedExecution 1 θ fresh rb (reciprocalEntryRouter forward backward) born s}}
    {{following : Execution (extendParameters θ fresh) (reciprocalEntryRouter forward backward) s u}}
    (h : ReciprocalEntry forward backward e following) :
    (e.after.emissionTimes 1).length + (following.emissionTimes 1).length = {value} := by
  have hc := h.b_emissions
  omega
"""
    a_error = """example {{θ route s u}} {{e : @Execution 2 θ route s u}} (h : FeedbackEpoch e) :
    e.ledger.error 0 2 = {value} := by
  have hd := h.a_learning.error_target
  linarith
"""
    b_mark = """example {{θ route s u}} {{e : @Execution 2 θ route s u}} (h : FeedbackEpoch e) :
    e.ledger.mark 1 2 = {value} := by
  have hd := h.b_learning.mark_zero 2
  linarith
"""
    recovery = """example {{θ fresh rb born s u forward backward}}
    {{e : @StagedExecution 1 θ fresh rb (reciprocalEntryRouter forward backward) born s}}
    {{following : Execution (extendParameters θ fresh) (reciprocalEntryRouter forward backward) s u}}
    (h : ReciprocalEntry forward backward e following) : u.x 1 .b = e.birth.newborn.x .b + {value} := by
  have hb := h.recovery_b
  linarith
"""
    gain = """example {{θ fresh rb born s u forward backward}}
    {{e : @StagedExecution 1 θ fresh rb (reciprocalEntryRouter forward backward) born s}}
    {{following : Execution (extendParameters θ fresh) (reciprocalEntryRouter forward backward) s u}}
    (h : ReciprocalEntry forward backward e following) : u.x 1 (.z 2) = e.birth.newborn.x (.z 2) + {value} := by
  have hg := h.gain_b_return
  linarith
"""
    residual = """example {{n θ ε route s u i}} {{e : @Execution n θ route s u}}
    (pulse : LearnedPulse e i) (hb : PhysicalBox θ ε) (hi : UpperRegion s)
    (p : Port) (hs : PreparedSection s i) (hq : 1/10 ≤ s.x i .q)
    (hg : 9/5 ≤ Real.exp (s.x i (.z p)) ∧ Real.exp (s.x i (.z p)) ≤ 12/5)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q) (ht : s.time + 15/2 ≤ u.time) :
    pulse.trigger.beforeFire.time - s.time {relation} restLatency (Real.exp (s.x i (.z p))) := by
  exact pulse.latency_le_rest hb hi p hs hq hg hr ho hno ht
"""
    first_gap = """example {{first rest : ℝ}}
    (hf : 3/10 < first ∧ first < 9/10) (hr : 3/10 < rest ∧ rest < 9/10) (hle : first ≤ rest)
    (delay : ℝ → ℝ) (hd : ∀ t, 3/10 ≤ delay t ∧ delay t ≤ 2/5) :
    79/10 ≤ (352+rest+delay (352+rest)) - (344+first+delay (344+first)) ∧
      (352+rest+delay (352+rest)) - (344+first+delay (344+first)) ≤ {value} := by
  constructor <;> linarith [(hd (344+first)).1,(hd (344+first)).2,
    (hd (352+rest)).1,(hd (352+rest)).2,hf.1,hf.2,hr.1,hr.2]
"""
    future = """example {{θ fresh rb ra born u}}
    {{e : @StagedExecution 1 θ fresh rb ra born u}} (h : TeachingQueueClosure e) :
    (u.pending.filter (fun d => d.cell = 1)).Perm ({value}) := by
  exact h.b_sources
"""
    good = dict(end='4599/10',sources='sourceTrain 1 2 320 8 16')
    return [
        ('all sixteen B novelty sources are required', contract.format(**good), contract.format(**dict(good,sources='sourceTrain 1 2 320 8 15'))),
        ('B novelty uses its actual untrained return port', contract.format(**good), contract.format(**dict(good,sources='sourceTrain 1 1 320 8 16'))),
        ('the terminal state follows the last source and output', contract.format(**good), contract.format(**dict(good,end='440'))),
        ('physical reciprocal entry gives A exactly thirty-eight outputs', a_count.format(value='38'), a_count.format(value='39')),
        ('physical reciprocal entry gives B exactly twenty-seven outputs', b_count.format(value='27'), b_count.format(value='28')),
        ('A receives its three return ERROR doses', a_error.format(value='9/5'), a_error.format(value='0')),
        ('prepared B relearning gives no additional MARK', b_mark.format(value='0'), b_mark.format(value='1/10')),
        ('the return epoch does not add recovery to B', recovery.format(value='1/10'), recovery.format(value='1/5')),
        ('B return gain contains exactly three ERROR doses', gain.format(value='9/5'), gain.format(value='12/5')),
        ('the first residual latency is not forced to equal the rest reference', residual.format(relation='≤'), residual.format(relation='=')),
        ('the first wire gap cannot reuse the regular upper bound', first_gap.format(value='87/10'), first_gap.format(value='81/10')),
        ('teaching retains the later external B source queue', future.format(value='e.birth.sources'), future.format(value='[]')),
    ]


def main():
    controls = cases()
    with tempfile.TemporaryDirectory(prefix='hybrid-reciprocal-negative-', dir=ROOT) as tmp:
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

        check('\n'.join(good for _, good, _ in controls), True, 'valid reciprocal controls')
        for name, _, bad in controls:
            check(bad, False, name)
            print(f'{name}: physical conclusion accepted; altered claim rejected.', flush=True)


if __name__ == '__main__':
    main()
