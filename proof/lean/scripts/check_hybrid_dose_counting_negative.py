#!/usr/bin/env python3
"""Check whole-trace counting and reject stronger or altered memory claims.

Each rejection has a positive control with the same actual execution premises.
The controls distinguish complete exposed phases from partial charge drains,
retain birth offsets, and require recovery contributions from all ports.
"""
from pathlib import Path
import subprocess
import tempfile

from lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[1]
PREFIX = '''import KernelR.HybridDoseCounting
open KernelR.Hybrid
'''


def main():
    gain = '''example {{n θ route s u}} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) (cover : ErrorSectionCover i p e) :
    u.x i (.z p) = s.x i (.z p) + ({factor} : ℝ) * cover.count := by
  rw [e.gain_balance i p, cover.ledger_eq]
'''
    recovery = '''example {{n θ route s u}} (e : @Execution n θ route s u)
    (errors : ∀ i p, ErrorSectionCover i p e)
    (marks : ∀ i p, MarkSectionCover i p e) (i : Fin n) (p₀ : Port) :
    u.x i .b = s.x i .b + (1/10 : ℝ) * ({count} : ℕ) := by
  exact (e.memory_of_section_covers errors marks).2 i
'''
    offset = '''example {{n θ route s u}} (e : @Execution n θ route s u)
    (errors : ∀ i p, ErrorSectionCover i p e)
    (marks : ∀ i p, MarkSectionCover i p e) (i : Fin n) (p : Port) :
    u.x i (.z p) = {birth}(3/5 : ℝ) * (errors i p).count := by
  exact (e.memory_of_section_covers errors marks).1 i p
'''
    comparison = '''example {{n θ₁ θ₂ route₁ route₂ s₁ u₁ s₂ u₂}}
    (left : @Execution n θ₁ route₁ s₁ u₁)
    (right : @Execution n θ₂ route₂ s₂ u₂)
    (i : Fin n) (p : Port)
    (lc : ErrorSectionCover i p left) (rc : ErrorSectionCover i p right)
    (counts : lc.count = rc.count) : {claim} := by
  have hl := left.gain_balance i p
  have hr := right.gain_balance i p
  rw [lc.ledger_eq] at hl
  rw [rc.ledger_eq, ← counts] at hr
  linarith
'''
    unique = '''example {{n θ route s u i p}} {{e : @Execution n θ route s u}}
    (left right : ErrorSectionCover i p e) : left.count = {count} := by
  exact left.count_unique right
'''
    error_exposure = '''example {{n θ route before s u after}}
    (entry : @Jump n route before s) (span : Execution θ route s u)
    (exit : Jump route u after) (i : Fin n) (p : Port)
    (hb : before.aux i p ≠ .error) (hs : s.aux i p = .error)
    (hu : u.aux i p = .error) (ha : after.aux i p ≠ .error)
    (exposed : {exposure}) : span.ledger.error i p = 3/5 := by
  exact guarded_error_dose entry span exit i p hb hs hu ha exposed
'''
    mark_exposure = '''example {{n θ route before s u after}}
    (entry : @Jump n route before s) (span : Execution θ route s u)
    (exit : Jump route u after) (i : Fin n) (p : Port)
    (hb : before.aux i p ≠ .mark) (hs : s.aux i p = .mark)
    (hu : u.aux i p = .mark) (ha : after.aux i p ≠ .mark)
    (exposed : {exposure}) : span.ledger.mark i p = 1/10 := by
  exact guarded_mark_dose entry span exit i p hb hs hu ha exposed
'''
    partial = '''example {{n θ route s u}} (span : @Execution n θ route s u)
    (i : Fin n) (p : Port) (exposed : span.ErrorExposed i p)
    (hs : s.x i (.m p) = 7/100) (hu : u.x i (.m p) = 1/40) :
    span.ledger.error i p = {dose} := by
  have h := span.error_charge_balance i p exposed
  rw [hs, hu] at h
  norm_num at h
  exact h
'''
    error_cover = '''example {{n θ route before s u after}}
    (entry : @Jump n route before s) (span : Execution θ route s u)
    (exit : Jump route u after) (i : Fin n) (p : Port)
    (hb : before.aux i p ≠ .error) (hs : s.aux i p = .error)
    (hu : u.aux i p = .error) (ha : after.aux i p ≠ .error)
    (phase : span.AllStates (fun v => v.aux i p = .error))
    (exposed : {exposure}) :
    let e : Execution θ route before after :=
      .cons (.jump entry) (span.append (.cons (.jump exit) (.nil _)))
    ∃ cover : ErrorSectionCover i p e,
      cover.count = 1 ∧ e.ledger.error i p = 3/5 := by
  dsimp only
  let cover : ErrorSectionCover i p
      (.cons (.jump entry) (span.append (.cons (.jump exit) (.nil _)))) :=
    .section entry span exit (.nil _) hb hs hu ha phase exposed (.nil _)
  refine ⟨cover, rfl, ?_⟩
  simpa [cover, ErrorSectionCover.count] using cover.ledger_eq
'''
    mark_cover = '''example {{n θ route before s u after}}
    (entry : @Jump n route before s) (span : Execution θ route s u)
    (exit : Jump route u after) (i : Fin n) (p : Port)
    (hb : before.aux i p ≠ .mark) (hs : s.aux i p = .mark)
    (hu : u.aux i p = .mark) (ha : after.aux i p ≠ .mark)
    (phase : span.AllStates (fun v => v.aux i p = .mark))
    (exposed : {exposure}) :
    let e : Execution θ route before after :=
      .cons (.jump entry) (span.append (.cons (.jump exit) (.nil _)))
    ∃ cover : MarkSectionCover i p e,
      cover.count = 1 ∧ e.ledger.mark i p = 1/10 := by
  dsimp only
  let cover : MarkSectionCover i p
      (.cons (.jump entry) (span.append (.cons (.jump exit) (.nil _)))) :=
    .section entry span exit (.nil _) hb hs hu ha phase exposed (.nil _)
  refine ⟨cover, rfl, ?_⟩
  simpa [cover, MarkSectionCover.count] using cover.ledger_eq
'''
    quiet = '''example {{n}} (θ : Fin n → Parameters) (route : Router n)
    {{T : ℝ}} (hT : 0 < T) (i : Fin n) (p : Port) :
    (birthResting (n := n) T).x i (.z p) =
      (birthResting (n := n) 0).x i (.z p) + {dose} := by
  let f := birthRestingFlow θ hT
  let e : Execution θ route (birthResting 0) (birthResting T) :=
    .cons (.flow f) (.nil _)
  let errors : ∀ i p, ErrorSectionCover i p e := fun i p =>
    .inactive (.flow f) (.nil _) (by
      change (birthResting (n := n) 0).aux i p ≠ .error ∨ _
      exact Or.inl (by simp [birthResting])) (.nil _)
  let marks : ∀ i p, MarkSectionCover i p e := fun i p =>
    .inactive (.flow f) (.nil _) (by
      change (birthResting (n := n) 0).aux i p ≠ .mark ∨ _
      exact Or.inl (by simp [birthResting])) (.nil _)
  have h := (e.memory_of_section_covers errors marks).1 i p
  simpa only [errors, ErrorSectionCover.count, Nat.cast_zero, mul_zero] using h
'''
    cases = [
        ('whole-trace ERROR increment', gain.format(factor='3/5'), gain.format(factor='2/5')),
        ('recovery includes every port',
         recovery.format(count='∑ p : Port, (marks i p).count'),
         recovery.format(count='(marks i p₀).count')),
        ('birth memory offset is retained', offset.format(birth='s.x i (.z p) + '),
         offset.format(birth='')),
        ('equal counts preserve increments across different devices',
         comparison.format(claim='u₁.x i (.z p) - s₁.x i (.z p) = u₂.x i (.z p) - s₂.x i (.z p)'),
         comparison.format(claim='u₁.x i (.z p) = u₂.x i (.z p)')),
        ('actual-trace ERROR count is unique', unique.format(count='right.count'),
         unique.format(count='right.count + 1')),
        ('complete ERROR requires full exposure',
         error_exposure.format(exposure='span.ErrorExposed i p'),
         error_exposure.format(exposure='span.AuxFlows i p .error')),
        ('complete MARK requires protected exposure',
         mark_exposure.format(exposure='span.MarkExposed i p'),
         mark_exposure.format(exposure='span.AuxFlows i p .mark')),
        ('partial ERROR cannot be counted as a full dose', partial.format(dose='9/25'),
         partial.format(dose='3/5')),
        ('actual ERROR entry/span/exit builds a one-section cover',
         error_cover.format(exposure='span.ErrorExposed i p'),
         error_cover.format(exposure='span.AuxFlows i p .error')),
        ('actual protected MARK entry/span/exit builds a one-section cover',
         mark_cover.format(exposure='span.MarkExposed i p'),
         mark_cover.format(exposure='span.AuxFlows i p .mark')),
        ('positive-duration quiet birth execution learns zero', quiet.format(dose='0'),
         quiet.format(dose='3/5')),
    ]
    with tempfile.TemporaryDirectory(prefix='hybrid-dose-counting-negative-', dir=ROOT) as tmp:
        path = Path(tmp) / 'Check.lean'
        command = lean_check_command(tmp, root_module='KernelR.HybridDoseCounting')
        for name, good, bad in cases:
            for expected, source in [(True, good), (False, bad)]:
                path.write_text(PREFIX + source)
                result = subprocess.run([*command, str(path)], cwd=ROOT, text=True,
                                        stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                        timeout=120)
                if (result.returncode == 0) != expected:
                    raise SystemExit(f'{name}: unexpected result:\n{result.stdout}')
                if not expected and 'error:' not in result.stdout:
                    raise SystemExit(f'{name}: failed without a Lean diagnostic:\n{result.stdout}')
            print(f'{name}: physical conclusion accepted; altered claim rejected.', flush=True)


if __name__ == '__main__':
    main()
