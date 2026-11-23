# Inverter instances with SKY130 mismatch: measure and Lean gate (development)

**Development work. Nothing here is preregistered and nothing here is a campaign.** Development seeds only
(9901-9903), outside 8501-8515 and every campaign seed.

- `instance.py SEED OUTDIR`: one instance per seed. The cell is `../inverter.py` (iteration 2), imported unchanged;
  the model section is `tt_mm` and the sample is drawn by `setseed SEED` then `reset`, as `run.py`'s `_mm` sections.
  Five runs (R1 absent, R2 present, R3/R4 leak on both sides of rest, R5 an ideal slow ramp of the main node through
  the FIRE level for the static threshold). Each log records a fingerprint (bias of the comparator, vth of the
  comparator pair and of the two mirrors); the instance is refused unless every run has the same sample.
  Writes `OUTDIR/SEED/MEASURE.json`; traces stay local.
- `emit.py MEASURE.json OUTDIR --lean-build DIR`: the per-instance Lean file, the family gates' pattern (mirror
  verdicts asserted by `decide +kernel`, fallback combinations tried, the compiling one is the kernel's verdict).
- `lean/InverterInstanceCheck.lean`: the Mathlib-free premises over `Rat`, the checker and its soundness, and the
  derivation of `InverterRead` (InverterTarget.lean) on both observed reads. `lean/check.sh` builds it.

K0 (eligibility) = measured values, outward rounded. K3 (room) = K0 plus 3 sigma of the frozen cell's noise
(`../../noise.json`): FIRE-comparator input noise on δ, two-mirror shot noise over the slot on the charge budgets.

## Open premises (not invented, not gated)

- **Real bridge.** The Rat premises are the numeric `before`/`after` hypotheses of `inhibited_silence` and
  `uninhibited_first_crossing` with the box reference in closed form and the exponential bounded by its degree-5/6
  Taylor polynomials. The ℝ lemmas linking them (closed form and monotonicity of the reference, Taylor bounds) are
  not written yet.
- **Leak asymmetry.** The theorems take one leak `a`. The gate evaluates every bound at the worse of the two measured
  sides (`aLo` for the reference maximum, `aHi` for the decay of `Q`); no tolerance lemma covers `a ≠ a′`.
- **Direct-rail delay.** `FrontEnd` delays the direct rails by exactly `emitEarly`; no tolerance is proved.
- **Latch delay** is a measured constant of the instance, not a proved bound.
- The campaign dates `window = 1/4`, `emitEarly = 2/5`, `emitLate = 13/20` are development choices.
