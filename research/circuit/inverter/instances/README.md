# Inverter instances with SKY130 mismatch: measure and Lean gate (development)

**Development work. Nothing here is preregistered and nothing here is a campaign.**

One self-contained package, meant to become the frozen campaign code later. Everything that can be chosen is in
[`config.json`](config.json).

| File | Role |
|---|---|
| `invinst/cell.py` | the deck; byte-identical at section `tt` to the pushed cell `../inverter.py` (062a2862), checked by `tests/test_cell.py` |
| `invinst/sim.py` | one ngspice run; the mismatch draw is `setseed SEED` then `reset` (the mechanism of `research/circuit/run.py`'s `_mm` sections, reused, not imported: run.py is a script) |
| `invinst/measure.py` | five runs per instance and every quantity of the inverter theorems |
| `invinst/gate.py` | exact Python mirror of the Lean premises, the per-instance Lean file, the kernel's verdict |
| `invinst/driver.py` | the one driver: a JOBS file (one seed per line), at most `max_jobs` at a time, each under `job_timeout_s`, an optional stopping rule and compute ceiling, `SUMMARY.json` with counts |
| `lean/InverterInstanceCheck.lean`, `lean/check.sh` | the Mathlib-free premises over `Rat`, the checker and its soundness, `InverterRead` on both observed reads |

Read unchanged from `research/circuit`: `blocks.spice`, `spiceinit.txt` (the ngspice setup), `noise.json`, `pdk/`
(`fetch_pdk.sh`). Lean modules imported from `research/learned-coincidence`: `InverterTarget` and its imports.

    python -m invinst.driver JOBS OUTDIR [--stop RULE.json] [--section tt]      # from this folder

**Runs.**
- R1: input absent.
- R2: input present.
- R3, R4: leak above and below rest.
- R5: an ideal slow ramp of the main node through the FIRE level, for the static threshold.

Each log records a fingerprint: the bias of the comparator, and the vth of the comparator pair and of the two mirrors.
An instance whose runs do not share one sample is refused.

**Gate.**
- K0 (eligibility): the measured values, outward rounded.
- K3 (room): K0 plus 3 sigma of the frozen cell's noise. The FIRE comparator's input noise is added to δ. The shot
  charge of the two mirrors over the slot is added to each budget and taken from Q.
- Usable: eligible, and with room, counted separately. Each also needs the observations: one sample, silent with the
  input present, firing with it absent.

**The premises**
- They follow the two-leak theorems `inhibited_silence_leaks` and `uninhibited_first_crossing_leaks`, as stated to me by the
  inverter session: their file is on its local branch `proof/inverter-tolerances`, not read here.
- The reference leak `a′` is the midpoint of the two measured sides. `α` is half their gap, and `L = D·H0·hl`.
- The reference is evaluated in closed form, with the exponential between its degree-5 and degree-6 Taylor polynomials.

## Open, not gated

- **The ℝ bridge.** The Rat premises imply the real `before`/`after` hypotheses: closed form and monotonicity of the
  box reference, and the two Taylor bounds. These lemmas are not written.
- **One leak constant.** The theorems take one actual leak `a`. The cell's leak differs on the two sides of rest. The
  gate only requires both sides to lie in `[a′ − α, a′ + α]`.
- **The latch delay** is a measured constant of each instance, not a proved bound.
- **The front end.** The direct-rail delay tolerance (`InverterLag.lean`), and `window + ε ≤ skew` and
  `emitLate − emitEarly ≤ skew`, involve the first layer's skew. They belong to the network stage; this package
  reports the window, the emission spread and the slot duration.
- **Campaign dates.** `window = 1/4`, `emitEarly = 2/5` and `emitLate = 13/20` are development choices.
