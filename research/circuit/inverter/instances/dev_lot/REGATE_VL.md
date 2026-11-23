# The development lot, re-gated with the varying-leak state bound

**Development work, not preregistered.** This file is separate from `RESULT.md`, which is the lot's own record and
is unchanged.

## What was done

- The 60 instances of the lot (`RESULT.md`, commit 96b867b) were gated again from their existing `MEASURE.json` and
  their kept traces. Nothing was simulated again.
- The gate adds one premise, `StateBound` (`lean/InverterInstanceCheck.lean`). It is the measured state bound of
  the varying-leak theorems, as the inverter session stated it (proof/inverter-bridge, local 8e1cd192, not read here):
  - max |x| over the slot, input present (R2, on `[0, D]`), is at most `H0 · hl` = 27/20;
  - max |x| over the slot, input absent (R1, on `[0, h + hl]`, the firing theorem's interval), is at most `H0 · hl`.
  - Both are rounded up to 10^-6.
- With it, the varying-leak term `α · X · D` equals the gate's `leakTerm`, so the margins are unchanged. The kernel
  agreed with the mirror on all 60. It took 155 s for the 60, Lean included.
- Taking the absent run over the whole slot `[0, D]` changes no verdict: its maximum is 1.3643, against 1.3639 on
  `[0, h + hl]`.

## Counts

| | 96b867b (lot) | re-gated |
|---|---|---|
| eligible (K0) | 60 / 60 | **59 / 60** |
| with room (K3) | 59 / 60 | **58 / 60** |

## Change per instance

| Seed | Lot (K0, K3) | Re-gated (K0, K3) | Cause |
|---|---|---|---|
| 9944 | true, true | **false, false** | StateBound: max \|x\| with the input absent is 1.363867 > 1.35 (ηH 0.197, the lot's largest help error). Its silence margin was 0.0032 at K3 |

Every other instance keeps its verdicts. 9928 still fails room on SilenceAfter, and its max \|x\| absent is 1.34755,
just under the bound.

## X distribution (min, median, max over 60)

| | min | median | max |
|---|---|---|---|
| X present, `[0, D]` | 0.8246 | 0.8728 | 0.9193 |
| X absent, `[0, h + hl]` | 1.1310 | 1.2406 | 1.3639 |
| X absent, `[0, D]` | 1.1314 | 1.2410 | 1.3643 |

The bound 1.35 is binding only for the input absent, and only in the help-error tail: 9944 at 1.3639, 9928 at
1.3476, 9963 at 1.3193.

Every verdict stays conditional on the open premises in `REGATE_VL_SUMMARY.json`:
- the leak along the trajectory is a modelling step [I];
- the bridge is reported proved but not read here;
- the latch is measured, not bounded.
