# The development lot, re-gated against the single-source gate module

**Development work, not preregistered.** `RESULT.md` and `REGATE_VL.md` are unchanged.

## What was done

- The per-instance gate files now import `research/circuit/lean/CircuitInverterGate.lean`, namespace
  `KernelR.Circuit.Gate`. It is the single source of the gate's definitions, which the Mathlib bridge also imports.
  - The file was taken byte-identical from `proof/inverter-bridge` at 13aba3a (sha256 `ffb51672…74b0ee`, checked by
    `lean/check.sh`).
  - The package's own copy, `InverterInstanceCheck.lean`, is retired.
  - The abstract layer (`Timing`, `Premises`, `check`, `FrontEndFits`, `inverterRead_of_premises`) is in
    `lean/InverterInstanceTiming.lean`. It imports the module and `InverterTarget`, and restates none of the
    module's definitions.
- The 60 lot instances were gated again from their existing `MEASURE.json` and kept traces. Nothing was simulated
  again. It took 83 s.

## Result

- **Eligible (K0): 59 / 60. With room (K3): 58 / 60.** This is identical, instance by instance, to `REGATE_VL.md`
  (d952021): the same verdicts, the same kernel verdicts and the same margins.
- The kernel agreed with the mirror on 60 / 60.
- The failures are unchanged:
  - 9944 fails both (StateBound);
  - 9928 fails room (SilenceAfter at K3).
- **Negative control:** asserting `StateBound` true for 9944 makes the file fail to compile.

Every verdict stays conditional on the open premises listed in `REGATE_SINGLE_SOURCE_SUMMARY.json`.
