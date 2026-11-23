# Stage D: the per-cell measures before the network run, the sealed prediction, the comparator

**Development only, nothing frozen.** Plan step 2 of CAMPAIGN_PLAN_DRAFT.md §2. Three new files; no pushed file is
changed.

| File | Role |
|---|---|
| `stage_d.py` | the stage-D session, the fit and gates, the prediction (`run`, `predict`, `seal`, `verify`) |
| `seal.py` | the sealed record: one canonical file per instance, `MANIFEST.json`, `SHA256SUMS` |
| `compare_d.py` | the direct comparison of one stage-N record with the sealed prediction |
| `tests/test_stage_d.py` | tests without simulation |

## Commands

```
python3 -B stage_d.py run SPEC OUT SEED [overlay=config_inverter_c5.json|overlay=none] [inverters=FILE|inverters=assumed] [solo=1]
python3 -B stage_d.py predict SPEC OUT [inverters=...]       # again from OUT/record.json, no simulation
python3 -B stage_d.py seal SEALDIR OUT [OUT ...]             # refuses an existing SEALDIR
python3 -B stage_d.py verify SEALDIR                         # or: cd SEALDIR && sha256sum -c SHA256SUMS
python3 -B compare_d.py SEALDIR SPEC STAGE_N_OUT [auto|noiseless|noisy] [OUT.json]
python3 -B tests/test_stage_d.py
```

## The session (`stage_d.py run`)

- The deck of `instrument.CalNetwork` (design point, junction areas, per-port leaks), the instance's mismatch seed,
  and the config overlay (default C5, `overlay=none` for config.json as pushed).
- No routing. Every R cell is driven by ideal pulses on its own ports, at its gate's amplitude, at T + delta. All cells
  share the slots, but no cell's pulses reach another cell. The inverters are idle.
- In the family's order (each cell's groups g0 then g1):
  1. **Training ascent from the preset.** Write gate open. Each group stops after `hold` = 2 FIREs in a row, or after
     10 rounds. This gives the stage-D words.
  2. **Mask reads, read-only, at the settled state.** One read per non-empty mask. This gives the cell's observed
     table and its read calibration.
  3. **Scans.** `instrument.scan_all` unchanged: bisection from the ascent's bracket, with both-direction repeats. The
     record is then loaded under repeat rule v2 (`records2.py`).
- **D4.** The cells share slots, so D4 is bounded as in the in-situ runs: by `d4_stage` (0.005), or by `solo=1`, which
  gives the run's own solo scans (the plan's D4 audit).
- **The fit.** `fit.cell_fit` unchanged, on a per-cell view of the record (`stage_d.cell_view`).
- **Eligible at K0**: every cell is measured and its K0 verdict holds, and with a front end every inverter's K0 gate
  holds. The K0 verdict covers Cell.Valid, the stage-D word equal to the model's stop, and the training and read
  calibrations.
- **Room at K3**: the same at K3.

## The inverter gate: an interface to confirm with the inverter kit

`inverters=FILE`, JSON: `{"kit_commit": "...", "inverters": {"n0": {"K0": bool, "K3": bool, ...}, ...}}`.

- Without it, an instance with a front end has **no prediction** ("inverter gate not measured").
- `inverters=assumed` is for development only. It is written into the prediction (`inverter_gate.source`), into the
  manifest, and into every comparison.

## The prediction record (`OUT/prediction.json`, sealed as `<TAG>_<seed>.json`)

- **Canonical JSON**: sorted keys, no spaces, ASCII, one trailing newline, exact rationals as strings.
- **Excluded**: dates, hosts, paths and costs. Costs go to `OUT/cost_d.json`, which is not sealed.
- **Fields**:
  - `tag`, `seed`, `status`;
  - the spec's and the overlay's sha256, and the sha256 of every code file (`CODE`);
  - `record_core_sha256`: the stage-D record without `cost` and the scans' `wall_s`;
  - the inverter gate;
  - per cell: measured or not and why, `need`, `maxWrites`, ε, anchors, the guarded tuple, the Lean cell at K0 and
    K3, and the verdicts with their failing clauses;
  - `eligible_K0`, `room_K3`, `applies` {noiseless, noisy}.
- **`prediction`** exists only when the instance is eligible at K0. It holds:
  - `words`: every training word, asserted to be `need` letters `s` and then `hold` letters `F`;
  - `cells` and `outputs` per pattern code: the observed tables composed through the layers, with each inverter
    firing exactly on its absent input;
  - `skew_silent`: the both cells.
- `stage_d_observed_not_a_prediction` keeps the stage-D words and tables for every instance. As the name says, it is
  not a prediction and the comparator does not read it.

## The comparator (`compare_d.py`)

- The seal is verified first. The stage-N record's tag and seed select the instance.
- The run's kind is read from the record's `noise` entry: noisy if b, w or d is non-zero. The field names are
  provisional and still to be confirmed with the noise module. A kind given on the command line that contradicts the
  record is refused.
- **Compared only where a prediction applies**: eligible at K0 without noise, room at K3 with noise. The comparison
  covers every letter, every cell FIRE bit, every output, and every both cell in a `skew` slot. Any difference gives
  `refuted`, with the differences listed. Otherwise the verdict is `agrees`.
- **Elsewhere**: `observed only (no prediction)`, with the reason. The observed words and outputs are shown and
  nothing is compared.
