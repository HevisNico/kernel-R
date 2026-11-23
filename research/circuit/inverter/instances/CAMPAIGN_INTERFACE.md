# The inverter campaign kit: one entry, and what stage D reads

**Development work, plan step 5 (CAMPAIGN_PLAN_DRAFT.md, research/layered-networks 8af2cba).** Nothing here is
frozen or preregistered.

## The entry

```
python -m invinst.campaign OUTDIR --seeds S1,S2,...      # or --seeds-file FILE (one seed per line, # comments)
       [--config config.json] [--netopts config_netopts.json]
```

From Python, with this package's folder on `sys.path`:

```
from invinst import campaign
campaign.run(seeds, outdir)        # returns OUTDIR/INVERTERS.json
recs = campaign.load(outdir)       # checks every SHA256SUMS line first; returns {seed: record}
```

- Ngspice 42 and Lean (`lake` on PATH) are needed. The Lean library is built once per OUTDIR, in `OUTDIR/lean_build`.
- What it runs:
  - It runs `invinst/driver2.py` unchanged. Each seed is measured at the network's directives (`config_netopts.json`)
    with the C5 cell of `config.json`, then gated at K0, K3 and StateBound.
  - The jobs run 4 at a time, each under a 1800 s timeout (`config.json` → `driver`).
- **There is no stopping rule.** Every listed seed is run. A failed or timed-out job is counted under its first failing
  clause; it is never dropped and never re-run.

## OUTDIR

| File | Content |
|---|---|
| `JOBS` | the seeds, one per line, in the given order |
| `CAMPAIGN_INPUT.json` | the seeds; sha256 of the two configs, of every `invinst/*.py` and `lean/*` file, and of `research/circuit/lean/CircuitInverterGate.lean`; the ngspice version line; git HEAD; `package_tree_clean` |
| `SUMMARY.json`, `status/`, `runs/<seed>/`, `gates/` | driver2's own outputs: the decks, logs, traces and MEASURE.json; the gate JSON and the Lean files |
| **`INVERTERS.json`** | **the file stage D reads** (below) |
| `records/INVERTER_<seed>.json` | the same records, one per file |
| `SHA256SUMS` | every file in OUTDIR except `lean_build/` and itself |

## INVERTERS.json

Its top level holds:
- `schema`, which is `"inverter-campaign/1"`;
- `verdict_status` and `open_premises`;
- `input` and `input_sha256`;
- the counts `n`, `n_ok`, `k_eligible_K0` and `k_room_K3`;
- `machine_minutes_jobs` and `wall_minutes`;
- `records`, one per seed, in JOBS order.

### Fields stage D reads, per record

| Field | Meaning |
|---|---|
| `seed` | the mismatch seed (`setseed SEED`, section `tt_mm`) |
| `status` | `ok`, `failed`, `timeout` (driver2's job status) or `missing` |
| **`eligible_K0`** | the instance has a prediction. The K0 gate holds in the Lean kernel, all three observations hold, and StateBound is **measured** and holds |
| **`room_K3`** | `eligible_K0`, and the K3 gate holds in the kernel; the instance may be predicted under noise |
| `first_failing_K0`, `first_failing_K3` | `null`, or the first failing clause in this order: `run_failed` / `run_timeout` / `run_missing` / `run_no_gate`, `not_measured`, `observed:<name>`, `StateBound:not_measured`, `StateBound`, `kernel:no_verdict`, `kernel:<premise>` (Order, SilenceBefore, SilenceAfter, FiringBefore, FiringAfter, Timing), `FrontEndFits` |
| `measures.K0`, `measures.K3` | the gate's rationals, as strings: `aLo`, `aHi`, `aRef`, `alpha`, `eps0`, `etaH`, `etaM`, `etaJ`, `delta`, `Q`, `latchLo`, `latchHi`, `emit`, `early` |
| `allowance` | `K0` and `K3` allowances, each with `delta` and `eta` |
| `timing` | `window`, `emitEarly` and `emitLate` |
| `state_bound` | `xPresent`, `xAbsent`, `limit` (27/20), `verdict`, `absent_on_whole_slot` |
| `files.gate`, `files.lean`, `files.measure` | paths relative to OUTDIR (the Lean file is the one the kernel accepted) |
| `sha256.gate`, `sha256.lean`, `sha256.measure` | the hashes of those files, for the prediction record |
| `fingerprint` | `names` (`sim.FINGER`: v(ibm) and the vth of key devices) and the R1 `values` |

### Fields for the report only

- `gate_eligible_K0` and `gate_room_K3`: the gate's own verdicts. The gate counts an unmeasured StateBound as not
  failing, but the campaign does not. A record is never looser than the gate; this is asserted.
- `kernel`, `kernel_agrees_with_mirror`, `observed`, `margins`, `front_end_fits`, `machine_s` and `values` (floats).

### Not checked here

`front_end_fits` is `"not checked"`, because `config.json` sets no front-end skew or epsilon. The window and spread
fit of the network's front end (`FrontEndFits`) belongs to the network pipeline.

## Open point, for the network pipeline to decide: the physical identity

- The plan's stage D wants each instance's cells to be physically the same in stage D and stage N.
- **This kit measures the inverter in its own deck, at `setseed SEED`. The network deck draws its whole netlist at
  `setseed SEED` (layered-networks `session.py`).**
- So the in-network inverter's devices very likely get different draws from this kit's inverter at the same seed
  [I: the draws follow the netlist's device order; not tested here].
- As built, a record is therefore a gate on an independent draw of the C5 cell, not on the network's inverter.
- The `fingerprint` field is there to settle this per instance. Stage D can print the same quantities in the network
  deck and compare them, with a tolerance of 1e-4 V (`fingerprint_tol_V`).
- If they differ, these records must not be used as the network inverter's anchors. The alternative is to measure the
  inverter inside the network deck, which is not built here.

## Cost

- At netopts (reltol 1e-5) it costs about 72–75 s of CPU per instance. This is 5 runs plus the gate, measured on lot 2
  (60 instances) and on the smoke test.
- The Lean library build adds about 1.5 min once per OUTDIR.
- Disk: about 4.8 MB per instance, mostly traces.
