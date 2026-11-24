# Stage-N controls (plan step 2): S, U and the duplicate run

**Development only, nothing preregistered.** Dev seeds 9801 (NOT1) and 9803 (XOR3, C5 overlay) only.
- New files: `controls2.py`, `tests/check_duplicate.py`. No pushed file changed.
- The formats were agreed with the campaign-pipeline driver session (stage D, `campaign_run.py`).

## Formats

| Control | Where | Record | Holds iff |
|---|---|---|---|
| **S, skew** | inside the stage-N run, after the 2^m tests: one slot per both cell, in spec order, in the noiseless and the noisy runs (`controls2.py stagen SPEC OUT SEED ROUND [overlay=…]`) | `OUT/noisy_record.json`. Slot `kind` "skew", `info` {cell "c<k>_<i>", layer, index, shift_tu "2", late_port 2}, one read (start, arrivals [a1, a2], latch, emission, second) and u. Top-level `skews`: the slot indices | the read's emission is null |
| **U, untrained** | a fresh session of the same deck and seed: the 2^m test slots only, from the preset, with no lesson and every R cell gated (`controls2.py untrained SPEC OUT SEED [overlay=…]`) | `OUT/untrained_record.json`, in noise2's layout, with `control` "U". Slots `kind` "test" with info.pattern | no R-cell read of any test has an emission. Inverter emissions are expected and reported |
| **Duplicate** | the instance's noiseless stage N rerun in a fresh OUT on a second machine | `tests/check_duplicate.py A B`, exit 0 iff identical | see below |

- **Skew slot.** All gates are closed. Both ports are pulsed at the gate's amplitude: port 1 as a routed pulse at the
  read start + δ, and port 2 **2 tu later**. That is campaigns 4–6's skewed coincidence (research/learned-dnf-circuit
  dnf.py: "the second input 2 units late"). Nothing is routed past the cell.
- `controls2.py verdicts OUT` gives the S and U verdicts.
- Every run writes **`OUT/trace.raw`** at its end (ngspice `write`: the saved vectors over the whole session).

### The duplicate criterion, fixed now

It is matched to campaign (a): PREDICTION.md §6 compares `input_spice`, `record`, `result`, `noise_sha256` and
`trace_raw`, with **trace.raw compared with its `Date:` header line excluded**.

1. `input.spice` byte-identical.
2. The records (`record.json`, `noisy_record.json`, `untrained_record.json`) and the verdict files
   (`*.verdict.json`, and the pipeline's `comparison.json`) identical after removing, at any depth, `cost`, `wall_s`,
   `cpu_s` and keys ending in `_wall_s` or `_cpu_s`.
3. **`trace.raw`**: the text header line by line with its one `Date:` line excluded, then the data byte for byte.
4. **`session.log`** (ngspice's whole pipe output: every command, answer and printed vector value): identical except
   the lines `" Reference value :  <t>"`.
   - These are ngspice's progress lines during a transient. Their number and their times differ between identical
     runs on the same machine: 305 against 304, and 285 against 286.
   - So they are printed on a wall-clock timer [I, from that evidence].
   - The number of excluded lines is reported, and any other differing line is listed.
5. The run logs (`*.log` beside the folder) are not compared.

**Every exclusion is listed above; nothing else is excluded.** In the runs here, no other line differed.

## Results

| Check | Instance | Result |
|---|---|---|
| Stage N noiseless = the pushed no-noise path | NOT1 9801 | all 6 training and test slots equal to dev/cal5_not1 |
| | XOR3 9803 | all 27 training and test slots equal to dev/cal6_xor3; the same words |
| **S, noiseless** | XOR3 9803 | **holds**: c1_0 and c1_1 silent with the second input 2 tu late |
| **S, noisy (round 1, noise seed 98031)** | XOR3 9803 | **holds**: both silent. **This is the XOR3 noise path's first run**: it completed, with words equal to the noiseless run (`ssFF`, `ssFF`, `sssFF` ×3) and all 4 outputs correct |
| S, positive check (shift 0, development only, `positive=1`: kind `skew_check`, counted for nothing) | XOR3 9803 | the same two slots with **coincident** inputs: **c1_0 and c1_1 both FIRE** (latches at +17.8 and +15.3 µs). So the 2 tu skew discriminates: S is not silent by construction. The first 29 slots of that run (training, tests, skews) equal the plain noiseless run's |
| **U** | NOT1 9801 | **holds**: no R output on either pattern; the inverter fired once (its input absent) |
| | XOR3 9803 | **holds**: no R output on any of the 4 patterns; 4 inverter emissions (on the absent inputs) |
| **Duplicate**, the full criterion | NOT1 9801, two runs on one machine | **identical**: input.spice; noisy_record.json (cost removed); trace.raw 14.7 MB, data identical, `Date:` the only excluded line; session.log identical with 285 and 286 progress lines excluded |
| Duplicate, negative control | NOT1 | a 1 nV change in one stored voltage → "DIFFERS at /slots[3]/u/c1_0[0]", exit 1. A changed wall time alone → identical |

**What is not shown here.** Identity across two **different machines** cannot be run in this container. The campaign's
rehearsal does that (CAMPAIGN_PLAN_DRAFT.md §10).

## Cost (CPU minutes)

| | NOT1 | XOR3 |
|---|---|---|
| stage N noiseless with skew slots | 1.5 | 42.2 (the 2 skew slots add about 0.5 to 41.7) |
| stage N noisy (round 1) | — | **55.4** (×1.31; the plan's estimate was about 60) |
| U | 0.45 | 3.0 |
| trace.raw size | 14.7 MB | **1.67 GB** |

- Validation in all: about 2.6 CPU-hours.
- **trace.raw is large: 1.67 GB per XOR3 run.** Each run therefore also writes `trace.digest.json`, with the size,
  the sha256 of the header without its `Date:` line, and the sha256 of the data.
  - The duplicate check compares the raw files when both are present, and otherwise the digests. Checked: a NOT1 run
    whose trace.raw was removed is identical by digest to its duplicate.
  - So a campaign machine can delete each trace after its digest is written. At 66 XOR3 instances, keeping the raws
    would take about 110 GB per group.
  - trace.raw is not committed. The digests are.
- **The ngspice convergence line.** "doAnalyses: Too many iterations without convergence" appears in session.log in
  every run, in both duplicates identically. It is not excluded, and it is counted per run by
  CAMPAIGN_PLAN_DRAFT.md §9.
