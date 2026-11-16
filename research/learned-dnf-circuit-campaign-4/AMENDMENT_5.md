# Campaign 4, amendment 5: the stages' protocols, the time limits, the extraction costs, and what the smoke runs showed

Pushed alone on `research/learned-dnf-circuit-campaign-4`, after `PREDICTION.md` (commit `1596b36`) and amendments
1 to 4 (commits `c14124f`, `d6a75a9`, `41cf88b`, `a167f3c`), before the implementation is frozen. It is the owner's
decision. Nothing else in `PREDICTION.md` or amendments 1 to 4 changes.

**No campaign seed (7501 and up) has been simulated, and nothing here depends on campaign-4 data or on any result of
the noise study's validation.** Every run below is on the nominal cell (model section `tt`, no mismatch, no seed).

## 1. The protocol of each stage

The launch kit claims a machine once per protocol file: its claim is the branch
`owner-launch/protocol-<SHA-256 of the protocol file>/<machine>` (`launch.py`, `claim_ref`), and a second launch on a
machine under the same protocol file is refused. `PREDICTION.md` (Execution, Launcher) has M and E1, E2, ... share
`PREDICTION.md` as their protocol, and Q, N1, N2 and N3 share `PREDICTED.json`; with the kit unchanged, only M and Q
could launch. So, the kit unchanged:

1. **Each stage has its own protocol file**, `research/learned-dnf-circuit-campaign-4/STAGE_<name>.md` (M or M1, M2;
   E1, E2, ...; Q; N1; N2; N3), written by the frozen code and pushed alone before the stage's launch. It names the
   stage and its **governing protocol**: `PREDICTION.md` for M and E, `PREDICTED.json` for Q and N1 to N3, with that
   file's commit and SHA-256. `PREDICTION.md`'s "with this file as their protocol" and "with `PREDICTED.json` as their
   protocol" now mean: with a stage file naming this file, or `PREDICTED.json`, as its governing protocol.
2. **Safeguard (i).** At launch, the frozen runner (`run4.py`) checks that the governing protocol in the repository
   still has the SHA-256 written in its stage file, and refuses the run otherwise, before any simulation.
3. **Safeguard (ii).** Each stage's source commit differs from the frozen implementation commit in no frozen file
   (the list sent at the freeze, byte for byte). Every other file in which it differs is one of: the stage files
   and their run lists; the records written by the frozen code (`BEFORE_M.md`, `MEASURED.json`, `PREDICTED.json`,
   the merged extractions, the Lean file of the kernel gate, `REHEARSAL.json`); the inventories; the manifests and
   attempt markers of the stages; and the evidence of the earlier stages. No file outside
   `research/learned-dnf-circuit-campaign-4/` differs: the launch kit, the theory modules and the noise study's code
   stay as at the frozen commit. The frozen code checks this when it writes a stage's manifest and refuses
   otherwise. CI must be green on that exact commit.
4. The same applies to the rehearsal, in its local clone.

## 2. The time limits

This states `PREDICTION.md` (Execution, Time limits: 1.3 times the wall time measured in the rehearsal, scaled to the
stages, slots and pulses of each run, and never above 1.3 times the measured cost model) as a computation:

1. **The run kinds**: calibration deck; extraction run with the trip value reused; extraction run without it; run
   without noise; untrained control run; noisy run under the device model; noisy run under the injected model.
2. **The ratio of a run kind** is the largest, over the rehearsal's runs of that kind, of the run's wall time
   recorded by the launch kit divided by its expected cost under the cost model. It is recorded in `REHEARSAL.json`.
3. **The estimate of a run** is that ratio times the run's expected cost.
4. **The time limit of a run** is 1.3 times its estimate, **rounded up to the next 10 s**, then **capped at 1.3 times
   its expected cost**, so that the rounding cannot exceed the cap.
5. The kit's estimate of a run is the smaller of its estimate rounded up to 10 s and its time limit. Before the
   rehearsal (to size `I`), the time limit is 1.3 times the expected cost, capped in the same way.

The expected cost is that of the cost model of `PREDICTION.md` (Execution, Cost model), with the costs of
`BEFORE_M.md` (section 4); it alone sizes `I` and the expected compute.

## 3. The stage caps

The stage caps are **recomputed by the frozen code** from the costs of `BEFORE_M.md` and the time limits of section 2,
with the formula of `PREDICTION.md` (Execution, Stages and manifests: for each machine, the sum of its runs' time
limits plus 10 s over the four runs at a time, plus the largest of them; the two machines added), and **recorded in
`BEFORE_M.md`**, as `PREDICTION.md` says (its opening paragraph, and The record before stage M). The figures that
`PREDICTION.md` gives (M 7 881 s, E1 10 658 s, Q 4 558 s, N1 to N3 5 412 s) are those of the costs known when it was
pushed; with the cap of section 2, the frozen code gives the same figures on those costs.

## 4. The extraction costs

Whether the trip value is reused is known only with the noise study's identity check, and is recorded in
`BEFORE_M.md` (`PREDICTION.md`, Noise-model extraction). The smoke runs of section 7 measured the extraction without
the trip value reused at about 2 400 to 2 900 s per cell, against the 1 200 s per cell of the cost model, which
assumes it reused; with those costs, every `window` and `fire` run without reuse would exceed its time limit.

So **the extraction costs of `BEFORE_M.md` are those of the setting that applies, as the validation report gives
them; if it gives none for that setting, they are the rehearsal's measured costs for that setting.** `I` and the
split of the E stages are recomputed from them by the existing rules of `PREDICTION.md` (Execution); `I` can only go
down.

## 5. The extraction in the rehearsal

The rehearsal runs the extraction **with the trip value reused**: its per-output runs, the single-run extraction, the
identity check of the two, and their wall times.

**If, and only if, the trip value is not reused** (it is reused only if the noise study's identity check passes,
`PREDICTION.md`, Noise-model extraction; so also if the validation report gives no result of that check), the
extraction without it is rehearsed as a **declared supplement to the rehearsal**, before `BEFORE_M.md`: its per-output runs, its single-run
extraction (alone in its stage), the identity check of the two, and their wall times. These are measurement-only
runs: their time limits are 3 times their expected cost, and they set the ratio of the run kind "extraction run
without the trip value reused" (section 2). The supplement is recorded in `REHEARSAL.json`, with its reason.

**Every run of the rehearsal is a measurement**, not a campaign run: its time limit is 3 times its expected cost,
and the rehearsal's stages are cut so that each fits the kit's bound of 14 400 s. The time limits of section 2 apply
to the campaign's runs.

## 6. What the smoke run showed for M8 and M7, and what will be reported

On the nominal cell's run without noise (section 7), read by the analysis's M8 code with the instance's guarded
tuple:

- **M8.** `PREDICTION.md` (M8) scores a read that fires by the larger of its peak before the FIRE crossing and
  `theta`. The guard stops the charge at the FIRE, so that score is about `theta`, below the guarded score at the
  need by about 3 000 units, against budgets of about 800. So **the residual of every firing read fails, and so do
  c's anchors and the submask comparison of its pair**. The simulator places each routed pulse on its 0.02-unit grid
  (`net.snap` of `research/network-circuit/net.py`), so **exact route equality fails on every routed read**.
  `PREDICTION.md` expected these parts of the check to be nearly empty; they fail. No rule of M8 changes: M8 refutes
  nothing, its results are reported as they are, and each is reported with these two reasons beside it.
- **M7.** The model gives the spread of the stored voltage (`sigma`), not of the FIRE latency. M7 reports the
  latency spread alone, and says so.

## 7. The smoke runs before the freeze (2026-11-16)

Debugging runs of the unfrozen implementation, with the pinned interpreter, ngspice and PDK; none is the rehearsal.
Wall times and peak memory as each run recorded them.

| Started (UTC) | Run | Where | Wall time | Peak memory |
|---|---|---|---|---|
| 15:44 | calibration deck, guard on | outside the kit, four at a time | 588 s | 567 MB |
| 15:44 | calibration deck, guard off | idem | 449 s | 519 MB |
| 15:44 | run without noise, need 4, with the skew control | idem | 672 s | 568 MB |
| 15:44 | untrained control run | idem | 142 s | 363 MB |
| 15:59 to 16:36 | the 21 per-output extraction runs, trip value not reused | outside the kit, four at a time (a fifth process for part of the time) | hold 120 to 209 s, pulse 120 to 169 s, window 595 to 825 s, fire 590 to 799 s | |
| 16:04 | a real launch of the kit (synthetic kind, local remote): the untrained control run on machine a; on machine b, a calibration deck with seed 7510 and `I = 9` | the kit | 137 s; seed 7510 refused by `run4.py`'s seed guard before any deck was written | |
| 16:07 | noisy run, injected model, need 4, round 1 | outside the kit, beside four extraction runs | 1 120 s | 818 MB |
| 16:37 | noisy run, device model (75 sources from the merged extraction), need 4, round 1 | outside the kit, alone | 740 s | 618 MB |

They showed:

- the words and outputs of the run without noise equal to its zero-error predictions, the skew slots silent, H and G
  without a failure, the untrained run silent on every pattern;
- the merged extraction passing V2, V2b and the 1 µV isolation check (operating points within 5 pV), and equal byte
  for byte to an independent merge;
- the extraction's cost without the trip value reused (section 4);
- the analysis reproducing `PREDICTED.json` and the merged extraction byte for byte from the evidence, the device
  run's samples regenerated to their recorded SHA-256, every record equal to its files.

The defects they found were fixed before the freeze (commits `618507c` and `395b9b5` on the work branch): the
nominal cell's merged extraction recorded the model section `tt_mm` in place of `tt`, the prediction step read
`BEFORE_M.md` from the code's folder in place of the repository it writes to, and the regeneration check wrote its
samples into the collected evidence. The one-launch-per-protocol rule of the kit (section 1) was found while the
rehearsal was being planned, not by a run.
