# Combined campaign: preregistration note 2 (2026-11-28): the campaign is withdrawn before its draw

This note records the stopping point of the combined campaign. It is pushed alone. `PREDICTION.md` (commit `321284af`) and preregistration note 1 (`0e15bb14`) are left unchanged, as the record of what was preregistered; the campaign they describe is withdrawn and will not be run under them. No seed of the campaign was drawn: the announce branch `evidence/combined-draw` was never created.

The text below is the stopping-point note published at the top of pull request #190 on 2026-11-28, reproduced here so that it stays with the files.

## Stopping point — 28 November 2026

The preregistered combined campaign is withdrawn before its official draw. The results below come from rehearsal 1.

Of the six XOR3 instances in the rehearsal, four received a prediction at K0. Two followed the predicted trajectory. On the other two, 27735 and 88529, one learning word contained an extra silent round: `ssFF` was predicted, `sssFF` was observed. The first `F` arrived one round later. In both cases, the final truth table was the predicted one. The preregistered rule covered the complete trajectory, so both instances are refuted at K0. For 27735, the duplicate on another computer reproduced the deviation exactly. [Rehearsal 1 analysis](https://github.com/HevisNico/kernel-R/tree/4fd58425/OUT1)

An exploratory replay examined the third reading. On each of the two isolated cells, two simultaneous inputs at 12 µs gave `F`. At the times tested, spreading the inputs 1.6 µs apart, while keeping the same mean arrival time and the port order observed in the network, was enough to reproduce the `s`. The two control cells gave `F` in all three conditions. [XOR replay report](https://github.com/HevisNico/kernel-R/blob/9618a665/research/layered-networks/dev/rehearsal1/replay/REPLAY_REPORT.md)

The preregistration, its note 1, the freeze `5d02acce` and the rehearsal 1 branches remain accessible in their original state. The NOT1 and ANDOR3 groups are postponed together with the combined campaign. The next step will start with XOR and will be the subject of a new preregistration. All seeds already used will remain excluded from new validation draws. An inventory of the local work, with the lots kept and the corresponding commits, is given below; every archive was verified before it was listed. [Preregistration](https://github.com/HevisNico/kernel-R/blob/321284af/research/layered-networks/PREDICTION.md) · [Note 1](https://github.com/HevisNico/kernel-R/blob/0e15bb14/research/layered-networks/PREDICTION_NOTE_1.md) · [Original freeze](https://github.com/HevisNico/kernel-R/tree/5d02acce)

### Next question — XOR

Before running a new XOR network, for which two-port readings can `F` or `s` be predicted from the cell's measurements and the arrival times expected upstream?

Before each simulation, we will record, for each targeted reading, the expected arrival range and the announced answer (`F`, `s` or abstention). The report will state separately whether the inputs arrived within the expected range and whether the announced symbol was right. Any arrival outside the range will remain visible, even when the symbol is correct.

The abstention rule, the success thresholds and the denominators will be fixed before the new seeds are drawn. The report will give three measures:

* **Coverage** — readings that received a prediction / targeted two-port readings.
* **Accuracy** — correct predictions / predictions issued.
* **Per-network agreement** — networks in which every announced symbol was checked and is correct / networks that received at least one prediction. The report will also give the number of networks entirely in abstention.

The two refuted cases and their controls will serve to develop the method. Its validation will be on new seeds.

### Inventory of local work archived at the stop

Every lot below is on its own branch under `archive/combined-campaign-stop/`, each with a `FICHE.md` (provenance, state of each item, how to recover it) and a `SHA256SUMS`. Every commit carries the owner's identity. Each lot was **pushed** by the session that held it, then **verified** by an independent audit session that fetched it by name into a fresh repository.

**What "verified" means here** (so as not to overstate it):
- For every lot: the archive can be fetched, its checksums match, and its fiche is present.
- Git bundles reopened on their base revisions: `K02`, `checker`, `test-writer`, `stage-d`.
- Re-run by the audit: only the test writer's 90 cases at `7fa3693e` (90/90), and the reconstruction of the three raw traces, matched against the `trace.digest.json` files of the published rehearsal 1 roots.
- Checked by checksum against a published reference: the six XOR replay raw traces in `stage-d`, against `dev/rehearsal1/replay/runs/RAW_SHA256SUMS.txt` at `9618a665`.
- Recomputed from the archived files: the implementer's results table.
- Not re-run: the implementer's and checker's suites, the review scripts, and anything that needs Lean, ngspice or the GitHub API.

| Branch | Pushed at | Verified | Contents |
|---|---|---|---|
| `coordinator` | `2bd6f517` | yes | coordinator's notes and the amendment 1 draft (**not adopted**) |
| `implementer` | `7e4c1129` | yes | run outputs and drafts; dev stays at `7fa3693e` (never frozen; full (c) and proof2 not run on it) |
| `checker` | `63ce50c7` | yes | reviews 1–4, review scripts and outputs, rescan records, one unpushed commit (bundle) |
| `test-writer` | `2ca8267f` | yes, 90/90 re-run | independent black-box tests (bundle of 59 local commits), the test file at each run, run records, helper scripts |
| `stage-d` | `104415a0` → `2849a10c` | yes | stage-D drafts and branches (4 bundles), scratch files, inventory of what was not copied; the six XOR replay raw traces (`r_27735_case1..3`, `r_88529_case1..3`), checked against their published sha256 |
| `K02` | `db9aa438` | yes | K02 runner drafts (bundle), rescan and suite records |
| `raw-K01` | `55a97416` | yes, digest matched | rehearsal 1 `XOR3_88529` N0 trace.raw (refuted at K0), 32 parts |
| `raw-K04` | `e1777bc1` | yes, digest matched | rehearsal 1 `XOR3_29179` N0 trace.raw (no K0 prediction), 37 parts |
| `raw-K07` | `d29b3814` | yes, digest matched | rehearsal 1 `XOR3_70285` N0 trace.raw (no K0 prediction), 34 parts |
| `K01-local` … `K12-local` | `57edfa54`, `05f7a48e`, `ed8dd24c`, `4a581e7e`, `dade3504`, `663f61cb`, `5236acfe`, `bf2aa887`, `b0adbc57`, `a1c8027b`, `3b513aa1`, `5c5699b7` | yes | per machine: the yield lot's stage-D session logs and inputs that its runbook never published; on K02 and K03, the discarded devtest (b) run 1 output |

Notes:
- The "verified" status applies to the commits listed, not to later states of the branches.
- `K05-local`: the yield lot's own `SHA256SUMS` reports `RESULT.json` differing. The same difference already exists, documented, on `evidence/yield-lot-K05` (`VERIFY_NOTE.txt`). It is not an archive defect.
- To replay the test writer's cases: Python's user site must be enabled (not disabled by `PYTHONNOUSERSITE`, `python -s`/`-I`, a different euid, or a venv created without `--system-site-packages`); a remote named `origin`; for the bundle, history depth ≥ 94 from `7fa3693e`. See its `FICHE_COMPLEMENT.md`.
- Not archived, regenerable: Lean `.olean` build products, the PDK symlinks, the test (c) scratch folders, and the checker's 23 GB scan repository. Each lot's fiche names what it left out.
