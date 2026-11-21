# The top-up on three machines: the plan, written before any run

**Status.** Development work. It sets which machine runs what, how the machines are shown to agree, how each checks
its environment, and how outputs come back. It is written before any top-up run, and nothing in it changes after the
first run.

## 1. Assignment

Each instance's runs are made on one machine only, so the 8 runs of an instance always share one machine.

| Machine | Session | Instances | Runs | Expected run time | Expected wall time, 4 at a time [I] |
|---|---|---|---|---|---|
| **M1** | "Function family" (this one) | 8301, 8302, 8303, 8304 | 32 | 26 336 s | about 2.1 h |
| **M2** | a new session opened by the coordinator | 8305, 8306, 8307 | 24 | 19 752 s | about 1.7 h |
| **M3** | a new session opened by the coordinator | 8308, 8309, 8310, then the duplicate (section 2) | 24 + 1 | 19 752 + 2 216 s | about 2.3 h |

**Per instance** [K, `dev/topup.py plan`]:

| Wave | Run | Expected | Limit |
|---|---|---|---|
| W1 | guard-on deck with the reads at 1.0 | 2 216 s | 4 440 s |
| W1 | guard-off deck with the reads at 1.0 | 1 608 s | 3 220 s |
| W2 | unary scans a1, a2, b1, b2 | 650 s each | 1 300 s each |
| W2 | preset checks of a and of b | 80 s each | 160 s each |
| | **In all** | **6 584 s** | |

**How each machine runs it.** It runs `topup.py worker` once with its own instances and nothing else, detached, with
its session's turn kept running. A machine that restarts loses the runs in flight. They are reported "not complete"
and never rerun. The machine reports to the coordinator before going on.

## 2. The duplicate: the machines agree

- **Which run.** **8301's guard-on deck** is run on M1 (in M1's worker, `8301-cal-on-unary`) and again on M3
  (`topup.py dup … 8301`, `8301-cal-on-unary-dup`, after M3's worker ends).
- **The criterion.** `topup.py compare M1_RUN M3_RUN` must report `identical: true`, which requires all of:
  - the deck's text (`input.spice`), byte for byte;
  - the waveform (`trace.raw`), byte for byte;
  - `record.json` and `result.json`, equal once their clock and machine fields are removed (`wall_s`, `peak_rss_MB`,
    the interpreter's paths and hashes, the run's id and file list);
  - the noise fingerprint.
- **If it is not identical**, the other machines' results are not pooled with M1's until the difference is explained.
  Nothing is rerun, and the comparison is reported as it is.
- **Not checked.** That ngspice 42 is bit-for-bit deterministic across containers. The duplicate is the test.

## 3. The environment, on each machine, before any run

Each step is the one used on M1 and seen to work there.

1. `apt-get install -y ngspice`: Ubuntu 24.04's `42+ds-3build1`, `/usr/bin/ngspice`.
2. `/usr/bin/python3.12 -m venv /home/user/owner-prep/venv312-dev`, then `…/bin/pip install numpy==2.3.5`. The venv is
   not at the pinned path (`TOPUP_RULES.md` 0).
3. `…/bin/pip download --no-deps numpy==2.3.5 -d /home/user/owner-prep/wheel`.
4. `git clone https://github.com/efabless/skywater-pdk-libs-sky130_fd_pr /home/user/owner-prep/pdk-src`, then
   `git -C … checkout 1232782c1b9fab3aacda74d67ce7c92bf7da8105`.
5. **The code.** Each branch is fetched by name and checked out at its commit, as a worktree:
   - `research/learned-dnf-circuit-campaign-6-impl` at `ecfcd1c1` (REPO, the frozen code);
   - `research/learned-dnf-circuit-campaign-6-followup` at `56f9e83e` (its `dev/`: dosedev*.py);
   - `research/learned-dnf-circuit-campaign-7-prep` at `b956efe4` (its `dev/`: batch2x.py);
   - `research/function-family-dev` (this folder's `dev/`).

   `PYTHONPATH` = FUP/dev : PREP/dev : function-family/dev.
6. **The checks.** `…/venv312-dev/bin/python -I dev/envcheck.py Mn /usr/bin/ngspice …/pdk-src …/wheel/numpy-2.3.5-…whl
   ENV_Mn.json` must print `all_ok: true`. It checks:
   - Python 3.12.3 and its pinned SHA-256;
   - numpy 2.3.5 outside the pinned path;
   - the wheel's SHA-256;
   - the installed RECORD equal to the wheel's, apart from 4 installer lines, with every file on disk matching it;
   - ngspice's pinned SHA-256 and version;
   - the PDK at its commit, clean.

   A machine whose check fails runs nothing and reports.
7. **The tests.** `dev/test_topup.py REPO` must pass (19 tests, no simulation).
8. **The inventory.** At the start and end of the worker: `uptime -s`, `nproc`, `free`, `df`, recorded in
   `RUNS/INVENTORY_START.txt` and `INVENTORY_END.txt`.

## 4. Outputs: hashing and collection

1. **On each machine**, after its worker ends:
   - `SHA256SUMS` lists every file under its RUNS folder (`find RUNS -type f | sort | xargs sha256sum`);
   - its own SHA-256 is sent to the coordinator with `ENV_Mn.json`, `WORKER.json` and every run's status and wall time.
2. **Collection.** After the coordinator's word, each machine pushes its RUNS folder to its own evidence branch,
   `evidence/function-family-topup-Mn`, under the owner's identity. Files over 90 MB are split into 90 000 000-byte
   parts named `<file>.part-000`, … (as on `evidence/learned-dnf-circuit-campaign-7-prep`), with `SHA256SUMS` over
   the unsplit files.
3. **The analysis machine** (M1) fetches each evidence branch by name, joins the parts, and checks every file against
   that machine's `SHA256SUMS` before reading anything. A file that does not match is reported, and its instance is
   not used.
4. **The dev branch carries no waveform** (section 5).

## 5. The dev branch

`research/function-family-dev`, based on `main` (fetched by name, at the commit current when it is made), in a new
folder `research/function-family/`.

- **Author.** The owner's identity, set in the local git config only, with the e-mail of main's latest commit taken
  by script.
- **Commit.** An empty body, no trailer, no PR.
- **When.** Pushed only on the coordinator's word.

The file list is in `README.md`.
