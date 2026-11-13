# Amendment 1: what is fixed before the first noisy run

Pushed before the first noisy run. When it is written, the 4 option
runs and the 24 step runs exist, all without noise, and nothing else.
`PREDICTION.md` is not edited. This amendment fixes the five points that
it left to this file, and records two things found on the way.

## 1. Step and options

By the rules of `PREDICTION.md`, applied by `rep_analyze.py`:

- **Largest step: 200 ns.** Between 400 and 200 ns, in the nine
  comparisons, the FIRE of every read, the counts and the latch and
  steering counts are the same, the largest change of a gain is 0.000089
  (limit 0.0002) and of `eps3` 0.000052 (limit 0.0001). One latch date
  moves by 0.001196 unit, above the 0.001 of the rule. So 400 ns is not
  adopted and 200 ns is kept (`STEP.md`).
- **Binary output: adopted.** Same rows and charges as the base run,
  byte for byte, and a lower total time (128 s against 130 s).
- **KLU: not adopted.** Its rows differ from the base run, and it is not
  faster (`ACCEL.md`).

`campaign.json` holds these three values; `rep_run.py` reads them.

## 2. Truncated trains

As written in `PREDICTION.md`: a repetition of a cell stops at the end
of the period of read `m` of its port of rule A1, the later of the two
if both ports pass. The verdict "count = m" is entirely decided at read
`m`; only the value of a count larger than `m` is lost. For a port 2,
the ten pulses of port 1 are played first, as in the complete train.
Each repetition is a complete and independent run from the initial
state.

## 3. Twenty repetitions, and the pooled bound

20 repetitions per cell: 1,040 runs, 1,140 trials on the 57 ports. The
bound for one port uses its 20 trials. The pooled bound on the 1,140
trials assumes **interchangeable ports and independent trials**: it
bounds the mean probability of a wrong count over these 57 ports. The
two ports of the five cells that have both share their runs.

## 4. Two machines

Even repetitions on machine A, odd repetitions on machine B, a second
cloud session of the same environment. Both check, at every run, the
SHA-256 of ngspice 42, the commit of the models and the SHA-256 of the
sources and of the reused code against `manifest.json`. Slices are
ordered by repetition number on each machine, and each slice is pushed
when it ends. There is no early stop on good results.

Each machine runs the preflight of `PREDICTION.md` before its first
repetition. `rep_run.py` writes the preflight of either machine in
`results/preflight/`; machine B moves its folder to
`results/preflight_B/` by hand before committing it, with
`PREFLIGHT_B.md`. No script is changed for that. The noisy preflight run
with noise number 900001 is expected to give the same bytes on both
machines; the comparison is reported.

If machine B cannot run, its repetitions are run on machine A after the
even ones, and a further amendment says so before they start.

## 5. Traces

Reduced traces, as written in `PREDICTION.md`. One archive per slice,
`09-repetition-traces/repNN.tar`, in the **Git history** of the private
repository, branch `sim/core-loop`, not attached to a release: the
creation of a release was refused by GitHub for this kind of session
("Creating, editing, or deleting releases is not permitted for this
session type"). With 20 repetitions and reduced traces the whole
campaign is expected to hold in about 150 MB, each archive well under
100 MB. After each slice the archive is pushed, read back from GitHub
and its SHA-256 compared with the local one; only then are the local
traces removed. The public repository holds, for each slice,
`results/repeat/repNN/ARCHIVE.json`: the name and SHA-256 of the
archive, the commit of the private repository, and the SHA-256 of each
trace; and for each run every extracted value. The traces of the option
runs and of the step runs are in `accel.tar` and `step.tar`, pushed and
read back in the same way.

## Found on the way

- **The noise is replayable.** `PREDICTION.md` says how: ngspice 42
  seeds its noise from its process id, and `fakepid.c` fixes the id seen
  by the simulator. The preflight checks it on the cell, on each machine.
- **Speed.** At 200 ns a noisy training of 21 pulses took about 195 s
  with four runs at a time in the certification campaign. The truncated
  repetitions are 11,820 periods in all: about 3 h 40 on two machines.
