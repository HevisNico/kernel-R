# Certification campaign: rules, criteria and predictions

Pushed to the public repository before the first run. The time at which
GitHub receives this push is the date of these rules. This file is not
edited afterwards. A deviation is declared in a new file, pushed before
the run or the computation that it concerns.

## What is known when this is written

Everything in `research/circuit/` up to pull requests 105 and 106: the
original campaign of 141 runs, its ten count disagreements, the five
instrumented replays, the DC calibration, the result that no port of the
100 original cells is in the certified domain, the decomposition of the
budget (`m*b` is the largest term, half of `b` is calibration error) and
the cumulative budget under estimates. No run of this campaign exists.

The cells of this campaign are new. Their mismatch seeds were never run.

## Purpose

Decide, port by port, whether the need theorem applies with bounds
measured on the port's own run, and whether its count is then the
predicted one. The theorem is `needAlong_of_cumulative_tolerance`
(`recursive-learning/native/Search/VariableNeedTolerance.lean`):

```text
if   |z(n) - z(0) - n*d0| <= B   for every n <= m,
and  z(m) <= z(n)                for every n >= m,
and  |z(0) - needCentre(level0, d0, m)| <= a,   |level - level0| <= ell,
and  a + B + (20/17)*ell + 1/8000 < d0/2,
then reads after fewer than m writes are silent and the read after m writes fires.
```

It is applied to the sequence `z(n)` of the gains of the first reads of a
port, frozen after the m-th: `z'(n) = z(min(n, m))`. The second
hypothesis then holds by construction, and the conclusion is about the
reads up to the m-th, which is what a count is.

## Simulator and sources

ngspice 42, Ubuntu package 42+ds-3build1, SHA-256
`820658317b0b54035208da41936fd6871ce924036e5ea4113a4168b821b7fc45`: the
binary of the original campaign. The SKY130 models at commit
`1232782c1b9fab3aacda74d67ce7c92bf7da8105`. The netlist `cell.spice` and
`blocks.spice`, the noise levels `noise.json` and `spiceinit.txt` of the
original campaign, unchanged; their hashes are in `manifest.json`. Every
run uses the solver options of the netlist, a largest step of 200 ns, and
27 °C. A generated deck adds to the netlist text: the saved nodes, the
pulse schedule of the two ports, a leak resistance or a ramp current
source where a run needs one, the seed, and the noise sources of
`noise.json` where noise is on. If another binary has to be used, an
amendment says so before the run.

## Runs

`manifest.json` holds the complete ordered list. Every run is made once.
A run that fails stays failed and is reported; nothing is run again to
replace it. `cert_launch.py` ends with a status that is not zero when a
run fails.

| Stage | Runs | Noise | What |
|---|---|---|---|
| 0. Preflight | 5 | off | Nominal cell: one training, one ramp, one leak scan. Mismatch seed 5001: one first read, and one first read with an added source of no current, which must give the same result. Instrumentation only |
| 1. Calibration cohort | 20 trainings, 20 ramps, 5 leak scans | off | Mismatch seeds 5001 to 5020, section `tt_mm`. Leak scans on 5001 to 5005 |
| 2. Characterization of the test cells | 100 ramps, 100 first reads | off | Mismatch seeds 6001 to 6100 |
| 3. Test | 100 trainings | on | The same seeds 6001 to 6100: 10 pulses on port 1, 10 on port 2, one on both |

Order: the constants of stage 1 are pushed before stage 2 is analysed;
the predicted need of every port is pushed before the first run of
stage 3.

- **Training:** the stimulus of the original campaign.
- **First read:** one pulse on port 1, then one on port 2, at the start
  gain. No noise.
- **Ramp:** no pulse. A current source draws the main capacitor down from
  rest to 0.75 V in 800 µs, about eight times slower than the slowest
  read. The level at which the protection latch rises is the static FIRE
  level of the cell. A DC sweep cannot be used on a circuit with latches.
- **Leak scan:** 40 pulses on port 1 under a leak of 0.1 TΩ, without
  noise. After the stop the gain falls by about 1/22 of a dose per
  period until one pulse is silent.

A noisy run is not reproduced by its seed. Every run saves, with 16
digits and at every solver point, the main capacitor, the protection
latch, the raw comparator, its reference and its noise source, the two
stored voltages, and for each port the sensor, the summing node, the
entry and exit latches and the steering signal. `cert_run.py` keeps, for
each period, the points from 1 µs before the pulse to 1.1 unit after its
start, and from 0.5 µs before the entry of the write window to 3 µs
after its exit. These compact traces go to the private repository; their
SHA-256 is in the public metadata of each run. The rest of the solver
output is not kept.

## Checks of a result

A result is used only if it has exactly the rows of its plan, in the
order of the ports of its plan, with finite values and with flags that
are 0 or 1: the checks of pull request 106 (`analyze.read_run`). A run
whose result fails a check is failed.

## Quantities

Coordinates: `q = 0.1 + (1.25 - Vq)/0.5`; one time unit is 20 µs; a pulse
starts 4.1 µs after the start of its period. All values at a date are
linear interpolations between the two solver points around it.

For a read (a pulse on a port), with `c` the value of `q` 1 ps before
the pulse:

- **Rest state:** `c`. It must be in `[0.1, 0.1001]`.
- **FIRE:** a rising crossing of the protection latch at 0.9 V in the
  period.
- **Gain of a silent read:** `G = log(P - 0.1 - (c - 0.1)*exp(-1/2))`,
  with `P` the largest `q` of the period. The scalar model with that
  gain has exactly the peak `P`; the constant `log(response 1)` is
  dropped, as it cancels everywhere.
- **Early gain of any read:** `Y = log(q(0.75) - 0.1 - (c - 0.1)*exp(-3/8))`
  at 0.75 unit after the start of the pulse.
- **Gain of a read with a FIRE:** `Y + kappa`, where `kappa` is a
  constant of stage 1. A read with a FIRE earlier than 0.76 has no gain.
- **Noise of the threshold in a read:** the largest `|v(nzm)|` between
  the start of the pulse and one unit later, divided by 0.5.

`Z(n)` is the gain of the n-th read of a port, n counted from 0: `G` if
that read is silent, `Y + kappa` if it has a FIRE. The **count** `k` of
a port is the number of its reads before its first FIRE (10 if none).

### Constants of stage 1, from the calibration cohort

- `kappa`: mean of `G - Y` over the silent single-port reads of the 20
  trainings.
- `d0`: mean of `Z(n+1) - Z(n)` over all pairs of successive reads of a
  port up to its first FIRE, in the 20 trainings.
- `mu` and `h_mu`: in each leak scan, take the first silent read after
  the first FIRE, with peak `Ps`, and the read before it, with the peak
  `Pf = 0.1 + (c - 0.1)*exp(-1/2) + exp(Y + kappa)` that its gain gives. The firing level lies
  between them. With `Ls` the static level of that cell,
  `mu = mean of (Ps + Pf)/2 - Ls` over the five cells and the nominal
  cell of stage 0, and `h_mu` is the largest `|(Ps + Pf)/2 - Ls - mu|`
  plus the largest `(Pf - Ps)/2`.
- `s`: slope of the gain against the stored voltage, the least-squares
  slope of `G` against the mean stored voltage of the port during the
  pulse, over the silent reads of the cohort, each port centred on its
  own mean. Used only to report `eta`, `sigma` and `e`.

If a leak scan has no silent read after its first FIRE, or a cohort
value is missing, the constant is not evaluable and so is everything
that needs it.

### Per port of a test cell, before its test run

From stage 2: `Ls`, the static level of its cell, and `G0s`, the gain of
its first read without noise (`Y + kappa` if that read has a FIRE).

```text
level0 = Ls + mu
gap    = log(level0 - 0.1) - G0s
m      = 0 if gap <= 0, else the smallest integer with m*d0 >= gap
a_s    = |gap - (m - 1/2)*d0|
```

`m` is the prediction. It uses no pulse of the test run. The table of
`m` for the 200 ports is pushed before the first test run.

### Per port, from its test run

Let `r = min(k, m, 9)`: the reads 0 to `r` are those the theorem speaks
of and that exist.

```text
eps_kappa = largest |G - Y - kappa| over all silent single-port reads of the 100 test runs
a   = a_s + |Z(0) - G0s| + mz
B   = max over 1 <= n <= r of |Z(n) - Z(0) - n*d0| , plus eps_kappa if read r has a FIRE, plus 2*mz
ell = h_mu + max over the reads 0..r of the noise of the threshold + mq
room = d0/2 - a - B - (20/17)*ell - 1/8000
```

`mz = 0.0002` and `mq = 0.0002` are margins fixed here. They cover the
resolution of a value read on the solver points (tolerances `reltol`
1e-4 and `vntol` 1e-7 V) and of the ramp.

`eps_kappa` also enters `a` and `Z(0)` when read 0 has a FIRE.

### Per write, reported and not used for the status

For each write `j` of a port before its first FIRE, with the endpoint
voltages of its window between the entry and exit latches:

```text
sigma(j)   = |s*(Cs/Cf)*(Vs(entry) - Vs(exit)) - d0|
k*eta(j)   = (s/Cf) * |Cf*((Vmem - Vsum)(entry) - (Vmem - Vsum)(exit)) - Cs*(Vs(entry) - Vs(exit))|
e(j)       = |Z(j+1) - Z(j) - s*((Vmem - Vsum)(entry) - (Vmem - Vsum)(exit))|
b_sum      = max over j of k*eta(j) + sigma(j) + e(j), plus 2*mz
b_direct   = max over j of |Z(j+1) - Z(j) - d0|, plus 2*mz
```

## Status of a port

| Status | Rule |
|---|---|
| Not evaluable | Its run or a run of its cell failed or failed a check; a constant is missing; a read 0..r has a FIRE earlier than 0.76 |
| Outside the certified domain | Evaluable, and one of: a rest state of a read 0..r outside `[0.1, 0.1001]`; the latch rises twice in one of these periods; the steering switch does not turn on exactly once in a silent period among them, or turns on in a period with a FIRE; `level0 - ell < 19/20`; `room <= 0`. The reason is given |
| Certified, count confirmed | None of the above, and `k = m` (or `k = 10` and `m >= 10`) |
| Certified, count contradicted | None of the above, and the count is not the predicted one. This is a failure of the application of the theorem to the circuit. It is reported as such and investigated; nothing is adjusted to remove it |

"Certified" means: every hypothesis of the theorem has a bound measured
on the run of the port or on the calibration, with the worst case, the
resolution and the margins above, and the theorem then gives the count.
It is a statement about a simulation. It rests on what cannot be
measured: that the comparator fires exactly when the uncut peak of a
read reaches the firing level within `ell`, which the leak scans support
on six cells; that a gain read 0.25 unit before the end of a pulse
stands for the gain of that read within `eps_kappa`; and the accuracy of
the solver.

No rule, constant, margin or cutoff is changed after a number of stage 3
is seen. If a rule proves wrong, a new rule is written and pushed before
it is used, and both results are shown.

## Target

`b <= 0.0026` per write, for both `b_sum` and `b_direct`. The report
gives, for each port and for the cohort, by how much it is met or
missed.

## Predictions

| | Prediction |
|---|---|
| E1 | Every rest state before a pulse is inside `[0.1, 0.1001]` in the 100 test runs |
| E2 | In every period of the test runs the latch rises at most once, the steering switch turns on exactly once in a silent single-port period and never in a period with a FIRE |
| E3 | The count equals the predicted `m` on 85% to 98% of the 200 ports |
| E4 | Between 20% and 60% of the 200 ports are certified |
| E5 | No certified port has its count contradicted |
| E6 | The target is missed: fewer than 25% of the ports have `b_direct <= 0.0026`, and the median `b_direct` is between 0.004 and 0.012. The noise of the gain from one read to the next is larger than the target |
| E7 | The static level of the 100 cells has a standard deviation between 0.001 and 0.008 |
| E8 | No run fails |

## What this campaign does not do

- It does not change the status of any port of the original campaign.
  `mc_2064`, port 1, keeps its historical status.
- It does not build the detection of a pulse: the three timing signals
  of each pulse stay ideal.
- It does not test the read windows of the ideal model.
- It is a simulation. No chip was built.
