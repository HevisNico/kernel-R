# SKY130 supervisor qualification and owner launch kit

**Phase 1, not preregistered. The physical certificate is not closed.**
A future registered campaign will be executed by a Claude Code cloud session
on behalf of the owner, on two cloud containers whose inventories are
recorded, with the [second launch kit](../sky130-supervisor-closure/launchkit/README.md),
which replaces the one of this folder for that campaign.
The first [launch kit](launchkit/README.md) supplies the pinned environment,
preflight, one command per machine, publication ordering, permanent attempt
claims, interruption handling and byte-identical survivor collection. Its
end-to-end test used an unrelated RC circuit, not a registered scenario.

The goal is service safety under an enclosed leakage jump, with no external
reauthorization inside that enclosure. Historical self-refresh missed 7/146
services (about 4.8%). This change has **not** simulated a leakage jump or
achieved that goal. Cost is secondary; no energy saving is claimed.

## Selected actuator and proved conditional controller

Clock-only maintenance reuses the timing signals with zero admitted input.
The 95% input remains diagnostic only: phase 0 observed one write in five
attempts. Clock-only writes require `upper + Dmax <= C`, including preparation;
there is no assumed saturation clamp. `C` is the smaller of the electrical
and semantic capacities.

The [Lean contract](lean/README.md) proves invariant preservation, no refusal
and every service's reserve floor for every trajectory satisfying its
whole-period loss, dose and sensor enclosures. Its sufficient room condition
is `C >= S + 2*H + 2*epsilon + Dmax`, with `Dmin >= H`. Preparation has its own
charged transition ledger and fresh entry certificate; its silences are never
service events. The physical readiness and reserve-to-FIRE implication remain
explicit premises, not consequences of the sampled waveforms.

The proof includes 31 named theorems. The axiom audit covers 361 declarations
(142 theorem declarations including generated ones); nine direct semantic
mutations are rejected. The simulator calibration runner is not connected to
the Lean kernel. This is a conditional model result, not a transistor proof.

## Capacity must preserve other reads

The new 26 qualification diagnostics include eight joint-read probes. The
baseline presets are near archived trained voltages, **not restored full
trained states**. The baseline is measured in the same setup; each result
records both actual pre-read Vmem values. Lower Vmem means more reserve.

| Nominal TT/27 C diagnostic | Joint FIRE latency, units of 20 us |
|---|---:|
| Baseline, no extra charge | 0.267717438 |
| Extra 1 mV on port 1 | 0.262489734 |
| Extra 2 mV on port 1 | 0.257326202 |
| Extra 4 mV on port 1 | 0.247197630 |
| Phase-0 proposed C=4 mV on port 1 | 0.249928772 |
| Extra 1 mV on both ports | 0.257476667 |
| Extra 2 mV on both ports | 0.247766050 |
| Phase-0 proposed C=4 mV on both ports | 0.234493875 |

C5's nominal window [0.2665,0.2685], P12's corner/temperature prediction
[0.262,0.272], and P7's cohort prediction [0.250,0.280] are different historical
criteria. [RESULTS.json](RESULTS.json) reports each separately; the widest is
not chosen after observing these data. The single-port C=4 point misses P7's
lower edge by only about 1.4 ns, so that borderline comparison alone is not a
numerically robust exclusion. The both-port case and 4 mV overcharge diagnostic
show a much larger timing change. The ideal Lean stopped-read window
(0.239,0.256] already excludes the nominal baseline; it is not a validated
transistor contract.

Thus the proposed 4 mV capacity is not qualified for the historical joint-read
semantics. This does not establish that every possible supervisor is
infeasible. Define the intended read contract, derive a semantic capacity,
and compare it with the guard's required room before continuing. A measured
voltage shift does not prove an integer trained count changed: the historical
training count remains the historical count, and no voltage-to-count decoder
has been justified. Higher gain can preserve a stopped count while violating
its latency/overshoot contract.

The leakage resistor parameter acts on both ports. Maintaining only port 1
cannot guarantee future joint reads while port 2 drifts. Either qualify a
one-port service contract explicitly or observe and maintain the second port
and include its cost. A finite voltage sweep is not a uniform capacity bound.

## Measured quantities and outstanding physical obligations

Nine deterministic diagnostics cover TT/SS/FF/SF/FS at 27 C, TT at -40/125 C,
and two TT mismatch instances (seeds 2001/2002). Each uses a constant 1e10 ohm
leakage resistance and service/clock-only/service. All 18 requested diagnostic
reads FIRE correctly. They start from presets, without a physical entry
certificate, so they are **not guaranteed service periods**. This is a finite
configuration sample, not the Cartesian product of all corners, temperature
and mismatch intervals.

For the nine maintenance slots, net voltage gain plus imposed-resistor loss
ranges from 1.344648 to 1.356709 mV. Complete-native-interval write-current
integrals divided by 30 pF range from 1.338395 to 1.365315 mV. These are two
different finite measurements; neither is a justified Dmin/Dmax enclosure.
The resistor uses Vsum/R, not Vmem/R. The capacitor is between sum and Vmem,
so terminal motion, other currents and omitted integration tails must enter
the charge balance. Each extracted interval records its omitted duration.

| Nominal Gear2 max step | Current-derived maintenance dose, mV | Net-plus-resistor proxy, mV |
|---|---:|---:|
| 200 ns | 1.347086352 | 1.346750334 |
| 100 ns | 1.347063090 | 1.346745969 |
| 50 ns | 1.347057478 | 1.346749077 |

The current estimate changes by 0.000028874 mV between 200 and 50 ns in this
one diagnostic. This improves the numerical evidence, but is not a theorem
bounding solver error, integration tails or all other configurations. The
trapezoidal nominal current result differs more, which also precludes silently
reusing a convergence allowance across integration methods.

| Contract input | Established here | Still needed |
|---|---|---|
| H | Integrated resistor losses on finite paths | Whole-period and within-period envelope including all other currents and declared deterministic domain |
| Dmin/Dmax | Instrumented writes and step refinement | Uniform charge-balance enclosure with numerical/tail allowance |
| Observer A | Simulator Vmem access, both capacitor terminals saved | Bounded observation and threshold/timing error model, outward rounding; no ADC claimed |
| C | Counterexamples to treating electrical room as semantic room | Explicit read contract, admissible semantic range, both-port treatment |
| Entry | Guarded charged-preparation theorem | Actual preparation schedule, cost bound and measured physical entry certificate |
| Physical service | Finite successful reads | Recovery/main-charge readiness and reserve-to-FIRE refinement over the domain |

Observer B (FIRE/silence only) would require a different interval observer;
its probes disturb the state. It is not supplied by access to Vmem. Likewise,
a sound lower loss estimate above H proves a violation, but arbitrarily small
or late excursions are not necessarily detectable at the first probe. A
future outside control needs a separated excursion and explicit measurement
window; refusal cannot repair an already failed service.

## Noise and compute budget

Three serial quiet/noisy timing pairs took (49.636,46.322), (59.775,79.185)
and (47.543,59.576) seconds. Their ratios are 0.933219, 1.324705 and 1.253106.
The largest observed ratio replaces phase 0's assumed 1.5 planning factor.
Noise draws are not a deterministic bounded-error domain. `setseed` controls
the mismatch setup here, not a promise of byte-identical Gaussian realizations.

`noise_bounds.py` computes a one-sided exact Clopper–Pearson lower confidence
bound for independent homogeneous **whole-run** successes. It rejects duplicate
IDs and heterogeneous pooling, counts incomplete runs as failures and never
treats correlated service periods as independent repetitions. Its use still
requires independence and a common success probability in each declared
stratum. Three successful runs would give only a 36.84% lower bound at 95%
confidence; the timing probes are exploratory, not confirmatory reliability
evidence. Reference: [SciPy exact-binomial documentation](https://docs.scipy.org/doc/scipy/reference/generated/scipy.stats._result_classes.BinomTestResult.proportion_ci.html).

The provisional six-sequence, 32-service-period packing costs **3 h 14 min
15 s aggregate**, or **1 h 37 min 08 s per machine** with three sequences each.
It uses 35 s/period, the measured maximum factor, 25% reserve, one setup-period
allowance and 30 s startup per sequence. Actual charged preparation and the
chosen number of noisy repetitions must fit the final forecast; more runs
cannot be added for free. A 2,300 s timeout per sequence plus 10 s termination
allowance would cap the six process budgets at 3 h 51 min. Setup, Git pushes
and evidence copying are additional owner time. Hardware-dependent estimates
are not hard runtime guarantees. Scope must be reduced before preregistration
if the updated owner-machine forecast exceeds four aggregate hours.

## Verification, raw evidence and next gate

```sh
python3 -B research/sky130-supervisor-qualification/verify.py
python3 -B research/sky130-supervisor-qualification/report.py --check
```

The first command checks published metadata, code identities, forecast,
conditional Lean proof/mutations, statistics and kit controls. It needs
Python3.12.14, numpy2.3.5 and Lean4.35.0; it runs no circuit campaign. The second
re-extracts the exact 26 locally retained waveforms and needs their raw files.
CI does the first only and does not pretend to possess the excluded waveforms.
[REPRODUCE.md](REPRODUCE.md) gives the exploratory commands and hash inventory.
Raw exploratory waveforms remain excluded from Git. Unique noisy records are
preserved separately; their hashes are published along with every saved deck,
metadata and simulator log. No historical source or evidence is modified.

Before PREDICTION.md: resolve semantic capacity and the second-port contract,
justify deterministic enclosures and the physical entry/refinement, then
freeze the scenario allocation, observation/repetition model, preparation and
terminal-stock accounting. Only afterward preregister, implement the actual
campaign runner, obtain exact-commit green CI and let the owner publish
RUN_ATTEMPT.json and launch once. The kit's passing synthetic test authorizes
none of those scientific steps by itself.
