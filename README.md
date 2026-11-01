# kernel-R

A hybrid dynamical kernel for pulse-driven learning and adaptation.

This repository contains the R cell definition, our reciprocal-learning and
teaching experiments, and their new local computer-assisted proofs. The older
A22 network engines and historical proof archive stay in the
[upstream repository](https://github.com/HevisNico/a22-going-further).

## Physical Lean proof status

The [Lean formalization](proof/lean/README.md) constructs an actual execution
from A's READY birth through C's first protected cadence MARK return at
**660**, with cumulative **A39/B44/C15**. Both independent births at160/480
and the first genuine C→B→A wave remain in the witness. The actual C656 input
adds MARK0.1, and the actual C660 source is consumed: C is READY at q=0.1
with fresh RAW660, its own newborn recovery+0.2 and own port0 log-gain+1.8.
A/B retain their actual cuts, modes, raw states, energy and continuations.
Exactly 19 Cport0 sources664..736 remain. The earlier639.9 checkpoint retains
three prepared cells, RAW absent and25 C sources. Parameters are fixed
independent fabrication-box members, with canonical pulses and bounded delays.

A separate autonomous-C construction now runs from the actual 639.9 state
through **789.9**. It projects C's already constructed global prefix through660,
then appends C's physical local continuation. It consumes all 25 C640..736
sources and emits exactly 20 cadence signals, giving C34 including teaching.
The endpoint is READY/q=0.1, with no RAW or pending source, own newborn port0
log-gain+2.4 and recovery+0.3. Its real emission ledger supplies a leaf packet
P(3,17,0); bounded delays label P(3,17,0.05) at the actual FIRE times. These
labels do not assert global issuance or receipt of the later wires.

The globally routed responses toward664/668 and the remaining cadence through
789.9 (**A54/B61/C34**) still require construction. The complete cadence
analysis is checked **conditionally on supplied later executions**. An
end-to-end physical Lean proof for every finite N remains open. See the
[checkpoint and theorem map](proof/lean/HYBRID_EXECUTION.md).

The [one-cell continuation proof](proof/lean/INDEFINITE_OPERATION.md) constructs
repeatable learned cycles and compatible complete executions at every finite
horizon, for input spacing at least7.5. Aport2/Bport2 coordinate projections of
the actual639.9 state now satisfy its exact-rest learned domain. These isolated
one-cell contracts use empty routing and new future sources; the empty analysis
queues do not erase the global C source queue. Network refinement remains open.

## Start here

- [N-cell composition theorem](proof/reciprocal_composition/THEOREM.md): every finite chain, with source-length and path-jitter budgets.
- [Robust slow chains](research/robust/README.md): drift, bounded charge noise and pulse-amplitude variation, from birth; Lean scope in [robust coverage](proof/lean/ROBUST_COVERAGE.md).
- [R kernel definition](kernel/README.md) and [original model](model/full_model_reference.md).
- [Cadence cascade proof](proof/reciprocal_cadence/THEOREM.md): C's faster cadence reaches A through B, from birth through time 789.9.
- [Birth-to-feedback proof](proof/reciprocal_entry/THEOREM.md): pulses-only initialization through time 459.9.
- [Prepared-section theorem](proof/reciprocal_learning/THEOREM.md): the local A-learns-from-B effect.
- [Lean proof project](proof/lean/README.md): constructed physical executions, conditional protocol theorems, certificate endpoint checks and finite adaptive-policy replay, with explicit coverage limits.
- [Reciprocal prototype](experiments/reciprocal/README.md): cells remain alive and learn back from their students.
- [Learned teaching choice](experiments/reciprocal/pedagogy/README.md) and [within-lesson adaptation](experiments/reciprocal/adaptive/README.md).
- [Complete English prototype ZIP](downloads/R_Reciprocal_Prototype.zip): runnable code, recordings, reports and proofs in titled folders.

Extract the ZIP and open `12_Certified_N_Cell_Composition/RESULTS.html` for the latest
proof, or `03_Visualization/OPEN_IN_BROWSER.html` for the recorded three-cell
network. The viewer replays simulations rather than solving the equations.

## Results and scope

| Work | Evidence and boundary |
|---|---|
| Reciprocal R | Numerical three-cell network; parents remain alive and relearn from peer pulses. Schedules and settings copies are supplied. |
| Teaching efficacy | Actual and reversed feedback both improve transmission; that alone does not establish learned pedagogy. |
| Curriculum selection | Native R gains store a teaching choice in an added diagnostic/feedback/readout architecture. |
| Within-lesson adaptation | A learned stopping policy improves on fixed durations; a programmed equivalent rule matches it. |
| Local feedback theorem | ±0.3% and ±10% physical boxes, from a prepared section. |
| Entry and composed theorem | The declared READY birth family reaches that section; pulses-only protocol through time 459.9. |
| Cadence cascade theorem | From birth through 789.9, on 45-parameter boxes: C->B->A; b gains 0.2 in each cell's fast stage; A's frozen period-4 probe improves 4/8 to 8/8. |
| N-cell composition theorem | Every finite directed chain, 15*N independent physical parameters: K>=4*N+12 and summed link-jitter budgets <=0.15. Fixed link delays allow arbitrary depth. |
| Robust slow chains (research) | Prepared or birth-entered slow chains under measurable drift inside ±0.3% or ±10%, charge noise \|w\|<=nu and received-amplitude factor in [1-alpha,1+alpha]: K>=3*N+1, T>=7.5+2*sum(delta_i+sigma_i). Eight certified (epsilon,nu,alpha) points, and closed ranges such as every nu in [0,0.002] ([ranges](research/robust/ranges/README.md)); delta=0 without noise or amplitude variation. Written proofs and integer-replayed certificates; the Lean chain induction is conditional on each cell's `CellLaw` and covers timing and counts only. |

The composed proof starts with b near 0.08, establishes one protected full MARK
in each cell, and reaches b near 0.18 at time 319.9. It then proves
`g_A,after = g_A,birth * exp(1.8)` on A's feedback port, with an isolated retained
probe changing from 0/8 to 8/8. The box contains all 30 original per-port physical
parameters of A and B independently.

The cadence extension reaches 789.9, including C's introduction, 20/18/16 fast
emissions in C/B/A and two full recovery MARK doses in each. It covers all 45
per-port physical parameters independently, with per-pulse wire jitter in [0.3,0.4].
The [cadence results](results/reciprocal_cadence/README.md) include retained probes
and causal cuts: without either reverse link, A remains at 4/8.

These ±10% prefix results do not certify the older entire A22 network at ±10%,
the settings-copy variant, open recurrence after 800 or adaptive pedagogy. The new
theorems combine written hybrid-flow arguments with checked interval obligations;
they are not complete Lean formalizations or independently peer-reviewed mathematics.

The [Lean project](proof/lean/README.md) proves physical flow, reserve and memory
invariants, the constructed prefix described above, and later conditional
protocol results. It also checks exact rational certificate endpoints and
recorded cadence/adaptive counters. These evidence checks do not establish
membership of the actual trajectories in every recorded interval. The complete
physical continuation, retained probes and physical leaf/relay refinement for
the finite-chain theorem remain separate obligations.

The [N-cell extension](results/reciprocal_composition/README.md) uses a closed
packet contract and a written induction, supported by 81 N-independent local
inequalities and 12 exact polynomial identities. Physical tolerances stay at
±10% as N grows. Source length and time grow linearly; fast-block traffic is
quadratic at the supplied minimum source length. Per-pulse wire jitter must
obey the path budget; the old 25-pulse train and full ±0.05 jitter per link
are not claimed to work unchanged at arbitrary depth.

## Verify the proofs

Python 3.12 and its standard library suffice; no numerical packages or network
access are required.

Dependency replay runs only authenticated source snapshots in a temporary
directory, with isolated Python startup. Unlisted modules, packages and caches
in a supplied dependency directory cannot join that snapshot.

```sh
python -B -m unittest discover -s tests
python -B certify/reciprocal_learning/tests.py
python -B certify/reciprocal_entry/tests.py --link-code certify/reciprocal_learning --link-003 results/reciprocal_learning/eps3e-3/certificate.json --link-01 results/reciprocal_learning/eps1e-1/certificate.json
python -B certify/reciprocal_entry/verify.py results/reciprocal_entry/eps1e-1/certificate.json --link-certificate results/reciprocal_learning/eps1e-1/certificate.json --link-code certify/reciprocal_learning
python -B certify/reciprocal_cadence/tests.py
python -B certify/reciprocal_composition/tests.py
```

There are 14 local-theorem, 16 entry/composition, 18 cadence and 21 N-composition
tests, plus three project-layout checks. The cadence
checker replays 95 actual input cases, 1,030 strict obligations and 2,533 enclosures
for each physical box, and rechecks the authenticated earlier theorems.
The entry checker
verifies 59 obligations and 170 enclosures, then rechecks the pinned local theorem's
31 obligations and 103 enclosures. The two arithmetic implementations are outward
Decimal intervals and integer fixed point with explicit exp/ln series tails.

## Restore recordings or run a fresh experiment

The recorded data are kept once in the ZIP instead of duplicating dozens of
large JSON files in the source tree. Restore them with their SHA-256 checks:

```sh
python -B tools/prepare_recordings.py
```

This creates ignored `audit_runs/` inputs. Existing different local outputs are
never overwritten. The full records remain directly inspectable inside the ZIP.
To run a fresh network:

```sh
python -m pip install -r requirements.txt
python -u -B experiments/reciprocal/simulate.py --out audit_runs/new_reciprocal
python -u -B experiments/reciprocal/analyse.py --out audit_runs/new_reciprocal
python -u -B experiments/reciprocal/validate.py --out audit_runs/new_reciprocal
```

NumPy 2.3.5 and SciPy 1.17.0 are pinned. Use a new output directory for each run.
The individual experiment guides provide further teaching and adaptation commands.
New adaptive plans lock both simulation engines and the numerical runtime;
legacy two-file plans are rejected by the updated validators. See the
[adaptive reproduction notes](experiments/reciprocal/adaptive/README.md#reproduce).
The bundled adaptive records have been recomputed on the original seeds with
that complete manifest. All 127 experiment checks and continuous teacher replay
pass; legacy adaptive development and aborted-run records have been removed.

After installing the numerical requirements, run the terminal-event and
provenance regressions with:

```sh
python -B -m unittest discover -s experiments/reciprocal/tests -v
```

## Rebuild the ZIP

```sh
python -B tools/prepare_recordings.py
python -B experiments/reciprocal/package.py
```

The output is `dist/R_Reciprocal_Prototype.zip`, constrained below 30,000,000 bytes.
The provided download is a pinned research snapshot; rebuilding an archive need
not preserve ZIP timestamps, while its source/data manifest remains verifiable.

Optional viewer QA uses Node.js: `npm install`, then `npm run check:viewer`.
`npm run check:browser` additionally needs an installed Playwright Chromium binary.
The original reports distinguish DOM/SVG checks from unavailable full-browser tests.

## Where the robust results live

The robust results are in `research/robust/`, not in `certify/`, `proof/` and `results/`.
They originate in a tested offline package. The numerical sources, certificates and
traces retain their identities; the current guide and its documented provenance
updates adapt that snapshot to this repository. Their protocol is a different, slow-input chain: it is not the fast period-4
packet protocol of the N-cell composition theorem. Their status is that of the other
written theorems: hybrid arguments written by hand, finite inequalities replayed in
independent integer arithmetic, and, in Lean, the chain induction and the certificate
endpoints. Proving each cell's `CellLaw` from the hybrid execution is the open step
([plan](proof/lean/CELLLAW_PLAN.md)).

## Reference boundary and limitations

The [kernel guide](kernel/README.md) describes R as a cell and links the current
three-cell and chain protocols. The `model/` snapshots and
[archived A22 kernel guide](kernel/reference/A22_KERNEL_README.txt) preserve the
original reference context. `kernel/KERNEL_SHA256SUMS` identifies upstream engine
files; those engines are not vendored here. See [provenance](docs/PROVENANCE.md).

General pedagogy, semantic memory, new waveform invention and chip energy/area
benefits remain unproved. Observation bins, feedback coding, lesson primitives
and copying rules are supplied components unless explicitly learned in a test.
R's monotone parameters impose saturation and forgetting limits. The
[proposed invention protocol](experiments/reciprocal/adaptive/INVENTION_PROTOCOL.md)
is a future experiment, not a completed result.

## How this was built

This work is done with two AI assistants, **Claude** (Anthropic) and **ChatGPT** (OpenAI), under the direction of Nicolas Breuillaud.

## License

Source code is [MIT](LICENSE). Documents, proofs, data, certificates and other
non-code material are CC BY 4.0 under [LICENSE-docs.md](LICENSE-docs.md).
