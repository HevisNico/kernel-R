# kernel-R

[![Lean proof checks](https://github.com/HevisNico/kernel-R/actions/workflows/lean.yml/badge.svg)](https://github.com/HevisNico/kernel-R/actions/workflows/lean.yml)

Lean now constructs a complete pulse-driven learning-and-cadence protocol
for three cells.

Starting from A's original READY birth, with independent B/C births at 160/480,
the construction reaches **789.9** with cumulative **A54/B61/C34**. All three
cells finish READY at q=0.1, with no RAW current and an empty global queue.

1. [Result: a constructed three-cell learning protocol](#result-a-constructed-three-cell-learning-protocol)
2. [Lean headline: the exact theorem and how to check it](#lean-headline-the-exact-theorem-and-how-to-check-it)
3. [Model ↔ Lean: equations, events and assumptions](#model--lean-equations-events-and-assumptions)

## Result: a constructed three-cell learning protocol

R is a pulse-driven hybrid cell with local gain and recovery memory. This
repository develops its physical equations, experiments and Lean proofs,
drawing inspiration from Nicolas Breuillaud's
[*The Reset Operator: A Structural Constraint on Recursivity*](https://ssrn.com/abstract=6964960).
The earlier engines and proof archive remain in the
[upstream A22 repository](https://github.com/HevisNico/a22-going-further).
The reference credits the model's inspiration; its broader claims are not
premises or conclusions of the Lean theorem below.

Three cells can change their response through pulses alone: ERROR activity
increases an input's gain while the main cell is READY; protected MARK
activity increases recovery, which controls the return from SLOW to READY.
The constructed protocol uses these two local mechanisms to teach C from B,
then propagate C's faster cadence back through B to A. Source schedules and
contacts are declared parts of this protocol.

The actual FIRE counts and terminal coordinates are:

| At 789.9 | A | B | C |
|---|---|---|---|
| Cumulative emissions from each cell's own birth | **54** | **61** | **34** |
| Emissions in the final cadence block | 16 | 18 | 20 |
| Active learned port | 2 | 2 | 0 |
| Active log-gain relative to its own birth | +2.4 | +2.4 | +2.4 |
| Recovery relative to its own birth | +0.3 | +0.3 | +0.3 |
| Terminal main state | READY, q=0.1 | READY, q=0.1 | READY, q=0.1 |

All auxiliaries are READY in their rest bands, every RAW current has ended,
and the global pending queue is empty. Other gains preserve their teaching
memories, including Aport0+1.8, Bport1+0.6 and Cport1+0.6. Energy follows the
actual ODE and remains within [50,100]. Actual FIRE jumps issue wire tokens;
actual arrivals consume them. No reaching execution, receiving calendar,
output count or settings-copy operation is supplied to the existence theorem.

The statement has the quantifier order

> **For every admissible choice of fixed parameters, birth data and bounded
> delay functions, there exists a constructed physical execution with these
> properties.**

The assumptions include A's READY `BirthState` with all auxiliaries READY,
the exact declared source queues, independent READY B/C `Newborn` states,
canonical width-one pulses and per-cell/per-port parameters fixed in time in either
the ±0.3% or ±10% fabrication box. Each of five delay functions is bounded
in [0.3,0.4] and sampled at its actual sending FIRE. No equality of parameters
or delay functions between cells is required.

The birth coordinates satisfy q=0.1±10⁻⁵, b=0.08±10⁻⁵, energy in [50,100],
and each log-gain lies within10⁻⁵ of log(0.3), log(1.2), log(0.3) on ports0/1/2.
All auxiliaries start READY with m=0.025±10⁻⁵ and no active RAW. These are
independent birth ranges, not copied learned states.

The declared contacts use the sending FIRE date F to select these windows:

| Contact | Target port | Sending window | Delay function |
|---|---|---|---|
| A→B teaching | B1 | 160≤F<310 | `forward` |
| B→A feedback | A2 | 320≤F<470 | `backward` |
| B→C teaching | C1 | 480≤F<630 | `delay` |
| C→B cadence | B2 | 640≤F<780 | `cascadeForward` |
| B→A cadence | A2 | 640≤F<780 | `cascadeBackward` |

The external source programs are Aport0 at0,8,…,120 and160,168,…,280;
Bport2 at320,328,…,440 and480,488,…,600; and Cport0 at640,644,…,736.
The B/C source tokens enter with their genuine births. Routed receiving dates
are derived from actual emissions and the delay functions.

**Scope:** this is the declared **three-cell protocol through 789.9**, with
fixed fabrication parameters and bounded delays. It proves existence of a
witness; it does not assert the same result for every admissible execution.
Physical every-N refinement, indefinitely operating networks, operational
noise/drift, retained frozen probes and settings-copy semantics remain open.
Separate robust analyses and numerical simulations retain their stated scope;
simulation output is not the Lean proof. See the
[full proof boundary](proof/lean/HYBRID_EXECUTION.md) and
[N-cell coverage](proof/lean/N_CELL_COVERAGE.md).

## Lean headline: the exact theorem and how to check it

The short public entry point is
[**KernelR/Headline.lean**](proof/lean/KernelR/Headline.lean), in namespace
`KernelR.Hybrid.Headline`:

| Declaration | Checked statement |
|---|---|
| `three_cell_protocol_exists` | From the birth/source, fixed fabrication-box and five bounded-delay hypotheses, returns `Nonempty (ConstructedBirthCadenceProtocol ...)` |
| `terminal_state_and_counts` | For that witness: time 789.9, all READY/q=0.1, no RAW, empty queue and exact cumulative A54/B61/C34 |
| `learned_memories` | For that witness: own active log-gains+12/5 and own recoveries+3/10 |

<details>
<summary>Exact Lean signatures</summary>

These declaration headers are copied from `KernelR/Headline.lean`; proof bodies
are omitted. The variable declaration supplies the shared witness to the last
two statements.

```lean
namespace KernelR.Hybrid.Headline

theorem three_cell_protocol_exists {θ born freshB freshC ε}
    (hborn : @BirthState 1 born)
    (hb : @PhysicalBox 3 (extendParameters (extendParameters θ freshB) freshC) ε)
    (ha : ∀ q, born.aux 0 q = .ready)
    (hqueue : born.pending = sourceTrain 0 0 0 8 16 ++ sourceTrain 0 0 160 8 16)
    (newbornB newbornC : Newborn) (forward backward delay cascadeForward cascadeBackward : ℝ → ℝ)
    (hforward : ∀ time, (3 / 10 : ℝ) ≤ forward time ∧ forward time ≤ 2 / 5)
    (hback : ∀ time, (3 / 10 : ℝ) ≤ backward time ∧ backward time ≤ 2 / 5)
    (hdelay : ∀ time, (3 / 10 : ℝ) ≤ delay time ∧ delay time ≤ 2 / 5)
    (hcascadeForward : ∀ time, (3 / 10 : ℝ) ≤ cascadeForward time ∧ cascadeForward time ≤ 2 / 5)
    (hcascadeBackward : ∀ time, (3 / 10 : ℝ) ≤ cascadeBackward time ∧ cascadeBackward time ≤ 2 / 5) :
    Nonempty (ConstructedBirthCadenceProtocol θ born freshB freshC newbornB newbornC
      forward backward delay cascadeForward cascadeBackward)

variable {θ born freshB freshC newbornB newbornC forward backward delay cascadeForward cascadeBackward}
  (c : ConstructedBirthCadenceProtocol θ born freshB freshC newbornB newbornC
    forward backward delay cascadeForward cascadeBackward)

theorem terminal_state_and_counts :
    c.final.time = (7899 : ℝ) / 10 ∧
    (∀ i : Fin 3, ReadyCoordinates c.final i) ∧
    (∀ i : Fin 3, c.final.x i .q = 1 / 10) ∧
    (∀ (i : Fin 3) (p : Port), c.final.raw i p = none) ∧
    c.final.pending = [] ∧ aCount c = 54 ∧ bCount c = 61 ∧ cCount c = 34

theorem learned_memories :
    c.final.x 0 (.z 2) = born.x 0 (.z 2) + 12 / 5 ∧
    c.final.x 1 (.z 2) = newbornB.x (.z 2) + 12 / 5 ∧
    c.final.x 2 (.z 0) = newbornC.x (.z 0) + 12 / 5 ∧
    c.final.x 0 .b = born.x 0 .b + 3 / 10 ∧
    c.final.x 1 .b = newbornB.x .b + 3 / 10 ∧
    c.final.x 2 .b = newbornC.x .b + 3 / 10

end KernelR.Hybrid.Headline
```

`aCount`, `bCount` and `cCount` are defined in that source from actual
`emissionTimes` FIRE lists, concatenated/counting the appropriate phases across
both births. They are not supplied output counters.

</details>

The witness retains both genuine births and the actual intervening executions.
After C's birth, teaching and cadence use one fixed gated three-cell router;
retargeting preserves the complete physical ledger and delivered occurrences.
The [protocol implementation](proof/lean/KernelR/HybridBirthCadenceProtocol.lean)
and [checkpoint map](proof/lean/HYBRID_EXECUTION.md#constructed-protocol-checkpoint)
expose the construction behind the headline.

The project pins **Lean 4.35.0** and **Mathlib v4.35.0** in
[lean-toolchain](proof/lean/lean-toolchain),
[lakefile.toml](proof/lean/lakefile.toml) and
[lake-manifest.json](proof/lean/lake-manifest.json). Mathlib is locked to commit
`56a005855ea17e0b0958f73ec801ae140b0a1679`.
The verified code commit is
[c7b66bba9065debde10fe9a9bd4134b256396330](https://github.com/HevisNico/kernel-R/commit/c7b66bba9065debde10fe9a9bd4134b256396330);
the subsequent README-only commit records this identifier and changes no code.
With Lean installed, from the repository root:

```sh
git checkout c7b66bba9065debde10fe9a9bd4134b256396330
cd proof/lean
lake exe cache get
lake build KernelR.Headline
lake build
lake build Audit
```

The headline's `#print axioms` output is:

```text
'KernelR.Hybrid.Headline.three_cell_protocol_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
'KernelR.Hybrid.Headline.terminal_state_and_counts' depends on axioms: [propext, Classical.choice, Quot.sound]
'KernelR.Hybrid.Headline.learned_memories' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are Lean's standard logical axioms, not added physical hypotheses. The
global audit restricts project theorem dependencies to this list. See the
[complete reproduction commands](proof/lean/README.md#reproduce) and
[workflow](.github/workflows/lean.yml). Source/evidence checks cover 436 Lean
source files, all 16 robust certificates and 12 project tests. All 226 new paired
controls pass; the configured inventory is 1103 pairs, without asserting that
every historical suite has been rerun locally. The complete export passes
**9,489 build jobs** and the global audit of **26,317 project theorems**.
The five inherited modules are unchanged; source checks reject admitted proofs
and added project axioms. The workflow badge links to actual runs; fresh PR
checks retain their actual status until they finish.

This work is done with two AI assistants, **Claude** (Anthropic) and **ChatGPT** (OpenAI), under the direction of Nicolas Breuillaud.

AI assistance concerns the preparation of models, code, proofs and documentation.
Lean checks the resulting proof terms against their definitions and hypotheses;
that check is separate from the assistance used to write them. It does not
validate the physical assumptions as an experimental model or establish every
claim made elsewhere in this repository.

## Model ↔ Lean: equations, events and assumptions

The one-page [**model-to-Lean correspondence**](docs/MODEL_LEAN_CORRESPONDENCE.md)
maps the pulse shape, READY/FAST/SLOW equations, auxiliary cycle, plasticity,
energy, caps, threshold guards, delivery queues, births and completion to their
exact Lean definitions. Start there to inspect what the proof actually models.
The [kernel guide](kernel/README.md) explains the cell, while the
[archived model](model/full_model_reference.md) retains its original network
context; the archived 18-layer topology is not an assumption of the N=3 theorem.

<details>
<summary>Supporting results, experiments, reproduction and provenance</summary>

### Guides and experiments

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

### Results and scope

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
the settings-copy variant, open recurrence after 800 or adaptive pedagogy. The written
theorems combine hybrid-flow arguments with checked interval obligations;
they are not complete Lean formalizations or independently peer-reviewed mathematics.

The [Lean project](proof/lean/README.md) proves physical flow, reserve and memory
invariants, the constructed N=3 protocol described above, and generic
conditional protocol results. It also checks exact rational certificate endpoints and
recorded cadence/adaptive counters. These evidence checks do not establish
membership of the actual trajectories in every recorded interval. The complete
physical refinement for arbitrary finite chains, retained probes and
indefinite network continuation remain separate obligations.

The [N-cell extension](results/reciprocal_composition/README.md) uses a closed
packet contract and a written induction, supported by 81 N-independent local
inequalities and 12 exact polynomial identities. Physical tolerances stay at
±10% as N grows. Source length and time grow linearly; fast-block traffic is
quadratic at the supplied minimum source length. Per-pulse wire jitter must
obey the path budget; the old 25-pulse train and full ±0.05 jitter per link
are not claimed to work unchanged at arbitrary depth.

### Verify the proofs

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

### Restore recordings or run a fresh experiment

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

### Rebuild the ZIP

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

### Where the robust results live

The robust results are in `research/robust/`, not in `certify/`, `proof/` and `results/`.
They originate in a tested offline package. The numerical sources, certificates and
traces retain their identities; the current guide and its documented provenance
updates adapt that snapshot to this repository. Their protocol is a different, slow-input chain: it is not the fast period-4
packet protocol of the N-cell composition theorem. Their status is that of the other
written theorems: hybrid arguments written by hand, finite inequalities replayed in
independent integer arithmetic, and, in Lean, the chain induction and the certificate
endpoints. Proving each cell's `CellLaw` from the hybrid execution is the open step
([plan](proof/lean/CELLLAW_PLAN.md)).

### Reference boundary and limitations

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

</details>

Source code is [MIT](LICENSE). Documents, proofs, data, certificates and other
non-code material are CC BY 4.0 under [LICENSE-docs.md](LICENSE-docs.md).
