# kernel-R

[![Lean proof checks](https://github.com/HevisNico/kernel-R/actions/workflows/lean.yml/badge.svg)](https://github.com/HevisNico/kernel-R/actions/workflows/lean.yml)

**Lean now constructs a pulse-driven learning-and-cadence protocol for every
positive finite directed chain.**

For N independently born cells, fixed independent fabrication parameters and
bounded native wire-delay functions, the declared preparation and K-input
program reaches a complete resting endpoint. Every cell is READY at q=0.1,
with no RAW current and no pending token. Active log-gains and recoveries are
derived from each cell's own birth values; no reaching execution or output
calendar is supplied. The precise scope is stated below.

1. [Result: every finite chain, with explicit scope](#result-every-finite-chain-with-explicit-scope)
2. [Lean headline: signatures, axioms and reproduction](#lean-headline-signatures-axioms-and-reproduction)
3. [Model ↔ Lean: equations, events and assumptions](#model--lean-equations-events-and-assumptions)

## Result: every finite chain, with explicit scope

All N cells are born at time0 in independently chosen READY states. Routes
are closed during16 direct period-eight preparation inputs per cell: the
leaf receives them on port1, each relay on port2. The leaf then receives
K period-four port0 sources from160, with **K≥4N+12**. These future sources
are present in the global queue from birth. Each source and wire is consumed
by an actual arrival; each routed token is issued by an actual FIRE.
Preparation and cadence share **one fixed gated router**, opening at160.

| Derived quantity | Result |
|---|---|
| Terminal time T | `160 + 4*(K-1) + (11/10)*(N-1) + 8` |
| Fast emissions at depth j, leaf j=0 | `K-5-2*j` |
| Root fast emissions | `K-2*N-3` |
| Total fast emissions | `N*(K-N-4)` |
| Total preparation emissions | `12*N+2` |
| Entire birth-to-T emission ledger | `N*(K-N+8)+2` |
| Each active log-gain, leaf port0 / relays port2 | Own birth value +2.4 |
| Each recovery | Own birth value +0.3 |
| Endpoint | All READY/q=0.1, RAW absent, empty global queue |

Other gains retain their physical preparation memories. The energy ODE,
reserve/cap invariants and actual raw-current origins are retained throughout.
Physical cell indices run root-first in Lean; the depth index in the table
runs leaf-first.

The exact quantifier order is:

> **For every positive finite N, admissible K, independent fixed fabrication
> and READY birth data, and admissible native real-time delay functions,
> there exists a complete physical execution of the declared protocol.**

The15 fabrication parameters per cell are chosen independently in either the
±0.3% or ±10% box and are **fixed in time**. Births have q=0.1±10⁻⁵,
b=0.08±10⁻⁵, energy in[50,100], each auxiliary READY with m=0.025±10⁻⁵,
no RAW, and log-gains within10⁻⁵ of log(0.3), log(1.2), log(0.3) on ports0/1/2.
Pulses have the declared canonical width-one exponential shape. Sources,
ports and contact windows are supplied protocol data.

For each link, a fixed centre d and budget σ satisfy
`0≤σ≤0.05` and `0.3+σ≤d≤0.4-σ`; the path sum is at most0.15.
The theorem quantifies over **functions δ(t)** satisfying
`-σ≤δ(t)-d≤σ` at every real time. It samples δ at each actual sending FIRE,
so every wire delay is in[0.3,0.4]. No independence or cancellation of errors
is assumed. The generic full-budget physical receiver now constructs its
output packet and exact count from these actual inputs.

**Limits near the result:** this is constructive existence for the declared
finite directed-chain program and bounded native delay functions. It is not
universal refinement of every admissible execution. A full birth-to-terminal
factory for arbitrary *prescribed per-emission error sequences* remains a
separate realization obligation; the indexed-delay helper alone does not
supply it. Frozen probes, cuts/settings copies and indefinitely operating
networks retain their own obligations. Operational noise/drift research and
simulated observations have separate scopes. See the
[proof ledger](proof/lean/EVERY_N_PLAN.md) and
[coverage map](proof/lean/N_CELL_COVERAGE.md).

The earlier **staged three-cell protocol** remains proved from A's original
birth and independent B/C births at160/480 through **789.9**, with
**A54/B61/C34**, all READY/q=0.1, no RAW and no pending tokens. Its
[original headline](proof/lean/KernelR/Headline.lean) and
[checkpoint map](proof/lean/HYBRID_EXECUTION.md#constructed-protocol-checkpoint)
remain available. The new common-time birth program has different preparation
and traffic; its N=3 instance is not the old staged protocol.

R's structural mechanism is two memories with complementary gates: ERROR
activity increases an input's log-gain while the main cell is READY; protected
MARK activity increases recovery while admission is closed. Gain changes the
response to future inputs; recovery changes the actual SLOW-to-READY return.
The constructed protocol uses both to acquire and transmit cadence. The
[kernel equations](kernel/README.md) and
[model correspondence](docs/MODEL_LEAN_CORRESPONDENCE.md) give their exact gates.

This work draws inspiration from Nicolas Breuillaud's
[*The Reset Operator: A Structural Constraint on Recursivity*](https://ssrn.com/abstract=6964960).
This credits the theoretical inspiration; the paper's broader claims are
not premises or conclusions of the Lean result.

## Lean headline: signatures, axioms and reproduction

[**FiniteChainHeadline.lean**](proof/lean/KernelR/FiniteChainHeadline.lean)
groups three checked statements in `KernelR.Hybrid.FiniteChainHeadline`:

| Declaration | Checked conclusion |
|---|---|
| `every_finite_chain_exists` | Actual birth-to-T witness for every N=n+1, with the exact hypotheses below |
| `terminal_state_and_memories` | Complete resting coordinates, no RAW/tokens, own active log-gain+12/5 and recovery+3/10 |
| `actual_counts` | Actual fast per-cell/root/total counts and cumulative birth-to-T ledger |

<details>
<summary>Exact Lean signatures</summary>

N is represented by n+1; physical index0 is the root and `Fin.last n` the leaf.
Proof bodies are omitted. `finiteChainPreparationPort` selects leaf port1 and
relay port2; `cadenceActivePort` selects leaf port0 and relay port2.

```lean
namespace KernelR.Hybrid.FiniteChainHeadline

theorem every_finite_chain_exists {n θ bornCells K ε}
    (hborn : ∀ i : Fin (n+1), BirthState (bornCells i))
    (hb : @PhysicalBox (n+1) θ ε) (ha : ∀ i q, (bornCells i).aux 0 q=.ready)
    (hqueue : ∀ i, (bornCells i).pending=sourceTrain 0 (finiteChainPreparationPort n i) 0 8 16)
    (sigma centre : ℕ → ℝ) (delay : ℕ → ℝ → ℝ)
    (hK : 4*(n+1)+12≤K) (hsigma : ∀ j, 0≤sigma j)
    (hbudget : KernelR.Chain.pathJitter sigma n≤3/20)
    (hcentre : ∀ j, j<n → (3/10:ℝ)+sigma j≤centre j ∧ centre j≤2/5-sigma j)
    (herror : ∀ j, j<n → ∀ time, -sigma j≤delay j time-centre j ∧ delay j time-centre j≤sigma j) :
    Nonempty (ConstructedBirthCadenceChain θ bornCells K sigma centre delay (cadenceChainTerminal n K))

variable {n θ bornCells K sigma centre delay T}
  (c : @ConstructedBirthCadenceChain n θ bornCells K sigma centre delay T)

theorem terminal_state_and_memories :
    c.final.time=T ∧ (∀ i, ReadyCoordinates c.final i) ∧
    (∀ i, c.final.x i .q=1/10) ∧ (∀ i p, c.final.raw i p=none) ∧
    c.final.pending=[] ∧
    (∀ i, c.final.x i (.z (cadenceActivePort n i))=
      (bornCells i).x 0 (.z (cadenceActivePort n i))+12/5) ∧
    (∀ i, c.final.x i .b=(bornCells i).x 0 .b+3/10)

theorem actual_counts (hK : 4*(n+1)+12≤K) :
    (∀ i, (c.fastExecution.emissionTimes i).length=K-5-2*(n-i.val)) ∧
    (c.fastExecution.emissionTimes 0).length=K-2*(n+1)-3 ∧
    c.fastExecution.ledger.emissions.length=(n+1)*(K-(n+1)-4) ∧
    (∀ i, (c.execution.emissionTimes i).length=
      finiteChainPreparationCount n i+(K-5-2*(n-i.val))) ∧
    c.execution.ledger.emissions.length=(n+1)*(K-(n+1)+8)+2

end KernelR.Hybrid.FiniteChainHeadline
```

`ConstructedBirthCadenceChain` retains the actual preparation, fast execution,
source/parameter equalities, issued and delivered occurrences, and their
concatenation under one router. The count fields refer to actual FIRE ledgers.

</details>

The project pins **Lean 4.35.0** and **Mathlib v4.35.0**, with Mathlib commit
`56a005855ea17e0b0958f73ec801ae140b0a1679` in
[lake-manifest.json](proof/lean/lake-manifest.json).
The exact checked native finite-chain commit is recorded in the
[PR #15 validation table](https://github.com/HevisNico/kernel-R/pull/15).
From the repository root, with Lean installed:

```sh
cd proof/lean
lake exe cache get
lake build KernelR.FiniteChainHeadline
lake build
lake build Audit
```

The three `#print axioms` outputs are:

```text
'KernelR.Hybrid.FiniteChainHeadline.every_finite_chain_exists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'KernelR.Hybrid.FiniteChainHeadline.terminal_state_and_memories' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'KernelR.Hybrid.FiniteChainHeadline.actual_counts' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are Lean's standard logical foundations. The source check rejects
admitted proofs and added project axioms; the global audit checks every
imported/current project theorem against this list. The complete export passes
**9,537 build jobs**, **27,515 audited theorems**, **484 Lean source checks**,
**16 robust certificates**, **12 project tests** and **178 new paired controls**.
The five inherited sources are unchanged. CI configures1,281 paired controls;
this inventory does not claim a new local rerun of every older suite. The
[validation ledger](proof/lean/EVERY_N_PLAN.md) distinguishes checked commits
from fresh CI runs still in progress.
The [full reproduction commands](proof/lean/README.md#reproduce) include source,
evidence and paired corruption controls; the workflow badge reports actual CI.

This work is done with two AI assistants, **Claude** (Anthropic) and **ChatGPT** (OpenAI), under the direction of Nicolas Breuillaud.

AI assists construction of models, code, proofs and documentation. Lean checks
the resulting proof terms against their definitions and hypotheses. That check
does not experimentally validate the physical assumptions or establish every
claim made in the repository.

## Model ↔ Lean: equations, events and assumptions

The [**one-page correspondence**](docs/MODEL_LEAN_CORRESPONDENCE.md) maps main
and auxiliary charges, gain/recovery learning, energy/work, pulses, thresholds,
jumps, caps, fixed parameters and birth families to actual Lean definitions.
The [kernel guide](kernel/README.md) explains the cell; the
[archived model](model/full_model_reference.md) preserves its original network
context. A22 topology and simulations remain supporting material below.

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
invariants, the common-birth finite-chain construction above, the earlier
staged N=3 protocol, and generic conditional results. It also checks exact rational certificate endpoints and
recorded cadence/adaptive counters. These evidence checks do not establish
membership of the actual trajectories in every recorded interval. The native-function chain factory is now constructed. Prescribed indexed-error
realization, retained probes and indefinite network continuation remain separate
obligations.

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
