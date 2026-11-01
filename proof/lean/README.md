# Lean formalization of selected Kernel R results

This project checks mathematical lemmas and finite evidence with Lean 4.35.0 and
Mathlib v4.35.0. It is a **partial formalization**. Neither the complete hybrid
execution nor the Python interval implementations have been verified in Lean.

## Physical execution foundation

The [hybrid execution notes](HYBRID_EXECUTION.md) describe the operational
semantics and exact ledger balances in `Hybrid` and `Refinement`. These modules
derive memory/queue balances, mode-local ODE solutions and observed guard
endpoints from physical flows and jumps. Their extensions prove birth-family
cap, charge and reserve invariants, including work <=500 and positive energy
throughout reachable flows. `HybridEvents`, `HybridAuxEvents` and
`HybridEventBudget` derive emission chronology and a uniform physical jump budget
for every finite prefix before a bounded horizon, with initial delivery tokens
and bounded routing fanout counted explicitly. The phase-selection and sensor
modules now extract actual protected phases and the complete auxiliary cycle
of a received pulse, with directly proved real timing bounds. Variable-gain
READY comparisons retain every active raw tail. An isolated low-gain input now
has no actual emissions, a total ERROR dose of 3/5 and unchanged recovery. A
learned input emits exactly once, with its actual firing extracted in the real
(3/10,9/10) bracket.
From the declared prepared section this learned-input case now returns before
6.990787, preserves all gains and recovery, and restores READY at exact resting
charge. Its actual firing equation retains the initial residual charge.
A broader silent case now covers the nominal fast gain and low birth recovery,
preserving READY charge/sensor bands before the next input. The learned case
also covers actual gains in [1.8,2.4]. The first strong low-recovery input
remains SLOW at the next input; its following protected input supplies MARK 1/10
and restores the prepared section without emissions or gain changes.

The first complete source phase is now derived from a READY birth: with the
initial queue 0,8,...,120 on a low port, empty routing and an actual execution
complete through any T>=128 (including 159.9), it reaches the prepared section
with exactly 12 emissions, total receiving ERROR 1.8 and MARK 0.1. Source-token
conservation selects every actual arrival. The proof derives three silent
inputs, the first strong input, the protected input and the learned remainder.
It does not assume their case word or counts. A receiving-cell refinement also retains other cells’ arrivals and derives
prepared-train counts for arbitrary input gaps of at least 7.5. Cell-specific
source conservation permits outgoing routes and future tokens at other cells.
Prepared cases and their variable-gap trains can now be proved directly from
the current physical region and raw-origin validity, at arbitrary starting
times. The earlier birth-reachable statements are retained as corollaries.
A current-state physical invariant now also propagates gain/recovery caps and
reserve in [50,100]. It derives positive ERROR/MARK exposure, so the silent,
first-strong and protected-input cases can be reused from current bounds.
An explicit birth event now appends a fresh READY cell at the current date,
retaining existing cells and all their pending tokens. Its independent new
parameters and source queue are explicit; physical bounds and memory balances
compose across the two execution phases.
The first physical phase is now also derived with both source trains already
in the initial queue: a genuine execution cut at 128 retains the remaining
trajectory and future tokens. An actual endpoint at 160 is still prepared with
12 emissions, ERROR 1.8 and MARK 0.1, whether the source due at 160 is pending or
already delivered. This preparation transfers across a birth at that date.
A separated prepared train starting at exact resting charge now also has its
actual emission calendar: every input date plus one unique real response-root
latency in (0.3,0.9), derived from its preserved physical gain. This retains
other-cell traffic and does not assume a latency box.
Gated-contact conservation now derives actual wire inputs from those physical
emissions, retaining future external sources and other-cell traffic. Once A's
input at 160 is active with its fifteen successors pending, the A-to-B contact
gives exactly sixteen B arrivals before 281.3 and period-eight gaps in [7.9,8.1]
with independent wire jitter. This is now connected to both source/birth orders
at 160 and B's complete response. The concrete forward [160,310) and reverse
[320,470) contacts give a conditional physical theorem at 319.9: A has 28 total
emissions, B has 14, and both are prepared at exact resting charge with their
own derived learning and recovery. No received calendar, case word or output
count is assumed. The phase executions and birth remain premises.
The B-to-A return is now connected too: B's direct sixteen sources yield three
silent inputs and thirteen outputs; their actual delayed arrivals yield three
silent A inputs and ten outputs. At 459.9 the cumulative counts are A=38/B=27,
with prepared resting states, raw validity, physical reserve and each cell's
own derived memories. The first strong output retains its residual-dependent
latency; only later prepared outputs share the rest latency. B's next train at
480..600 remains in its initial birth queue throughout the entry proof.
The physical prefix now continues through C's genuine birth at 480 and its
teaching endpoint at 639.9. The future B source train is conserved through the
return, and both old cells stay prepared up to 480. Whether source 480 is still
pending or already delivered, birth preserves B's coordinates and actual
remaining queue. B's sixteen prepared outputs give C sixteen real wire inputs
on its own fast port; C emits fourteen times and gains ERROR 0.6 and MARK 0.1.
A remains quiescent with unchanged memories. C's gains and recovery are measured
from its own newborn coordinates, with independent fabrication parameters.
The composed `CEntry` theorem derives cumulative A=38/B=43/C=14 from A's original
birth, given the actual executions and both birth events. At 639.9 all cells
are prepared at exact resting charge without raw current; A/B queues are empty
and C retains exactly its external birth sources. A corollary retains all
twenty-five period-four inputs 640,644,...,736 on C port 0 in that same queue.
It does not yet classify their fast responses.
The cadence contacts C-to-B-to-A and C's twenty-five period-four source inputs
are now instantiated too. From the actual C-entry state, source conservation
and receiving-cell cuts derive the three weak C inputs and reach the fresh
fourth input at 652. Their ERROR is 1.8 and MARK is zero. The real carried
charge lies in [0.1,0.3]; it is not reset to rest. A/B remain idle and their
queues empty while all twenty-one later C sources 656..736 remain pending.
The supplied complete execution still reaches 789.9; this prelude theorem
only identifies its prefix through 652.

The local period-four pulse cases are now derived directly from current
physical states: the first strong input, protected MARK-only input, second
strong input, mixed MARK-then-ERROR input, and final high-gain learned train.
In the mixed case the real SLOW return lies between 0.5 and 0.99 after input;
the remaining raw current is integrated, produces no extra output, and gives
the full ERROR 0.6 after the full MARK 0.1. Its final charge retains its actual
residue. The MARK clock includes its finite exponential ramp. High-gain learned
inputs settle before 3.8 with one output and unchanged memories. A direct real
enclosure puts the three-dose rest latency in (0.65,0.66), without certificate
membership premises. These are local cases under explicit current-state/gap
bounds. Their assembly into the complete C20/B18/A16 cascade remains open,
as do fine enclosure membership, probes, global existence/progress and the
complete execution-to-abstraction theorem.

## Reproduce

Install [elan](https://github.com/leanprover/elan), then from this directory:

```sh
lake exe cache get
lake build
lake build Audit
python3 scripts/check_audit_negative.py
python3 scripts/generate_evidence.py --check
python3 scripts/robust_evidence.py --check
python3 scripts/check_sources.py
python3 scripts/check_negative.py
python3 scripts/check_hybrid_negative.py
python3 scripts/check_hybrid_analytic_negative.py
python3 scripts/check_hybrid_event_negative.py
python3 scripts/check_hybrid_phase_negative.py
python3 scripts/check_hybrid_pulse_negative.py
python3 scripts/check_hybrid_return_negative.py
python3 scripts/check_hybrid_training_negative.py
python3 scripts/check_hybrid_bootstrap_negative.py
python3 scripts/check_hybrid_protected_negative.py
python3 scripts/check_hybrid_source_negative.py
python3 scripts/check_hybrid_cell_negative.py
python3 scripts/check_hybrid_local_negative.py
python3 scripts/check_hybrid_invariant_negative.py
python3 scripts/check_hybrid_staged_negative.py
python3 scripts/check_hybrid_boundary_negative.py
python3 scripts/check_hybrid_calendar_negative.py
python3 scripts/check_hybrid_routed_negative.py
python3 scripts/check_hybrid_teaching_negative.py
python3 scripts/check_hybrid_reciprocal_negative.py
python3 scripts/check_hybrid_c_introduction_negative.py
python3 scripts/check_hybrid_cadence_negative.py
```

The toolchain and dependency commits are pinned in `lean-toolchain` and
`lake-manifest.json`. The first build downloads Mathlib's compiled dependencies.
The build checks proof terms; the audit rejects any project theorem using axioms
other than `propext`, `Classical.choice` and `Quot.sound`. There are no admitted
proofs, project axioms or native-evaluation proofs. The Audit build target uses
Lake's exact artifact paths. Its scan includes every imported and current
`KernelR`/`A22` theorem; negative controls cover corruption in both locations.
Standalone proof controls reuse the same dependency artifacts and compiler
options.

## Coverage and hypotheses

The [robust coverage guide](ROBUST_COVERAGE.md) covers the additional birth,
noise-dependent latency and arbitrary-depth slow-chain formalization.

| Module | What Lean establishes | Remaining premise or boundary |
|---|---|---|
| `Doses` | Fundamental-theorem-of-calculus charge balance; full ERROR dose 3/5, full MARK dose 1/10; exponential gain after three doses; recovery entry interval | The charge derivative, integrability, mode endpoints and lack of clipping must hold on the relevant interval |
| `Flow` | Exponential decay solves a single mode; FAST ends at 1/4; SLOW returns at accumulated recovery log(5/2); protected charge inequality | A mode-local result; it does not construct a hybrid execution |
| `Recovery` | Bounds on the actual real logarithms log(5/2) and log(4), return before 6.990787 and protection throughout the specified dose window | The displayed bounds on recovery, firing latency and accumulated integral |
| `Calendar` | Routed latency hulls, gaps in [7.5,8.5], disjoint pulses, causal delay, quiescence and preservation of intervals under fixed latency | The latency and duration enclosures |
| `Energy` | Integrating-factor barrier; reserve stays in [50,100] on a smooth interval with work in [0,500]; explicit constant-work comparison bounds | The derivative and work bounds must hold; the separate `HybridWork` module derives the work bound and composes the birth-family reserve invariant across hybrid events |
| `Protocol` | Cycle counts 13/10 for local feedback and 38/27 for the composed words, dose updates and logical composition | The words are supplied abstractions; producing those words from the hybrid equations is not proved |
| `Cadence` | Four pulse cases, including MARK followed by full ERROR; integral of the exponential MARK profile; post-MARK return equation and monotonicity; two extra MARK doses and four total ERROR doses; retained wire jitter after shared-latency cancellation | Physical guards, clipping inactivity, the validity of the phase decomposition and the interval enclosures remain separate obligations |
| `CadenceRecorded/*` | Per-input cumulative dose counters for both 95-case traces, teaching counts 16/14, fast counts 20/18/16, route input/output counts and totals A=54/B=61/C=34 composed with the earlier cycle words | Case labels and recorded counters are inputs; the hybrid equations are not proved to produce these traces |
| `Inheritance` | Bounded monotone copying, idempotence, deterministic readout under exact copying, impossibility of erasing acquired increases with monotone memory | A supplied mathematical copying operation; no claim of physical realization or invented pedagogy |
| `Adaptive` | Stop at the first `notLate` observation, budget bounds, independence from future observations after stopping and from final grades | Categories and decoder are supplied; learning them is not formalized |
| `Intervals` | Exact rational interval algebra and transfer of endpoint order to enclosed real values | Membership of the real quantities in the boxes is an explicit hypothesis |
| `Certificates/*` | 2,402 endpoint-order obligations and validity of 5,964 intervals, across the two local, two entry, two cadence and two N-cell certificates | These are exact rational checks of the published endpoints, **not** proofs that exp/log evaluations or model trajectories lie in the intervals |
| `Recorded` | Exact finite replay: 140/160 and 147/160 successes; 882 and 873 student pulses; four fixed-duration scores per lot | Recorded observations and grade flags are inputs, not formally derived from differential equations; this is no statistical or generalization theorem |

The five upstream modules `StrictRoot`, `PeakBounds`, `CommutationE`,
`FirstCrossing` and `FutureWave` supply reusable interval/root/READY/latency lemmas.
They retain their original hypotheses and explanatory scope comments. Importing
them does not import a proof of the whole A22 network or extend that network's
perturbation range to ±10%. See [upstream provenance](evidence/UPSTREAM.json).

## How the evidence is connected

`scripts/generate_evidence.py` reads the eight certificates already in
[results](../../results) and the adaptive evaluation inside the repository's
[pinned prototype ZIP](../../downloads/R_Reciprocal_Prototype.zip). It validates
the ZIP and its manifest using the existing repository verifier. It does not
duplicate the raw recordings. Input SHA-256 identities are recorded in
[GENERATED_FROM.json](evidence/GENERATED_FROM.json).

The emitter converts decimal strings to exact rational literals. Lean proves
each emitted inequality with `norm_num`, and the finite replay with `decide`.
The emitter is not in the logical trust base of these individual propositions:
a wrong inequality cannot acquire a valid proof through code generation. The
correspondence between the emitted proposition and the intended model still
needs review; hashes and regeneration checks establish provenance, not semantics.

The adaptive records have been recomputed with the complete source/runtime
manifest on the original seeds. The emitter checks the bundled source hashes,
runtime metadata and actual learned policy before extracting outcomes. The
plan and policy hashes are recorded alongside the evaluation hash.

The adaptive replay uses the explicit stop rule equivalent to the reported
learned policy on these records. Python also checks the retained success flags
against the saved eight probe windows. That extraction check uses the original
numeric recordings; Lean proves only the resulting finite Boolean/list claims.
Teacher-query pulses remain separate from the reported student pulse totals.

## C → B → A extension

The cadence theorem requires more than reusing the earlier three-case cycle
model. `Cadence.PulseCase.markThenError` gives one MARK dose and one ERROR dose
without an emission. `CadenceRecorded` checks the accumulated counters after
**every** input, including those combined cases. The old `Protocol` abstraction
retains its original, narrower scope.

The new analytic lemma integrates the exponential MARK profile to obtain
`(b + 0.1) * u - J`, with
`J = 0.1 * tau + (0.1 - 0.4 * log(5/4)) / Lm`. The return identity uses that
deficit; it does not approximate MARK as an instantaneous jump in recovery.
The required physical phase ordering remains a guard obligation.

Shared firing latencies can cancel between dates, but fresh per-pulse wire
delays cannot. The new calendar lemma retains `d₂ - d₁` and proves the
[3.9,4.1] gap bound for a period-4 source and one wire with delays in [0.3,0.4],
or [3.8,4.2] for the two-wire C→B→A path with shared latencies.
A checked counterexample prevents an exact period-preservation claim under
independent jitter. This bound applies to the stated common-latency case;
skipped emissions and changed gains need their own calendar hypotheses.

The two cadence certificates add 2,060 strict comparisons and 5,066 interval
validity checks. Their generated files are split into chunks of at most 160
checks, with aggregate theorems importing every chunk. This limits individual
compilation size while preserving the exact published inputs. Neither the
retained 4/8→8/8 probes nor the causal cuts are upgraded to complete Lean
theorems of the hybrid system by this arithmetic/trace replay.

## Every finite N: compositional extension

The [N-cell coverage guide](N_CELL_COVERAGE.md) maps the written argument to
`Chain.Packets`, `Chain.Induction`, `Chain.Refinement`, `Chain.Algebra` and
`Chain.Consequences`. Lean checks packet-date closure, induction for arbitrary
finite depth, nonuniform jitter budgets, natural emission/traffic counts, dose
words, conditional cut propagation and terminal-time bounds. Both N-cell
certificates add 162 exact endpoint comparisons and 352 interval-validity checks.

The physical leaf and relay refinements remain explicit premises. The extension
does not claim a complete formal proof of the R hybrid trajectories or interval
enclosure soundness. In particular, the finite-chain theorem is conditional on
local contracts, while its induction and resource algebra are proved in Lean.

## What remains to close the complete proof

1. Instantiate and review the fixed-population and staged-birth semantics for
   the supplied protocols, including routing, simultaneous events and progress.
2. Prove soundness of the interval arithmetic and the exp/log enclosures used by
   the certificate checker, or derive the necessary enclosures directly in Lean.
3. Derive the actual pulse cases, strict cap inactivity and birth-to-section
   transition. The common birth-family energy/cap invariants are now proved,
   but do not establish the protocol chronology.
4. Instantiate the composition rule to obtain the complete reciprocal theorem.
5. For pedagogy, separately formalize the observation/readout/training interface
   and connect numerical records to that semantics.

The existing [local theorem](../reciprocal_learning/THEOREM.md),
[entry theorem](../reciprocal_entry/THEOREM.md) and
[cadence theorem](../reciprocal_cadence/THEOREM.md) therefore remain computer-assisted
written arguments with independent arithmetic replay. This project strengthens
selected parts without upgrading their overall status to fully formalized.

## Attribution and license

The five unchanged upstream Lean files come from Nicolas Breuillaud's
`HevisNico/a22-going-further`, commit
`269483eb2c6227b369cffb2c46f86eaae5272bb8`. Their Git blob identities are checked
locally and in CI. Source code, including Lean source, follows the repository's
[MIT license](../../LICENSE); this guide and evidence provenance follow
[CC BY 4.0](../../LICENSE-docs.md).
