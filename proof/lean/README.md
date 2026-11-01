# Lean formalization of selected Kernel R results

This project checks mathematical lemmas and finite evidence with Lean 4.35.0 and
Mathlib v4.35.0. It is a **partial formalization**. The actual protocol is now
constructed from A's original birth through B's first reverse-contact FIRE in
(344.3,344.9), with cumulative **A28/B15** and its issued reverse token still
pending. The full later hybrid execution and the Python interval
implementations have not been verified in Lean.

## Physical execution foundation

The [hybrid execution guide](HYBRID_EXECUTION.md) maps the operational equations,
proof interfaces and remaining obligations. `Hybrid` and `Refinement` retain
actual coordinates, raw-current origins, pending tokens and emission/dose
ledgers. Their extensions prove birth-family cap, charge and reserve invariants,
mode-local ODE solutions, guarded transitions and a uniform finite-prefix
physical event budget. These invariants alone do not supply future executions.

| Proof layer | Current result | Explicit boundary |
|---|---|---|
| Constructed execution | From the original READY A birth through teaching at 319.9 (A28/B14), then B's first reverse FIRE in (344.3,344.9) (A28/B15) | The reverse token is issued but not received; 28 external B sources plus that wire remain pending |
| Conditional physical protocol | Reciprocal epoch at 459.9 (A38/B27), C teaching at 639.9, complete cadence at 789.9 (A54/B61/C34) | Actual executions reaching the required horizons and genuine staged births are supplied |
| Finite-chain composition | Induction, packet timing, jitter budgets and resource algebra for every finite N | Physical leaf refinement and each local `RelayLaw` remain premises |
| Certificate/record replay | Exact rational endpoints and finite recorded counters | Not trajectory enclosure soundness or a generalization theorem |

The constructive factories take A's READY `BirthState` with initially READY
auxiliaries and the exact 32-source queue, B's independent READY `Newborn`,
independent fixed `PhysicalBox` parameters (±0.3% or ±10%), canonical amplitudes
and the declared contacts. Delays are sampled at each actual emission and lie
in [0.3,0.4]; the backward bound is needed for the saturated reverse-FIRE cut.
There is no supplied reaching execution, recorded case word, desired output
count or assumed firing date. Every source and wire is consumed by an actual
arrival; old memories, reserve and unfinished raw tails are carried forward.
No drift, charge noise or settings-copy operation is asserted by this execution
construction.

The next obligation is receipt of the issued reverse token and the remaining
coupled return cycles. Later C/cadence constructions, retained probes, fine
enclosure soundness and physical every-N refinement remain open. The separate
[robust coverage guide](ROBUST_COVERAGE.md) describes conditional noisy/drifting
slow-chain results.

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
python3 scripts/check_hybrid_cascade_negative.py
python3 scripts/check_hybrid_existence_negative.py
python3 scripts/check_hybrid_weak_existence_negative.py
python3 scripts/check_hybrid_first_fire_negative.py
python3 scripts/check_hybrid_protected_mark_negative.py
python3 scripts/check_hybrid_prepared40_negative.py
python3 scripts/check_hybrid_preparation_existence_negative.py
python3 scripts/check_hybrid_b_birth_product_negative.py
python3 scripts/check_hybrid_first_wire_negative.py
python3 scripts/check_hybrid_first_interleaved_negative.py
python3 scripts/check_hybrid_second_wire_negative.py
python3 scripts/check_hybrid_receiver_fire_negative.py
python3 scripts/check_hybrid_coupled_preparation_negative.py
python3 scripts/check_hybrid_coupled_teaching_negative.py
python3 scripts/check_hybrid_feedback_entry_negative.py
```

The toolchain and dependency commits are pinned in `lean-toolchain` and
`lake-manifest.json`. The first build downloads Mathlib's compiled dependencies.
The build checks proof terms; the audit rejects any project theorem using axioms
other than `propext`, `Classical.choice` and `Quot.sound`. There are no admitted
proofs, project axioms or native-evaluation proofs. The Audit build target uses
Lake's exact artifact paths. Its scan includes every imported and current
`KernelR`/`A22` theorem; negative controls cover corruption in both locations.
Standalone proof controls reuse the same dependency artifacts and compiler
options. `check_hybrid_feedback_entry_negative.py` adds 29 paired controls for
the real B344 weak entry, first residual-dependent B FIRE, issued reverse
token, own memories, A28/B15 and both interval-scoped emitting products. Each
positive conclusion is compiled before its altered version must be rejected.

## Coverage and hypotheses

The table below describes the analytic, abstract and evidence modules. The
physical `Hybrid*` results above and in the [theorem map](HYBRID_EXECUTION.md)
provide additional refinements; an abstract module alone does not construct them.

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
The abstract `Cadence` lemma requires the physical phase ordering as a premise;
the `Hybrid*` local cases and conditional cascade derive their own guards.

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

1. Continue the constructed reverse FIRE through its actual receipt and the
   reciprocal epoch at 459.9, then construct C's birth/teaching and the cadence
   through 789.9. Preserve global queues, own memories and port availability.
2. Prove the remaining real enclosure memberships, retained probe responses,
   causal cuts and protocol extension/saturation obligations. Exact comparisons
   of stored endpoints do not establish these facts.
3. Derive the physical leaf and relay contracts and instantiate the checked
   packet induction for every finite chain.
4. For pedagogy, separately formalize the observation/readout/training interface
   and connect numerical records to that semantics.

The existing [local theorem](../reciprocal_learning/THEOREM.md),
[entry theorem](../reciprocal_entry/THEOREM.md) and
[cadence theorem](../reciprocal_cadence/THEOREM.md) remain computer-assisted
written arguments with independent arithmetic replay. The current partial
formalization and its exact boundaries are detailed in the
[hybrid guide](HYBRID_EXECUTION.md).

## Attribution and license

The five unchanged upstream Lean files come from Nicolas Breuillaud's
`HevisNico/a22-going-further`, commit
`269483eb2c6227b369cffb2c46f86eaae5272bb8`. Their Git blob identities are checked
locally and in CI. Source code, including Lean source, follows the repository's
[MIT license](../../LICENSE); this guide and evidence provenance follow
[CC BY 4.0](../../LICENSE-docs.md).
