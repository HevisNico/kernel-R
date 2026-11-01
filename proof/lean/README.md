# Lean formalization of selected Kernel R results

This project checks mathematical lemmas and finite evidence with Lean 4.35.0 and
Mathlib v4.35.0. It is a **partial formalization**. The actual protocol is now
constructed from A's original birth through **639.9**, including independent
B/C births at160/480, actual teaching sources, wire receipts and guarded returns.
Cumulative counts are **A38/B43/C14**, with exactly **25** later Cport0
sources640..736. All three cells are prepared at q=0.1 with RAW absent and
own acquired memories retained. The later cadence execution remains conditional;
the Python interval implementations have not been verified in Lean.

## Physical execution foundation

The [hybrid execution guide](HYBRID_EXECUTION.md) maps the operational equations,
proof interfaces and remaining obligations. `Hybrid` and `Refinement` retain
actual coordinates, raw-current origins, pending tokens and emission/dose
ledgers. Their extensions prove birth-family cap, charge and reserve invariants,
mode-local ODE solutions, guarded transitions and a uniform finite-prefix
physical event budget. These invariants alone do not supply future executions.

| Proof layer | Current result | Explicit boundary |
|---|---|---|
| Constructed execution | From the original READY A birth through the reciprocal epoch at459.9 and C teaching at639.9; A38/B43/C14 | Three cells prepared/q=0.1, RAW absent; exact25 C640..736 sources and own memories retained |
| Conditional physical protocol | Complete cadence at789.9 (A54/B61/C34) | The later actual execution is supplied; both genuine births and the prefix through639.9 are constructed |
| Finite-chain composition | Induction, packet timing, jitter budgets and resource algebra for every finite N | Physical leaf refinement and each local `RelayLaw` remain premises |
| Certificate/record replay | Exact rational endpoints and finite recorded counters | Not trajectory enclosure soundness or a generalization theorem |

The constructive factories take A's READY `BirthState` with initially READY
auxiliaries and the exact 32-source queue, B's and C's independent READY `Newborn`s,
independent fixed `PhysicalBox` parameters (±0.3% or ±10%), canonical amplitudes
and the declared contacts. Delays are sampled at each actual emission and lie
in [0.3,0.4]; the backward bound supplies the actual reverse receipt.
There is no supplied reaching execution, recorded case word, desired output
count or assumed firing date. Every source and wire is consumed by an actual
arrival; old memories, reserve and unfinished raw tails are carried forward.
No drift, charge noise or settings-copy operation is asserted by this execution
construction.

At352, A is main READY with auxiliaries in their READY rest bands, no RAW
and its actual charge at least0.1. Its exact cut and continuation to H+7.5
are retained; no A `PreparedSection` or charge reset is assumed. A's own
birth port2 log-gain has gained0.6, while B's own independent newborn port2
log-gain has gained1.8. Other gains and both recoveries are preserved; on
the receipt-to352 suffix ERROR is zero elsewhere and total recovery is zero.
The [checkpoint/factory map](HYBRID_EXECUTION.md#constructed-protocol-checkpoint)
retains this352 checkpoint and describes the subsequent complete construction.

`birth_protocol_reverse_teaching_exists` in
[HybridBirthReverseTeaching](KernelR/HybridBirthReverseTeaching.lean) returns a
`ConstructedReverseTeaching` containing the original staged birth-to459.9 trace. A's three real weak reverse inputs derive
ERROR1.8; its first learned response keeps the carried charge. Nine further
coupled cycles for B376..440 return both cells before the final quiet wait.
At459.9 A's own port0/port2 log-gains have each gained1.8, B's own port1/port2
log-gains have gained0.6/1.8, and both own birth recoveries have gained0.1.
Other gains are unchanged. The only pending tokens are B480..600.

`birth_protocol_c_teaching_exists` in
[HybridBirthCTeaching](KernelR/HybridBirthCTeaching.lean) returns
`ConstructedCTeaching` with the staged original-birth trace through639.9.
C's genuine480 birth retains A/B and adds its independent newborn state.
The actual first weak receipt is cut at488 without a charge reset. At496,
C's first learned response retains its low-recovery SLOW path until the next actual wire;
its protected MARK derives recovery+0.1 and the prepared504 section.
Thirteen actual B-to-C learned cycles finish at608, followed by a real quiet
wait to639.9. A stays physically quiet from459.9 and keeps its own memories.
C's own port1 log-gain gains0.6, its own recovery gains0.1, and its ports0/2
are unchanged. All earlier A/B memories remain. The final queue is exactly25
Cport0 sources640..736, with `CompleteThrough639.9`.

The next construction is the period-four cadence through789.9. Its conditional
analysis already derives later counts and memories from a supplied execution.
Retained probes, fine enclosure soundness and physical every-N refinement remain
open. The separate [robust coverage guide](ROBUST_COVERAGE.md) describes
conditional noisy/drifting slow-chain results.

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
python3 scripts/check_hybrid_reverse_receipt_negative.py
python3 scripts/check_hybrid_reverse_epoch_negative.py
python3 scripts/check_hybrid_c_teaching_existence_negative.py
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
The 40 paired controls in `check_hybrid_reverse_receipt_negative.py` also pass
for the actual reverse receipt and352 handoff, real sender clocks and RAW
expiry, retained weak continuation, own memories, exact source/wire queues,
A28/B15 and27 sources. The 40 additional paired controls in
`check_hybrid_reverse_epoch_negative.py` cover the subsequent real receipts,
weak cuts, learned cycles, source induction and original-birth459.9 factory.
All 40 valid conclusions compile and their altered versions are rejected.
The 50 new pairs in `check_hybrid_c_teaching_existence_negative.py` pass for
the actual C birth, retained weak/SLOW paths, protected MARK, real three-cell
execution, own memories, A38/B43/C14 and exact 25-source queue. Every valid
conclusion compiles and every altered conclusion is rejected.
The complete build passes 9,407 jobs; the global audit checks 23,998 project
theorems using only the three allowed logical axioms. Source identities pass
for 354 Lean files and five unchanged upstream modules. Generated evidence,
all 16 robust certificates and 12 project tests pass. CI includes 646 paired
controls in total; fresh CI status is reported separately on the PR.

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

1. Continue the constructed639.9 endpoint through the period-four cadence
   to789.9. Its conditional analysis is already checked. Preserve global queues, own
   memories, actual wire provenance and port availability.
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
