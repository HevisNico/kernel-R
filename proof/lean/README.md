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
throughout reachable flows. Protocol-specific chronology, the remaining real
enclosures, progress and the complete execution-to-abstraction theorem remain open.

## Reproduce

Install [elan](https://github.com/leanprover/elan), then from this directory:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
python3 scripts/generate_evidence.py --check
python3 scripts/check_sources.py
python3 scripts/check_negative.py
python3 scripts/check_hybrid_negative.py
python3 scripts/check_hybrid_analytic_negative.py
```

The toolchain and dependency commits are pinned in `lean-toolchain` and
`lake-manifest.json`. The first build downloads Mathlib's compiled dependencies.
The build checks proof terms; the audit rejects any project theorem using axioms
other than `propext`, `Classical.choice` and `Quot.sound`. There are no admitted
proofs, project axioms or native-evaluation proofs.

## Coverage and hypotheses

| Module | What Lean establishes | Remaining premise or boundary |
|---|---|---|
| `Doses` | Fundamental-theorem-of-calculus charge balance; full ERROR dose 3/5, full MARK dose 1/10; exponential gain after three doses; recovery entry interval | The charge derivative, integrability, mode endpoints and lack of clipping must hold on the relevant interval |
| `Flow` | Exponential decay solves a single mode; FAST ends at 1/4; SLOW returns at accumulated recovery log(5/2); protected charge inequality | A mode-local result; it does not construct a hybrid execution |
| `Recovery` | Bounds on the actual real logarithms log(5/2) and log(4), return before 6.990787 and protection throughout the specified dose window | The displayed bounds on recovery, firing latency and accumulated integral |
| `Calendar` | Routed latency hulls, gaps in [7.5,8.5], disjoint pulses, causal delay, quiescence and preservation of intervals under fixed latency | The latency and duration enclosures |
| `Energy` | Integrating-factor barrier; reserve stays in [50,100] on a smooth interval with work in [0,500]; explicit constant-work comparison bounds | The derivative and work bounds must hold; composition across hybrid event boundaries is not proved |
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

1. Instantiate and extend the hybrid semantics for the supplied protocols,
   including staged births, routing, simultaneous events and execution progress.
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
