# Final scope of this research milestone

The completed deliverable is a standalone Lean/Std package for a **conditional,
finite-prefix, observation-driven repair supervisor**. It now includes the
contract producer, executable selection and repair policies, their physical
interface, composition, cost accounting and concrete checked witnesses.

This closes the implementation/proof tranche in this PR. It is not a claim
that universal physical learning, arbitrary adaptive availability, or the R
hardware correspondence has been established.

## Review extension

[REVIEW_FOLLOWUP.md](REVIEW_FOLLOWUP.md) records subsequent review changes.
The package now also proves perpetual renewal for a funded fixed fallback,
with all-time service conditional on indefinitely valid physical laws; this
is narrower than arbitrary adaptive availability. It adds symbolic observation
costs with exact finite-catalogue constrained minimization, an executable
coupling verifier, and a substantive missing-availability counterexample.

## The end-to-end result

`OfferFactory.system_safe` is the entry point. For the actual plan generated
from a sequence of dated measurements and requested phase lengths, it proves:

- Service holds at every discrete calendar time from dispatch through the
  endpoint of the accepted prefix, including repair interiors and switches.
- The final propagated reserve estimate is a sound lower bound.

`OfferFactory.system_cost` gives the corresponding write bound through the
same executable plan. The lower-level results separately account for actual
switching credit spent, waiting time, write time and search reopenings.

The proof chain is:

`bounded-error measurements -> generated finite-lived offers -> checked admission -> physical transition laws -> composed service and cost`.

The general proof does not assume safety as a premise. It assumes the
measurement, future-evolution and actuator laws listed below, then derives
the previously required transition realization.

## Generated contracts

`OfferFactory.make` takes a timestamped scalar rate reading, its error bound,
a known future slew limit, fixed hardware guarantees and a requested positive
number n of decisions. Before choosing a rate ceiling it computes

`H = n * max(maximum_wait, write_latency)`.

The ceiling is the measurement interval's upper endpoint plus `slew * H`.
The issue time is the measurement time; expiry is issue time plus H. This
horizon includes writes as well as waits and does not depend circularly on
the newly derived ceiling. The coordinator still checks gain, capacity,
entry/handoff reserve, completion, service equality and switching credit.

`propose` rejects a reading whose timestamp differs from the current cursor.
It does not make an old observation fresh by changing its date. Given several
requested phase lengths, candidates are tried in their supplied order.

The hardware fields are preserved exactly; the generator cannot invent a
larger dose or capacity. Stated uncertainty and the known slew determine the
rate ceiling, not a fit to past successes alone.

## Exact assumptions

| Assumption | Scope |
|---|---|
| Sound initial reserve lower bound | At the initial dispatch; later estimates are propagated by proved transitions |
| Bounded rate-measurement error | For each reading used by an executed phase |
| Known upper bound on rate increase | Throughout that reading's entire generated horizon H, including repairs |
| Per-tick reserve dynamics | Reserve loss is no worse than the actual modeled rate for that tick |
| Minimum delayed dose and usable capacity | For the actual commanded writes, stated against accumulated actual loss |
| Fresh measurements and instantaneous boundary dispatch | Observation and switching latency are not modeled as extra timed actions |
| Integer-tick scalar model | Only a lower service specification; no continuous-time circuit or upper read-window theorem |

`OfferFactory.realizes_from_physics` derives the old transition contract from
actual-rate sums and delivery laws. `Supported` ties those assumptions to the
exact readings and selections executed by the program. It requires no future
physical evidence for a suffix that was never dispatched.

The system can block. Its safety theorem then ends at that boundary, not at
an imagined later recovery. The generic observation producer does not guarantee perpetual supply of
admissible contracts, fresh measurements or working actuators. The separate
fixed-fallback availability theorem supplies sufficient conditions for that
policy, including entry funding and persistent physical laws. These conditions
cannot be inferred from the absence of observed failure.

## Concrete completed witness

`FactoryExample` generates both contracts from measurements. The first rate
reading is 2 with zero error; the second is 2 with error one. The actual rate
remains 2. The second certified ceiling rises to 3 because uncertainty rises.
Hardware guarantees remain fixed: dose 10, latency 3, capacity 30, wait cap 4,
and known slew zero. The policy keeps service 10 and handoff reserve 19.

The generated run performs three writes and two waiting ticks over eleven
ticks, spends two switching credits, and reports final lower reserve 22.
The actual reference reserve is 28. The full service and cost statements are
proved using the same general end-to-end theorems. A stale reading is rejected.
These are formal deterministic witnesses, not an empirical comparison.

## Verification and reproduction

With the pinned Lean 4.35.0 distribution on PATH, from this directory:

```sh
python3 -B verify.py --report .lake/validation.json
```

The report records source hashes, the module-based axiom audit, seventy paired
semantic mutation controls and three audit controls. A mutation only counts
when the original compiles and the altered source fails for proof/type
reasons; parser/import/name failures do not count. The audit includes private
and generated declarations and allows only the standard logical axioms
`propext`, `Classical.choice` and `Quot.sound`.

`validation.json` is the recorded local result. The dedicated CI checks the
published commit independently. Existing repository tests are separate from
this proof audit; the historical Kernel R build remains its own CI gate.

## Claims deliberately not made

- No novelty or universal-architecture claim has been established.
- No experimental/transistor validation or fabricated-device guarantee is added.
- The four proposed R/adoption corollaries are not rederived here.
- Full M-matrix equivalence and bounds uniform in tower depth are not proved.
- Future slew, noise, actuator and capacity guarantees are supplied assumptions,
  not learned from an unbounded unknown environment.
- Search/rejection decisions inside a learning epoch and their physical
  correspondence are not implemented by this supervisor.
- The reference-state checkers are not observation-only physical certificates.

`EXPERIMENT_DRAFT.md` remains a design draft. An empirical comparison and an R
bridge need independently specified protocols and actual physical evidence;
they are separate research work, not unfinished claims hidden in this result.
