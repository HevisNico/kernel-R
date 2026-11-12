# Finite native re-preparation checkpoint

[SelectorReprepare.lean](../recursive-learning/native/Teaching/SelectorReprepare.lean)
constructs a native read, return to rest and re-preparation, preserving the
stored selector, with real re-preparation inputs and their pulse cost for a
prepared controller. It works for either selector value. **This checkpoint
does not close M2:** it lacks a prescribed restart calendar and a recurrent
boundary theorem. The subsequent [reusable-round construction](NATIVE_ROUNDS.md)
addresses those obligations. Neither implements the discrete search controller.

## One execution, one fixed router

`read_reprepared_exists` constructs the complete finite execution:

1. Start with a prepared read on port 2 and one future ignition token already
   in the initial queue. Execute the read and its actual FAST/SLOW return.
2. Wait in READY until that token arrives on port 1. Its date is chosen one
   time unit after the constructed return endpoint. This is an existential
   programme parameter, not a timing policy implemented by the cell.
3. The resulting ignition FIRE routes a work token to port 0 and a read token
   to port 2. The work token performs the existing native precharge history.
4. End at admission of the next read: main READY, charge in `[13/20,39/50]`,
   all sensors READY in `RestBand`, raw input on port 2 freshly active, other
   raw inputs absent, queue empty, and the same selector gain.

`reprepareRouter` routes only FIREs in its fixed ignition window
`[origin,origin+1)`. The earlier read does not trigger the new timers. Proof
fragments are transported to this router only after proving agreement at
every actual emission. The combined witness has that router from its initial
snapshot through its final snapshot. No queue is inserted at the intermediate
return boundary; `withFuture` lifts the whole first read and return with the
already queued token. No charge, gain, recovery or energy reset occurs.

## Contracts and non-vacuity

| Statement | Checked result |
|---|---|
| `rest_preparation_exists` | Actual waiting, ignition, work and read-admission history from a quiet READY cell |
| `read_reprepared_exists` | Composes the first read, return and re-preparation under one fixed router |
| `ReadReprepared.pulse_cost` | Exactly three deliveries, including the external ignition |
| `ReadReprepared.gains`, `.recovery` | Every log-gain and the recovery coordinate are retained |
| `RestPreparation.physical`, `ReadReprepared.crossing_exists` | Native physical invariant, transversal contacts and a complete geometric-crossing witness |
| `ReadReprepared.next_read_exists` | The resulting prepared state supports a complete selector read under the existing read interface |
| `prepared_read_reprepared_exists` | Explicit initial snapshots for either value and a constant work delay satisfy the construction |

The endpoint's next-read theorem uses the existing empty-router read
interface. It is an additional existence check, not a proof of repeated
autonomous cycles under the finite ignition router.

The initial snapshot is a resource assumption, not an execution from birth.
The generic theorem requires `PhysicalBox`, an initially physical and
prepared read, recovery `11/10`, ignition gain in `[9/5,11/5]`, and work
log-gain at `log(cap 0)`. Work delay can vary within the existing window
with jitter at most `73/40000`. `reprepareReadStart` explicitly instantiates
charge `7/10`, sensor charge `1/40`, energy `100`, ignition gain `2`, work
gain at cap, and selector log-gain `0` or `3/5`. Its physical invariant and
prepared-read contract are proved, with a constant delay as a witness.

## Cost boundary

The execution's delivery ledger is exactly:

| Input | Source | Charged new deliveries |
|---|---|---:|
| Ignition, port 1 | Initially queued external token | 1 |
| Work, port 0 | Routed by ignition FIRE | 1 |
| Next read, port 2 | Routed by ignition FIRE | 1 |

The first read pulse was admitted before the initial snapshot. Including
that resource gives four input pulses for the finite programme; the theorem
counts three **new** deliveries. There are exactly two FIREs before the
endpoint: the original read and the new ignition. The next read FIRE is
outside this prefix.

Pulse count is not a bound in joules, processor work or elapsed time. The
native energy coordinate obeys the original ODE and physical invariant;
it is not identified with this accounting unit. Preparing the initial gains,
recovery, energy and first input remains outside this count. Full controller
search, reports, writes and learner reset remain cost-refinement obligations.

## Validation

With the pinned Lean 4.35.0 toolchain and native dependencies:

```sh
cd research/recursive-learning/native
lake build
cd ../../reusable-controller
python3 verify_native_reprepare.py --report native-reprepare-validation.json
```

`SelectorReprepareAudit` checks all declarations in `SelectorRead`,
`SelectorReturn`, `CappedWorkRun` and `SelectorReprepare`, including unused,
private and generated declarations and their transitive axiom dependencies.
Only `propext`, `Classical.choice` and `Quot.sound` are allowed. The complete
`NativeAudit` imports this audit as well.

Six isolated controls reject omitting the external input, charging only two
deliveries, changing a retained gain, routing the previous read as ignition,
adding an unused project axiom, and admitting the next-read proof. Parser and
import errors do not count as successful rejection. The original sources and
compiled objects are preserved. The [validation record](native-reprepare-validation.json)
records source hashes and the focused audit; CI rebuilds the whole native
package and repeats both the return and re-preparation controls.

## Adaptive search stays behind the reuse gate

Before any adaptive-search work, M2 requires invariant preservation, a fixed
calendar, an `n`-round physical recurrence and universal complete-run behavior.
The proofs and validation for that stricter scope are in [NATIVE_ROUNDS.md](NATIVE_ROUNDS.md).

M1's fixed search rule has not been changed. The separate [discrete adaptive
milestone](ADAPTIVE.md) now selects coordinate priority, a unit-probe budget
and stopping behavior from a finite family, while leaving evaluation and
acceptance outside mutable state. It constructs policy validation, invariant
preservation, robust adoption and budgets for both levels.

Non-increasing validated policy cost is different from cumulative search
cost: trials consume resources. Total accounting needs a budget and, if
claimed, a separate amortization theorem. With inexact evaluation, true
non-degradation needs robust bounds or acceptance margins; accepting within
a tolerance alone does not prove it. Coupled or order-sensitive learners
also require revisiting M1's permanent blocked-bit argument. The discrete
extension uses certified failure to block and preserves memory on ambiguity;
it does not provide a physical adaptive controller.
