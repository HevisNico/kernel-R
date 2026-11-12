# Read-to-rest checkpoint

The native [SelectorReturn.lean](../recursive-learning/native/Teaching/SelectorReturn.lean)
constructs a continuation after either selector read outcome. This closes
the return sub-obligation, not the whole reusable-round milestone.
The subsequent [finite re-preparation proof](NATIVE_REPREPARE.md) closes the
minimal M2 continuation and its input count under explicit initial-resource
assumptions. This document records the narrower return result.

## Constructed, checked statements

- `selector_read_return_exists`: from `SelectorReadPrepared` and strictly
  positive recovery, construct the read and its FAST/SLOW tail. The initial
  read is itself constructed; no future execution is assumed.
- The tail reaches its exact exponential guard, takes the native `fastEnd`
  and/or `reopen` jumps, and finishes in READY with charge exactly `1/10`.
- Every sensor is READY in `RestBand`; raw inputs are absent and the queue
  is empty. The existing read constructor now exports its actual sensor
  rest bands and empty delivery ledger, including the active sensor's
  return and the other sensors' retained residues.
- Every log-gain and the recovery coordinate are preserved. The entire
  read plus tail emits exactly the original read FIRE and has no deliveries.
- The witness is complete through its endpoint and has transversal
  contacts. For an initially physical snapshot and `PhysicalBox`, the
  native execution preserves `PhysicalInvariant`, including reserve.
  Energy evolves by the native ODE; it is not replaced by an initial value.

The generic return helpers allow an arbitrary router, since their tail
has no FIRE. The combined read witness uses the existing empty router.
This does not establish reuse under a nonempty fixed controller router.

## Necessary boundary conditions, not hidden repairs

`SelectorReadPrepared` allows recovery zero. That is sufficient for the
protected read horizon but not a SLOW return. The new theorem requires
positive recovery explicitly; the capped controller's `11/10` meets it.
`zero_recovery_slow_orbit` proves that the zero-rate incoming SLOW orbit
stays above the reopen guard. It is not claimed as a general reachability
theorem for arbitrary external inputs.

Return also does not imply re-preparation. `QuietMainReturn.not_prepared`
proves this directly: `1/10` fails the prepared read's lower charge bound
`13/20`. This prevents a proof from silently treating a returned snapshot
as a new read-ready snapshot.

## Obligation discharged by the subsequent M2 proof

Construct actual input admission and precharge from the returned boundary,
preserving memories, handling every sensor/raw/queue event and charging for
every required input. Any initial source queue must be explicit; changing
time, charge or the queue by definition is not a continuation. The starting
gain and recovery preparation assumptions must remain visible.

[NATIVE_REPREPARE.md](NATIVE_REPREPARE.md) supplies that construction for a
finite programme with an initially queued ignition token. No autonomous
multi-round reuse, report/decode refinement or full controller cost theorem
is certified by this checkpoint.

## Reproduce and audit

This part needs the native package and Mathlib, unlike the discrete package.
With Lean 4.35.0 and its native dependencies installed:

```sh
cd research/recursive-learning/native
lake build Teaching.SelectorReturnAudit
cd ../../reusable-controller
python3 verify_native_return.py --report native-return-validation.json
```

The focused audit checks every declaration from `Teaching.SelectorRead`
and `Teaching.SelectorReturn`, including private/generated declarations
and unused axioms, and traverses their proof dependencies. Only `propext`,
`Classical.choice` and `Quot.sound` are allowed. The package-wide
`NativeAudit` imports this audit too.

Six isolated semantic mutations test zero recovery, invented prepared
charge, altered retained gains, reset sensor residues, an unused project
axiom and an admitted physical-return proof. Parser or import failures
do not count as successful rejection. The original sources and compiled
objects are not modified by the controls.

The local [validation record](native-return-validation.json) covers this
targeted build and audit, not a local build of every native module. The
native CI workflow builds the full package and repeats these controls.
Audit declaration counts measure coverage, not scientific contributions.
