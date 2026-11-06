# Zero recovery can prevent every later firing

A cell in SLOW with charge `q = 1/4` and recovery `b = 0` stays in SLOW
as long as its sensors do not spend positive-duration flow pieces in MARK.
Its charge remains `1/4`, and it emits no further spike. This holds for an
arbitrary network size and router, with no chain protocol or common execution
horizon assumed.

The result is checked directly in the native integral semantics and in the
model's upward-crossing semantics. It uses the unchanged field and jump
definitions. The weak/crossing proof does not rely on a general conversion to
first-contact executions, on transversal contacts, or on the chain theorem.

## Exact contracts

The native statements are in
[`HybridZeroRecovery.lean`](../proof/lean/KernelR/HybridZeroRecovery.lean).
`Execution.zero_recovery_quiet_lock` assumes an actual finite execution and:

- the selected cell starts in SLOW with `q = 1/4` and `b = 0`;
- every sensor of that cell starts READY with charge at most `1/40`;
- no raw pulse is initially active on any of that cell's ports;
- no input delivery to those ports actually occurs in the supplied execution.

It proves the SLOW mode, charge `1/4` and recovery zero at every recorded
snapshot, together with `emissionTimes i = []`. The more general
`Execution.zero_recovery_locked_paths` also proves the two coordinate identities
at every point inside every flow, using the explicit `NoMarkFlows` condition.
Other cells may continue to flow, jump, learn, deliver pulses elsewhere or fire.

The direct model-semantics statement is in
[`HybridZeroRecoveryCrossing.lean`](../proof/lean/KernelR/HybridZeroRecoveryCrossing.lean):

```lean
theorem CrossingExecution.zero_recovery_lock {n θ route s u}
    (e : @CrossingExecution n θ route s u) (i : Fin n)
    (hm : s.main i = .slow) (hq : s.x i .q = 1 / 4) (hb : s.x i .b = 0)
    (hmark : e.execution.NoMarkFlows i) :
    e.execution.ZeroRecoveryLocked i ∧ e.execution.emissionTimes i = []
```

Here `NoMarkFlows` concerns the actual sensor modes on each positive-duration
weak flow. `ZeroRecoveryLocked` records the locked state at every snapshot and
the constant coordinates along every flow. They are separate predicates:
the former is a hypothesis about the missing learning mechanism; the latter
is the proved consequence. No locked-mode conclusion is assumed.

The quiet-sensor input-based corollary is currently stated for native
`Execution`; the arbitrary-network crossing theorem uses its explicit
no-MARK condition. These are the exact scopes of the supplied theorems.

## Why the obstruction holds

Without a MARK sensor, every recovery actuator vanishes. The integral equation
therefore gives `b(t) = b(start) = 0`. In SLOW the main equation is
`q' = -b(t) q`, independently of the direct input current. Thus `q(t) = 1/4`.

A reopening jump requires `q = 1/10`. Since all jumps preserve the continuous
coordinates, none can reopen the selected cell from its unchanged SLOW charge.
FIRE requires READY, so no later firing is possible. The proofs include all
legal zero-time interleavings. The crossing proof applies these facts by direct
induction on the actual weak moves and then restricts to crossing executions.

## Zero recovery is not automatically permanent

The absence of new input pulses by itself is insufficient if a sensor is
already active. A pre-existing MARK phase may still increase recovery. An
active raw pulse may also raise a READY sensor to its threshold even if no
new delivery occurs. This is why the quiet-sensor corollary explicitly
excludes both possibilities.

`Execution.zero_recovery_repaired_by_mark` proves a contrasting exact transfer:
an actual isolated, fully exposed MARK section that drains its sensor from
`1` to `4/5`, starting with `b = 0`, ends with `b = 1/10`. The other ports'
MARK actuators must be closed for this equality. Exposure includes the
protected main mode, positive energy and the open recovery cap.

That theorem assumes the actual exposed section; it does not claim that any
input necessarily creates one. Once recovery is positive, the existing
[`Execution.slow_completion_of_charge`](../proof/lean/KernelR/HybridProtectedReturn.lean)
gives a conditional SLOW return bound for sufficiently long actual executions.
Together these distinguish an unrecovering lock from recovery that can be
restored by learning.

## Nonempty physical witnesses and the meaning of forever

`zeroRecoveryIdleValues` has `q = 1/4`, `b = 0`, READY sensors at `1/40`, no
active or pending input, zero log-gains and energy `99.89`. The energy is the
exact equilibrium for the constant SLOW work rate `1.1`, so every coordinate
has zero field. `zeroRecoveryIdleFlow` constructs an actual flow of any
positive duration. `zeroRecoveryIdle_complete` and
`zeroRecoveryIdle_crossing_complete` construct complete finite native and
crossing executions through any later horizon.

These states satisfy `PhysicalInvariant` for either declared fabrication box.
Zero recovery is allowed by the current physical-state bounds, which require
`0 <= b <= 1.1`; it is not allowed by the nominal birth bounds near `0.08`.
The witnesses therefore concern admissible current states, not a claim that
the chain preparation can drive its initially positive recovery down to zero.

The no-firing theorem quantifies over every supplied finite execution while
the no-MARK condition holds. It is not an independent theorem of existence
or time divergence for all infinite runs. The separately constructed complete
witnesses show that the locked behavior can persist through arbitrarily late
finite horizons.

## Local verification

From `proof/lean`:

```sh
lake build KernelR.HybridZeroRecovery KernelR.HybridZeroRecoveryCrossing
lake env lean ZeroRecoveryAudit.lean
python3 scripts/check_zero_recovery_negative.py
```

The targeted build passed locally with Lean 4.35.0 and the pinned Mathlib
dependencies (3,560 dependency/build jobs). The scoped audit passed for 1,996
project theorem declarations in the imported closure, including imported
auxiliaries. This is not the count of new results: the two new modules declare
19 explicit public theorems. Their printed axiom profiles use only `propext`,
`Classical.choice` and `Quot.sound`.

All 20 paired controls passed. Each of the 19 public theorem contracts has a
positive control and an individually rejected altered conclusion; an extra
pair checks that the no-firing proof does not silently discard the no-MARK
hypothesis. A rejected altered proof is a regression check, not a proof of
the negated statement. The explicit complete physical witnesses provide a
separate constructive non-vacuity check.

These are targeted local checks. They do not by themselves claim a fresh
full-project build or completed remote CI. No equation, guard, parameter box,
birth definition or existing theorem statement is weakened by this milestone.
