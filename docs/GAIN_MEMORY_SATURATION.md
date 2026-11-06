# Finite saturation of a port memory

This result concerns the log-gain `z` of one selected input port. The cap is
`c = log(C)`, where `C` is that port's fixed fabrication gain cap.
It is separate from the finite-chain learning/cadence theorem and from
terminal jump saturation.

## Exact result

For a finite actual execution admitting a complete mechanically exposed ERROR
section cover, with initial memory `z0 <= c` and `k` counted sections,

```text
z_final = min(c, z0 + (3/5) * k).
```

Consequently,

```text
z_final = c  iff  ceil((c - z0)/(3/5)) <= k.
```

The ceiling is a natural-number ceiling. A memory already at its cap has
threshold zero. Each full ERROR section runs from sensor charge `1/10` to
`1/40`, so its unconstrained charge transfer is
`8 * (1/10 - 1/40) = 3/5`. The last section may reach the cap before it ends:
its actual increment is then the remaining headroom, not an additional 0.6.

Once this port reaches its cap, every later legal finite execution preserves
that port's log-gain. This permanence statement does not need ERROR exposure,
a section cover, completeness, a chain router or a particular source queue.
The recovery memory `b` and other ports' gains can still change.

## Actual model and native interfaces

The direct upward-crossing statements are in
[HybridCrossingMemorySaturation.lean](../proof/lean/KernelR/HybridCrossingMemorySaturation.lean):

- `CrossingExecution.memory_saturated_iff_count` uses a
  `WeakCappedErrorSectionCover` of the actual weak history carried by the
  crossing execution.
- `WeakCappedErrorSectionCover.gain_eq` gives the full clipped formula.
- `CrossingExecution.gain_stays_at_cap` gives later permanence.

These statements apply to arbitrary finite cell counts, routers and input
queues, conditional on their actual execution/cover premises and the fixed
fabrication box. They do not use a global correspondence between native and
crossing executions. Instead, the existing single-flow strictification leaves
gain, energy and protected ERROR charge unchanged, so the integral result
transfers to weak flows; the weak execution result is then proved directly.

[HybridMemorySaturation.lean](../proof/lean/KernelR/HybridMemorySaturation.lean)
provides parallel native statements `Execution.error_capped_transfer`,
`CappedErrorSectionCover.gain_eq`,
`CappedErrorSectionCover.saturated_iff_count`, and
`Execution.gain_stays_at_cap`.

## Exposure and coverage obligations

`ErrorAvailable` deliberately differs from the older `ErrorExposed`.
Each actual positive flow in a counted section requires:

1. The selected sensor is in ERROR.
2. The main cell is READY.
3. Energy remains strictly positive.

The cap gate is not assumed open. Its exact strict test in the unchanged
`errorAct` field automatically closes at the cap. In the native interface,
`Execution.error_available_of_invariant` derives energy exposure from the
physical invariant, the physical parameter box and the actual mode predicates.

Each counted section has actual entry and exit jumps, all intervening
snapshots in ERROR, and the actual mechanically available span. Other moves
must be inactive for a structural auxiliary/main mode reason. A supplied
zero dose, a closed energy gate, or clipping cannot hide a partial learning
contribution. Initial or terminal unfinished active sections are not counted.

The older strictly exposed `ErrorSectionCover` embeds into the new native
cover by `ErrorSectionCover.toCapped`, preserving its actual count. Its old
uncapped formulas and the original finite-chain witness counts remain valid.
There is no replacement of those statements or of their existing hypotheses.

## Proof structure

For a span ending strictly below cap, monotonic gain implies that every
earlier cap gate was open. The old exact charge balance is therefore usable
in precisely that branch. If the endpoint is at cap, the existing cap barrier
and charge budget identify the clipped value. This proves
`z_out = min(c, z_in + 8 * (m_in - m_out))` from the actual integral field.

Induction on an actual section cover composes these clipped transfers.
Nonnegative additional ERROR doses give
`min(c, min(c,x) + d) = min(c,x+d)`. The exact ceiling criterion follows by
ordered-field arithmetic. Cap permanence follows independently from
nondecreasing gain and the cap barrier.

## Scope and witnesses

This is a conditional finite-section theorem. It does not prove that an
arbitrary input stream produces enough complete READY-exposed ERROR sections,
or that the cell reaches its cap by a universal wall-clock deadline.

A positive-duration complete crossing execution at the cap is constructed by
`saturated_resting_crossing_complete_exists`, with an explicit physical
stationary READY state and unchanged saturated memories. This establishes a
nonempty at-cap permanence setting. It does not establish reachability of that
state from the declared birth family or construct a cap-clipped final section
starting strictly below the cap.

No forgetting mechanism is added. The result concerns the existing port
memory; it is not a theorem that all memories of the entire cell stop changing
or a proof of the general Reset Operator argument for other models.

## Verification

From `proof/lean`:

```sh
lake build KernelR.HybridMemorySaturation KernelR.HybridCrossingMemorySaturation
lake env lean MemorySaturationAudit.lean
python3 scripts/check_memory_saturation_negative.py
lake build
lake build Audit
```

Lean 4.35.0 and Mathlib v4.35.0 remain pinned. The scoped and global audits
permit only `propext`, `Classical.choice` and `Quot.sound`, and reject added
axioms and admitted proofs. See the
[validation ledger](../proof/lean/EVERY_N_PLAN.md#memory-saturation-local-validation)
for the observed checks and their scope.
