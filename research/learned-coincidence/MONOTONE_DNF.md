# Design addendum · Learned AND–OR cascade

## Training and membership

Layer 1 trains each conjunction $T_a$ by reading its active external target ports together. A silent read doses every active target port, and FIRE ends the writes. Layer 2 is disabled during this stage. The first-layer checker keeps the previous stopping, rail and full-cube margin conditions. This new class accepts unary conjunctions and puts the held-out suite at the external cascade boundary.

Freeze layer 1, then train each selected port $a$ of each layer-2 cell $i$ **in isolation**. Broadcast the external pattern $T_a$ and route the actual layer-1 FIREs to the addressed learner. With the other upstream outputs silent, the slot delivers a single pulse on line $a$. The learner adds a dose only on silence and only to ports that actually arrived. Later presentations of the same isolated line cease writing as soon as it fires. Each selected pair receives $Q_2+1$ presentations in distinct settled slots. The predicted need is computed from the training parameters and plays no part in the update. During tests both layers are read-only.

The reachability check is exact for the specified router, which presents all upstream outputs to the addressed learner. The external mask $T_a$ is the smallest mask that fires line $a$. It isolates that line precisely when every other target has a bit outside $T_a$. If a different target is contained in $T_a$, that line also fires on every external mask that fires $a$. This check applies to every upstream line selected by any downstream learner. For example, with upstream targets $\{0\}$ and $\{0,1\}$, the second line cannot be taught in isolation under this router.

The downstream checker requires early silence and robust stop on each selected singleton, bounded write counts and strict rail headroom. It certifies test FIRE on each trained selected singleton and silence on the maximal pattern of *unselected* lines. All gains are nonnegative, so any incoming mask with a selected line fires, and every mask without one stays silent. A configured constant output has no selected lines. With none selected, a sufficiently high fixed help term certifies FIRE even on the empty read, and a sufficiently low one certifies silence even on all available lines.

## Expressive power

A downstream output with selected upstream lines $U_i$ expresses the disjunction of the conjunctions $\{T_a:a\in U_i\}$. This is monotone disjunctive normal form (DNF). For a nonconstant monotone function on a finite Boolean cube, the minimal true input sets are nonempty and form an antichain. Use one upstream cell for each such set, and select all their lines at the downstream output. Presenting the term itself fires exactly its own line, because no other minimal true set is contained in it. Thus the single-line reachability requirement is satisfiable for this construction. A shared layer for several outputs still needs the reachability check on its actual list of terms.

The design uses **fixed bias for the two constants**, with zero selected lines and no training writes. Constant false is the empty disjunction. Constant true uses a fixed threshold-crossing help term on a read, including one with no active input. Neither requires a synthetic training pulse. This is a guarded choice. A native realization of constant true needs a genuine read gate and a qualifying biased read of the empty mask. Placing a singleton in layer 1 realizes a one-bit projection. The characterization concerns arbitrary finite $M$ and enough upstream cells for its minimal true sets. It gives no polynomial bound on the number of terms.

| Function | Upstream terms selected by the downstream cell |
| --- | --- |
| Majority of 3 | 01, 02, 12 |
| 2-of-4 | 01, 02, 03, 12, 13, 23 |
| $(A\land B)\lor(C\land D)$ | AB, CD |

The Lean examples check membership and all truth-table entries. They compute the predicted Boolean response, which is the specification for the later training proof. A finite XOR control exhibits input $\{0\}$ with output true and its superset $\{0,1\}$ with output false. Adding a bit therefore violates the monotonicity needed for realizability.

## Frozen targets and calibration

[MonotoneTarget.lean](MonotoneTarget.lean) states two propositions. `MonotoneCharacterization` gives the equivalence between monotonicity and realization by an admissible guarded parameter tuple. `TwoLayerMonotoneRecognition` specifies the observed singleton admissions, exact per-port stopping counts, rail safety and the DNF test outputs. The latter is conditional on complete read observations and separated, settled training slots.

Its named `CascadeCalibration` premise reuses `CalibratedAdditiveRead` with the same timing, threshold decoder and signed residual bound as the AND–AND design. For a downstream read it supplies a score view at the current vector of port counts. Those counts are reconstructed from the actual preceding arrivals and FIREs. Each arrival must equal the dated upstream FIRE plus its wire delay, and an upstream silence contributes no delivery. This premise covers the residual of the **joint** downstream read as well as the singleton training reads. It leaves the native existence, physical dose footprints, read-only gates and calibration enclosure to later work.
