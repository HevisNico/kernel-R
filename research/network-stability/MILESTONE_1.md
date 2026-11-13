# Milestone 1 — discrete cyclic write model (proposal)

Use one exact-dose memory per cell, represented in dose units by $x_i=x_i^0+k_i$, where $k_i$ counts writes. Start with work $q_i^0\le Q$ and zero writes. A write at $i$ is enabled exactly when $q_i\ge d>0$. It consumes $d$ work at $i$, adds $A_{ji}$ at $j\ne i$, and increments $k_i$. Use a nonnegative integer matrix with zero diagonal, uniform row sums $\sum_j A_{ij}<d$ and column sums $\sum_j A_{ji}<d$. A trace consists of legal writes. A maximal trace stops only when no write is enabled, or continues indefinitely. This permits arbitrary choices among enabled cells. The positive fixture uses two reciprocal edges of weight 1, $d=2$ and $q^0=(2,2)$. Both cells write once and the final work vector is $(1,1)$.

## Lean statement sketch

The model names below are proposed interfaces. The counterexample file contains the checked phase-0 control.

```lean
theorem stabilize (M : Model N) (Q : Nat)
    (hd : 0 < M.retire)
    (hdiag : ∀ i, M.spill i i = 0)
    (hrow : ∀ i, (∑ j, M.spill i j) < M.retire)
    (hcol : ∀ i, (∑ j, M.spill j i) < M.retire)
    (hinit : ∀ i, M.initialWork i ≤ Q) :
    (∀ s, M.Reachable s →
      (∀ i, s.writes i ≤ Q ∧ s.work i ≤ M.retire * Q) ∧
      (∑ i, s.writes i) ≤ Q * N) ∧
    ∃ terminal, M.Reachable terminal ∧ M.Terminal terminal ∧
      terminal = M.computeTerminal (Q * N) ∧
      ∀ trace, M.Maximal trace → M.EndsAt trace terminal
```

`State` is the work and write-count pair. `computeTerminal` repeatedly writes at the least enabled index, for at most the given fuel. `EndsAt` asserts a finite last state. For $0\le x_i^0\le B$, all model memories are in $[0,B+Q]$, including linear interpolation during each dose. An interpretation with rails above $B+Q$ gives strict headroom.

## Proof plan

1. Maintain the balance $q_i+d k_i=q_i^0+\sum_j A_{ij}k_j$. By the column inequality, each write reduces total work by at least one. Reuse the weighted arithmetic in `CouplingCertificate.decrease` with unit weights, then induct over prefixes. Every maximal trace ends within $QN$ writes, and the canonical finite computation produces a terminal witness.
2. For a first attempted $(Q+1)$st write at $i$, all other counts are at most $Q$. Balance and the enabling guard give $d(Q+1)\le q_i^0+\sum_j A_{ij}k_j\le Q+(d-1)Q=dQ$, a contradiction. The same balance gives $q_i\le dQ$. These are uniform local bounds.
3. Compare any legal trace with a terminal count vector $k^*$ by first excess. Just before a first write exceeding $k_i^*$, the local count equals $k_i^*$ and all other counts are at most their corresponding terminal values. Nonnegative spillover and the balance imply $q_i\le q_i^*<d$, a contradiction. Apply the comparison in both directions to reachable terminal counts. Balance also fixes terminal work.

## Controls and validation

- **Checked now.** [Counterexample.lean](Counterexample.lean) sets $d=1$, uses reciprocal weights 1 and starts with one work unit. It proves no positive margin exists for any weights, no reachable state is terminal, traces exist at every length, and every candidate memory ceiling is exceeded. This is a cyclic counterexample in the proposed write model.
- **During milestone 1.** Use the same model for the positive two-cell fixture and the checked counterexample. Attempt the weakened theorem with non-strict row and column tests on that counterexample. Add a control with one source and one sink, $d=2$, $Q=2$, initial work 2 at both cells, and one edge of weight 1. This meets both inequalities. If a mutation duplicates each spill to two units, the claimed original work balance fails after the first source write. Require each mutation to fail on its intended semantic assertion, with a positive compilation control.
- **Toolchain.** Compile the control with `lean research/network-stability/Counterexample.lean` from the repository root under Lean 4.35.0. Its printed dependencies are within `propext`, `Classical.choice` and `Quot.sound`. For milestone 1, use the pinned Mathlib v4.35.0 if needed and audit every exported theorem with the same allowlist.

Out of scope for milestone 1 are native pulse realizability, ERROR/MARK overlap and clipping, arbitrary asynchronous physical deliveries, heterogeneous doses, perturbations, and a native R network need theorem. A subsequent milestone must supply at least one native cyclic instance of the transition contract and then generalize that bridge.
