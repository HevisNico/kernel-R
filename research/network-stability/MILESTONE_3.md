# Milestone 3 — one native reciprocal instance

[NativeReciprocal.lean](NativeReciprocal.lean) instantiates the existing staged birth and reciprocal teaching construction. The router has a forward edge and a later return edge. The nominal witness uses the existing nominal parameters and newborn, and fixes both delays to $7/20$. At the prescribed horizon $4599/10$, each cell's port 2 log-gain has increased by $9/5$ over its own birth value.

The companion theorem compares every complete run from the same post-birth state with the constructed run at that horizon, for fixed parameters and router. It proves identical per-cell FIRE dates, the two port 2 gains, and both recovery memories. The known schedule separates the two contact gates. The final snapshot still contains future external deliveries. The result concerns a finite reciprocal training epoch and leaves eventual write freedom and equality across changed read errors open. It is a native positive instance of reciprocal routing and a prescribed learning outcome. A refinement from the score abstraction in milestone 2 remains open.

## Reproduce the checks

With Lean 4.35.0 on PATH, run from the repository root:

```sh
(cd proof/lean && lake exe cache get &&
  lake build +KernelR.HybridBirthReverseTeaching +KernelR.HybridUniversalExecution +KernelR.FutureControls)
bash research/network-stability/check.sh
```

The check compiles all local Lean modules, rejects axiom dependencies beyond the three allowed by the repository and runs the paired semantic controls. GitHub Actions runs the same check using the pinned core toolchain.
