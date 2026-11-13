# Milestone 1 — chip-firing / abelian-network model

[ChipFiring.lean](ChipFiring.lean) formalizes the classical potential and least-action arguments. A cell can write when its work reaches a common threshold $d>0$. It consumes $d$ work, sends nonnegative integer work to its neighbors and increments its own stored count. **Enabling is monotone**: additional incoming work can enable a write and can never disable one.

- `stabilize Q d` fixes $Q,d$ before the network size $N$. Initial work is at most $Q$ per cell. Every row and column sum is strictly below $d$. Every legal prefix has length at most $QN$, every cell writes at most $Q$ times, and its work is at most $dQ$. The deterministic least-index computation returns a reachable terminal state, and every reachable terminal state equals it. An infinite legal write schedule would have a prefix longer than $QN$.
- `memory_bound B Q d` bounds each stored value, in dose units, by $B+Q$ for initial values at most $B$. This is a statement about discrete write states.
- `weighted_budget Q d W eta0` fixes all four constants before $N$. A weighted column margin gives $\eta_0 n \le WQN$ for every length-$n$ prefix, with the remaining potential retained in the stronger Lean inequality. When $\eta_0>0$, this is a uniform linear bound. The row bound in `stabilize` separately controls concentration of writes in one cell.

The potential calculation uses the existing `coupled_decrease` lemma. Least action compares any legal prefix with a reachable terminal write vector. A first write exceeding that vector would require a cell with no more work than its terminal amount to be enabled.

[Counterexample.lean](Counterexample.lean) checks two reciprocal edges in the same model. At $d=2$, both cells write once and end with one unit of work each. At $d=1$, the non-strict row and column inequalities pass, the work unit circulates, no terminal state is reachable and writes can exceed any ceiling. The mutation checks also reject duplicate spill against the one-edge balance.
