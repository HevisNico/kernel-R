# Finite-chain protocol

This is the protocol quantified by
[`TrustedHeadline.every_finite_chain`](../proof/lean/KernelR/TrustedHeadline.lean).
The [cell laws](CELL.md) give the dynamics and threshold rules.

## Birth and fabrication

- Choose any integer `N ≥ 1` and source length `K ≥ 4N + 12`.
- For one choice of relative box, ±0.3% or ±10%, choose each cell's fifteen
  fabrication parameters independently within that box. The parameters stay
  fixed in time. The [nominal values](CELL.md#constants) are per port.
- All cells start at time zero with the main unit and all three sensors READY
  and no active raw current. Each cell independently has `q = 0.1 ± 10⁻⁵`,
  `b = 0.08 ± 10⁻⁵`, reserve `E ∈ [50, 100]`, and sensor charges
  `mᵢ = 0.025 ± 10⁻⁵`. Its three log-gains are within `10⁻⁵` of
  `log(0.3)`, `log(1.2)`, and `log(0.3)` on ports 0, 1, and 2.
  The headline supplies the all-READY requirement in addition to the reusable
  [`BirthState` definition](../proof/lean/KernelR/Hybrid.lean).

## Chain and sources

Number cells from the root (0) to the leaf (`N − 1`). Cell `i > 0` sends
only to cell `i − 1`. All input pulses have the
[canonical width-one shape](CELL.md#canonical-pulses).

- Each cell has exactly sixteen preparation inputs at dates `8k` for
  `k = 0, …, 15`. They enter port 1 at the leaf and port 2 elsewhere.
- The leaf also has `K` inputs to port 0 at dates `160 + 4k` for
  `k = 0, …, K − 1`. These and the preparation inputs make up the birth queue.
- Fix a delay function `δⱼ(t)`, centre `dⱼ`, and budget `σⱼ` for each link.
  Require `σⱼ ≥ 0`, `0.3 + σⱼ ≤ dⱼ ≤ 0.4 − σⱼ`,
  `|δⱼ(t) − dⱼ| ≤ σⱼ` for every real `t`, and `Σⱼ σⱼ ≤ 0.15`.
  Lean takes a nonnegative budget sequence on all natural indices and uses
  the first `N − 1` budgets for the path sum. Index `j = N − 1 − i`
  denotes the link out of cell `i`.
- The horizon is `T = 160 + 4(K − 1) + (11/10)(N − 1) + 8`. The
  [fixed router](../proof/lean/KernelR/ExplicitFiniteChainRouter.lean) acts
  only on `[160, T + 1)`. A FIRE at `F) from a non-root cell in that
  interval schedules one delivery on its parent's port 2 at `F + δⱼ(F)`.
  The root schedules no delivery.

## Complete executions and outcomes

The theorem constructs complete native first-contact and geometric upward-crossing
executions with the same weak history. It compares every finite execution in
either semantics from those same birth data, with the same parameters and
router, that is complete through `T`. This means it reaches `T`, settles
all enabled events under its semantics, and leaves no delivery due by `T`.

The endpoint, modulo ordering of the pending queue, and each cell's ordered
FIRE dates are fixed for these inputs. At the endpoint every main unit and
sensor is READY, the main charge is 0.1, and no raw current or delivery
remains. The active port (leaf port 0, otherwise port 2) gains 2.4 in
log-gain relative to birth, and each recovery rate gains 0.3. The preparation
prefix contains fourteen leaf firings and twelve at each other cell. The
[theorem guide](../docs/UNIVERSAL_FINITE_CHAIN.md) gives the exact traffic
counts and root cadence.
