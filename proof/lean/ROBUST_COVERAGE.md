# Robust birth and slow-chain coverage

This is an extension of the repository's partial formalization, using Lean
4.35.0 and the pinned Mathlib. It is separate from the earlier period-4 chain.

| Modules | Kernel-checked result | Explicit remaining input |
|---|---|---|
| `Robust.Noise` | Bounded noise integrals; ERROR/MARK dose bounds; invariant READY radius; charge perturbation envelope | Integral solution balance, integrability and amplitude bounds |
| `Robust.Birth` | Widened recovery and charge sections; three noisy ERROR doses; warm-up word counts | The physical execution realizes the supplied warm-up word, completes each mode, avoids clipping and reaches the section |
| `Robust.Latency`, `Robust.Response` | Derivatives and concavity of the exponential response; decreasing fixed-width increments; first-crossing perturbation bounds; same-response latency equality | Analytic envelopes, root existence and sound numerical enclosures; the reference uses each cell's actual learned gain |
| `Robust.Packets` | Exact date transformation through a cell and wire; first-shot advance removal; minimum spacing; periodic tail at zero jitter | The local latency bounds |
| `Robust.Induction` | Induction for every finite N over actual finite streams; exact counts; total traffic; zero-noise constant period; 32-cell period-8 arithmetic | Each cell satisfies `CellLaw` from a prepared section; wires realize the specified delays/errors |
| `Robust.Evidence`, `Robust.Certified` | 438 strict endpoint comparisons and 1,386 interval-validity proofs from 16 certificates; explicit margin transfer and the 0.00748 radius budget | Real exp/log/model quantities belong to the published rational intervals |

The sufficient period is `T ≥ 7.5 + 2 Σ (δᵢ + σᵢ)` over the first N−1
cells/links. The final cell's latency affects output jitter but no downstream
input. A cell removes three silent inputs. For K ≥ 3N+1, root traffic is K−3N;
K=3N+8 gives eight root outputs. Total traffic satisfies
`2 traffic + 3N(N+1) = 2NK`. The first firing's positive residual becomes an
advance; its possible delay is retained in the phase budget, not discarded.

For fixed wires and δ=0 the sufficient period is 7.5 at every depth. For the
checked ε=.1, ν=.002, α=0 point, δ=.00748 gives 7.96376 for 32 cells, so T=8
is sufficient **conditional on the local execution laws**. No interpolation
between stored parameter points, optimality of δ, or complete hybrid execution
proof is claimed. The endpoint proofs alone do not establish `CellLaw`.

`research/robust` preserves the previously tested offline package sources and reports byte for byte
(excluding temporary/cache files and raw compressed traces). Its historical “no Lean / no GitHub” notes
describe that snapshot's creation, not this integration. Birth preparation uses
16 external port-0 pulses per cell with routes closed; it is not preparation
from a single upstream input. Source manifests also cover numerical engines. Raw numerical traces remain local;
run the snapshot validators to regenerate them before using `--verify-record`.

Reproduce from `proof/lean`:

```sh
python scripts/check_sources.py
python scripts/generate_evidence.py --check
python scripts/robust_evidence.py --check
lake build
lake env lean Audit.lean
python scripts/check_negative.py
```

The robust emitter independently replays every certificate with integer
intervals before generating exact rational propositions. Lean checks the proof
terms; the audit checks all project theorems, including generated auxiliaries.
Negative tests pair passing controls with rejected endpoint, phase-budget,
first-shot-delay and traffic corruptions. Numerical campaign recordings remain
corroborating evidence, not proofs of the trajectories in Lean.
