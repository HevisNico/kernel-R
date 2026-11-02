# R model ↔ Lean correspondence

This map compares the [R cell equations](../kernel/README.md) with the
operational semantics in [Hybrid.lean](../proof/lean/KernelR/Hybrid.lean).
Lean proves properties of these definitions under stated hypotheses; matching
a physical device or a numerical engine requires separate justification.

Write a=ln4, κ=1/2, r=1/10, rₘ=1/40, and gₚ=exp(zₚ).

| Model component | Equation or operational rule | Exact Lean definition |
|---|---|---|
| State and fixed parameters | q, mₚ, zₚ, b, E; main READY/FAST/SLOW; auxiliary READY/MARK/SILENT/ERROR; per-port Cₚ,Lₘₚ,Lₛₚ,Lₑₚ,Mₚ | `Coord`, `MainMode`, `AuxMode`, `Snapshot`, `Parameters`; `PhysicalBox` independently bounds the five parameters at every cell/port, with ε=3/1000 or1/10 |
| Canonical pulse and raw origin | p_F(t)=a exp(−a(t−F)) on[F,F+1), zero outside; each active port retains its actual F | `a`, `pulse`, `current`, `Snapshot.raw`; `Jump.arrive` installs an origin, `Jump.rawEnd` removes it exactly at F+1 |
| READY charge and gain | q′=κ(r−q)+Σₚexp(zₚ)pₚ(t) | `drive`; `field` at `.q` with main `.ready`; gains multiply incoming current only in this mode |
| FAST and SLOW | FAST:q′=−a q until q=1/4; SLOW:q′=−b(t)q until q=r | `field` at `.q`; `Jump.fire`, `Jump.fastEnd`, `Jump.reopen`; no prescribed SLOW return date |
| Auxiliary charge | READY:mₚ′=κ(rₘ−mₚ)+Mₚpₚ; otherwise mₚ′=−L_mode,p mₚ | `field` at `.m p`, `auxDrain`; auxiliaries see raw current even while main admission is closed |
| Auxiliary thresholds | READY→MARK at1; →SILENT at4/5; →ERROR at1/10; →READY at1/40 | `Jump.mark`, `.silent`, `.error`, `.auxReady` |
| Gain learning and protection | zₚ′=8Lₑₚmₚ when auxiliary ERROR, main READY, E>0 and zₚ<ln Cₚ; otherwise0 | `errorAct`; `field` at `.z p` |
| Recovery learning | b′=½ΣₚLₘₚmₚ when auxiliary MARK, main not READY, E>0 and b<11/10; otherwise each contribution0 | `markAct`; `field` at `.b` |
| Energy and work | E′=10(100−E)−W; W sums main work, auxiliary admission/drains and actual learning actuations | `work`; `field` at `.energy`; [HybridWork](../proof/lean/KernelR/HybridWork.lean), `Execution.reserve_birth_invariant`, proves reserve bounds under physical birth/parameter hypotheses |
| Caps and actual doses | Gain/recovery actuation vanishes at its cap; full ERROR adds0.6 and protected MARK adds0.1 only when their gates remain open | `errorAct`, `markAct`; [HybridInvariants](../proof/lean/KernelR/HybridInvariants.lean) cap barriers; [Refinement](../proof/lean/KernelR/Refinement.lean) actual integral ledgers and gain/recovery balances |
| Continuous evolution and first sections | Integral ODE on every flow prefix; strict interior guards prevent passing the first threshold in an old mode | `Flow.integral_eq`, `.guards`, `BeforeGuards`; `.raw_support` and `.pending_urgent` prevent flowing past raw expiry or a due token |
| Events and causal wiring | Jumps preserve time and physical coordinates. FIRE appends routed tokens; arrival removes one actual due occurrence on a free port | `setMain`, `setAux`, `setRaw`, `Jump`, `Delivery`, `Router`, `CausalRouter`; `Execution` composes actual flows and jumps without a fixed simultaneous-event priority |
| Births and terminal completion | A starts in the declared birth family; later births add independent READY coordinates and sources. Completion discharges enabled jumps and every token due at the horizon | `BirthState` plus the headline's READY-auxiliary/source premises; [HybridStagedBirth](../proof/lean/KernelR/HybridStagedBirth.lean): `Newborn`, `BirthStep`, `StagedExecution`; `CompleteThrough` |

The [universal finite-chain headline](../proof/lean/KernelR/UniversalChainHeadline.lean)
constructs the common-birth directed-chain protocol for every positive finite
N, K≥4N+12, independent fixed parameter/birth choices and arbitrary prescribed
per-emission wire errors with cumulative budget≤0.15. It constructs fixed
native delay functions bounded at every real time. All cells are born at 0,
prepare with 16 period-eight inputs, and the leaf receives K port0 sources
from 160. The full source program is already present at birth.

At T=160+4(K−1)+1.1(N−1)+8, **every complete finite execution** from those
same birth data with that fixed router is READY/q=0.1, with no RAW or pending
token, active log-gain own birth+2.4, recovery own birth+0.3, and the same
ordered actual FIRE dates per cell. The factory constructs a complete witness,
so the universal class is nonempty. The fixed router covers preparation and
cadence; [`finiteChainPreparedData`](../proof/lean/KernelR/HybridFiniteChainPreparedData.lean)
defines its declared sources and contacts.

| Universal comparison step | Lean proof |
|---|---|
| Same physical integral flow, including cap contacts | [HybridFlowUniqueness](../proof/lean/KernelR/HybridFlowUniqueness.lean): `Flow.path_unique`, using scalar integral barriers |
| All nine simultaneous jump types commute observationally | [HybridJumpLocalDiamond](../proof/lean/KernelR/HybridJumpLocalDiamond.lean): `Jump.local_diamond`, modulo pending-list permutation |
| Every complete finite trace has the same physical endpoint and FIRE dates per cell | [HybridUniversalExecution](../proof/lean/KernelR/HybridUniversalExecution.lean): `Execution.observational_unique`, `Execution.emissionTimes_unique` |
| Prescribed errors on every actual fast sender list | [HybridUniversalBirthCadenceChain](../proof/lean/KernelR/HybridUniversalBirthCadenceChain.lean): `all_complete_errors`, after dropping 14 leaf /12 relay preparation FIREs |

`CompleteThrough e T` requires the terminal date T, no enabled terminal jump,
and every pending token strictly future. The comparison quantifies over
finite traces in that class. It does not claim that a stopped prefix has
already completed, or establish infinite/maximal-run progress or non-Zeno
extension. It does not equate flow subdivisions or the global ordering of
simultaneous independent events.

The earlier [three-cell headline](../proof/lean/KernelR/Headline.lean) retains
its distinct staged 0/160/480 births, horizon 789.9 and A54/B61/C34. Operational
drift/noise, frozen probes/settings copies, numerical observations and A22
retain their separate [coverage boundaries](../proof/lean/N_CELL_COVERAGE.md).
