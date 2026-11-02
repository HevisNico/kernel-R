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

The [headline](../proof/lean/KernelR/Headline.lean) constructs the declared
three-cell protocol through789.9 for every admissible fixed parameter/birth
choice and five bounded delay functions. It supplies an execution witness,
not a theorem about every admissible execution. Its exact source schedules and
contact gates are protocol data, rather than learned settings. The fixed
three-cell teaching/cadence law is
[`teachingCadenceRouter`](../proof/lean/KernelR/HybridTeachingCadenceRouter.lean).

The current result derives A54/B61/C34, terminal READY/q=0.1, no RAW, an empty
queue and own learned memories. Numerical simulations, the archived A22
network, operational drift/noise, frozen probes/settings copies and physical
every-N or universal refinement have their separate
[coverage boundaries](../proof/lean/HYBRID_EXECUTION.md).
