# Physical execution semantics and analytic refinement

The complete protocol-to-abstraction theorem remains open. The modules below
prove physical flow and invariant results needed for that theorem. They do not
yet derive the four main-cell pulse cases or the full training calendars from
complete executions. Sensor triggering and the protected auxiliary cycle are
now extracted from actual executions by the modules described below.

## Physical definitions

`KernelR/Hybrid.lean` defines a pulses-only finite network with all q/m/z/b/E
coordinates, main and three auxiliary modes, raw-current origins and pending
delivery tokens. Parameters are independent per cell and port. `PhysicalBox`
states the ±0.3% or ±10% fabrication family. `BirthState` states the common
zero-time birth family, including allowed residual ERROR phases. Its pending
queue must separately be fixed to the supplied source protocol. The field here
uses fixed fabrication parameters and canonical amplitudes. The drift, charge
noise and amplitude variation studied by the conditional `Robust` modules have
not yet been instantiated in this operational semantics.

`field` contains the actual equations, complete work expression, energy gates,
and gain/recovery cap gates. A positive-duration `Flow` supplies continuous
coordinates satisfying integral ODEs on every prefix, with fixed discrete state.
Strict pre-guard conditions prevent advancing through a mode's first section.
Raw support and pending-delivery urgency prevent passing current ends or arrivals.

`Jump` permits only guarded section changes, delivery of an actual queued token,
or the end of an active raw current. Jumps preserve physical coordinates and time.
A fire appends routed tokens. An arrival removes one actual occurrence and requires
a free port. Canonical currents have half-open support, independently of main mode;
reopening admission retains any unfinished raw tail.

Sources must be in the initial pending queue. `CausalRouter` states causality of
the supplied wiring; generic ledger identities do not require that extra premise.
There is no staged-birth or settings-copy operation. Those protocols need a
separate semantic extension or a proved reduction.

`Execution` retains arbitrary legal zero-time interleavings without a total event
priority. `simultaneous_fire_mark_orders` constructs both compatible orders for
simultaneous main-fire and auxiliary-MARK guards. It does not establish global
confluence or simulator coverage of all simultaneous events.

`CompleteThrough` requires reaching the horizon and discharging enabled jumps
and due deliveries, including events exactly at the horizon. `Flow.prefix`
constructs a valid shorter prefix of an existing flow; it does not construct a
future continuation. `birth_resting_complete_exists` exhibits a complete
positive-duration silent execution from a nominal READY state and proves that
this state belongs to `BirthState`, with the prescribed nominal log-gains and
an empty source queue. This is one concrete birth-family witness, not existence
for every initial state or for the training protocols; those remain unproved.

## Checked implications

| Module | Consequence proved from the operational equations | Boundary |
|---|---|---|
| `Refinement` | Exact per-port ERROR and MARK integrals; telescoped gain/recovery balances; recovery equals the sum of all MARK contributions; queue conservation; actual emissions | Quantifies over finite admissible executions |
| `HybridFlow` | Scalar ODE uniqueness derived from integral equations; FAST and protected-auxiliary exponential solutions; SLOW uses the integral of actual varying recovery | Observed mode spans must still be selected from the execution |
| `HybridFlow` | Exponential solutions compose across legal zero-time interleavings; observed jumps supply phase endpoints; FAST duration is 1; MARK/SILENT/ERROR durations use actual rates; SLOW returns at accumulated recovery log(5/2) | Does not establish the supplied protocol's ordering of these phases |
| `HybridFlow` | A FAST flow cannot pass its first physical exit section; zero-input READY relaxation and gate-implied constant gains/recovery | No general extension/progress theorem |
| `HybridReady` | Main and auxiliary READY responses to one active canonical input, including residual charge and attenuation from the real pulse origin; first threshold contacts agree with the analytic response | Main input gain is frozen by local absence of ERROR; variable-gain overlap and multi-input cases remain separate |
| `HybridInvariants` | Integral cap barriers; gains and recovery cannot overshoot their caps, and are nondecreasing in the fabrication family; birth-state memory bounds | Strict cap inactivity during a required complete dose is not automatic |
| `HybridBounds` | Coarse bounds on actual real log/exp expressions and independent fabrication parameters | Does not certify every stored certificate enclosure |
| `HybridRegion` | Main charge upper bound and mode-dependent auxiliary upper bounds, including m<=0.1 in ERROR, preserved from birth across flows and jumps | Port-separation/protocol-calendar results are not asserted |
| `HybridWork` | Actual work is nonnegative and <=500, derived before assuming positive reserve; reserve stays in [50,100] for every finite admissible execution from the declared family, and throughout each reachable flow | Does not supply existence of those protocol executions |
| `HybridWork` | Energy exposure in ERROR/MARK lemmas follows from reachability and the reserve invariant | Required main/auxiliary chronology and strict cap inactivity remain premises |
| `HybridEvents` | Emission dates are chronological and inside the actual execution interval; causal wiring preserves future delivery dates; FAST potential telescopes across all legal interleavings; per-cell firing count is at most T+1 from birth | A due token is allowed at the current date; port availability and progress remain separate |
| `HybridAuxEvents` | Protected SILENT decay supplies a clock; a discrete rank counts all four auxiliary transitions; at most 8T+10 auxiliary jumps per cell and port from birth, including residual ERROR | This is a coarse event budget, not a prescribed pulse-case sequence or full-dose conclusion |
| `HybridEventBudget` | Every jump is partitioned into main, auxiliary, arrival or raw-end events; queue and raw-current balances give a uniform natural budget for all finite prefixes ending by T | Requires an explicit routing fanout bound; no continuation or complete protocol execution is constructed |
| `HybridEnvelope` | READY comparison with variable physical gains, every active port and attenuation from each actual raw origin | Comparison gain bounds remain explicit; monotonicity and caps supply a general physical instance |
| `HybridClipping` | ERROR gain increase is at most eight times actual auxiliary charge loss; per-port MARK dose is at most half the loss, including closed gates; strict cap exposure follows from remaining-charge headroom | Complete dose still requires actual main-mode chronology; a real headroom lemma does not establish a dose count |
| `HybridPrefix` and `HybridPulseSpans` | Cut an actual execution using its existing flow path; preserve observed flow modes; retain raw origins; compose exact READY sensor responses across legal events | Prefixes of given executions, not future continuation constructions |
| `HybridPhases` | Select the first actual mode-changing jump and reconstruct the original execution; extract complete FAST and protected auxiliary phases | Requires starting mode/charge and a sufficiently long actual execution; existence is not asserted |
| `HybridAuxCycle` | From actual MARK entry at m=1, extract MARK, SILENT, ERROR and the READY successor, with real protected duration in [123/110,41/30] | Main-cell interactions and subsequent inputs remain separate |
| `HybridResponseBounds` | Real response bounds, including response<=3/4 in the raw window and a positive lower bound at 9/10 | Selected coarse analytic bounds, not soundness of every stored enclosure |
| `HybridSensor` | A received pulse at a READY sensor in its rest band forces MARK in (t+1/100,t+1/40); ERROR starts after t+99/100; READY returns after t+1 and before t+419/300 | Given an execution reaching that horizon; no phase word is supplied; main firing and dose exposure remain open |
| `HybridInputs` | Queue and delivery provenance from actual sources/emissions; actual delivery dates; input isolation from queue/routing dates; raw validity, persistence and expiry | Concrete source queue and wiring must still be instantiated |

The real coarse bounds used for work are a in (1,1.4), C<=5, Lm<=14, Ls<=3,
Le<=11 and M<=60. The sensor response at 1/50 is proved >=1/55 using real
exponential inequalities. These are proofs about the actual real expressions;
no stored rational endpoints or Python arithmetic implementation are assumed.
They suffice for the work invariant but do not close the other certificate bounds.

The reserve proof uses an integral barrier rather than differentiability at all
cap contacts. A density that points inward on the wrong side of a boundary cannot
move a continuous integral solution outside that boundary. This covers the work
discontinuities caused by actuator clipping and energy gates.

## Doses and clipping

Actual actuation is always integrated without rounding. For an openly exposed
ERROR span, the dose is `8*(m_start-m_end)`; for MARK it is
`(m_start-m_end)/2` per port. Actual legal entry/exit jumps yield the endpoints
for full doses of 3/5 and 1/10. Other-port contributions remain in recovery.
A partial dose such as `8*(0.07-0.025)=0.36` stays partial.

The global cap theorem permits clipping. A complete ERROR phase at an already
closed gain cap does not receive a full dose. `ErrorOpen`, `MarkOpen` and the
span exposure predicates still require the relevant mode chronology and strict
cap inactivity. For a flow reached from the declared birth family, the energy
part is now derived by `reachable_power_gate_open`, rather than postulated.

The clipped ERROR budget bounds `z+8*m` across an ERROR span regardless of
gate closures. Thus a strict inequality on the initial `z+8*(m-1/40)` proves
gain-cap inactivity throughout that span. Together with a reachable reserve
and actual READY main-mode spans, `error_exposed_of_headroom` derives the
complete exposure predicate across legal intervening events. The real low-gain
headroom estimate covers an increase of 12/5 above the low nominal log-gain;
it does not establish that the protocol has produced that increase.

Neither full-dose lemmas nor mode-span predicates derive the four pulse cases of
the certified protocol. That remaining distinction is explicit in signatures.

## Actual sensor cycle

`Execution.sensor_cycle` starts immediately after a canonical input has been
received: its active raw origin is the current date, the sensor is READY and
its charge lies in the declared rest band. The initial physical upper region
and independent fabrication box are required. The theorem takes an actual
execution reaching at least t+419/300.

It extracts the first READY-to-MARK jump, then the three protected auxiliary
phases and their actual outgoing jumps. Every decomposition reconstructs the
given execution. Trigger and protected durations follow from integral equations,
physical guards and proved real exponential inequalities; no recorded phase
word, desired count or stored root enclosure is assumed. Other cells, ports
and main-mode switches may interleave freely.

ERROR starts after t+99/100 and may overlap the last part of the raw pulse,
which is retained by the variable-gain comparison lemmas. READY returns after
the raw end t+1 and before t+419/300. Times are in the model's time units.
Determining the main cell's firing and protection of doses during this cycle
remains part of the pulse-case proof. The theorem does not construct its input
execution or exclude later inputs. `HybridInputs` supplies provenance and
isolation lemmas to discharge source and routing obligations separately.

## Physical event budget

For a network of n cells born at zero, let Q be the length of its actual initial
pending queue and suppose each firing routes at most F delivery tokens
(`FanoutBound`). Every finite admissible prefix ending by T satisfies

```
physical jumps <= n*(27*T + 33) + 2*(Q + F*n*(T + 1)).
```

All nine `Jump` constructors are counted, including events exactly at T and
arbitrary compatible zero-time interleavings. No supplied firing count or event
word is used. The bound is deliberately coarse:

- A FAST logarithmic potential gains one at a real firing and decreases by the
  elapsed FAST time. Its terminal value is at most one, so an incomplete final
  phase is retained. Each cell fires at most T+1 times, and has at most 3T+3 main
  mode changes. A newly entered FAST phase cannot be left before one time unit,
  even across intervening other-cell or auxiliary events.
- On each port, a SILENT logarithmic potential decreases at the actual rate
  Ls/log(8), proved at most two in both fabrication families. A mode rank relates
  the number of all auxiliary changes to SILENT entries, giving 8T+10 changes.
  These clocks are proof potentials, not added physical coordinates.
- Every arrival consumes an initial or routed token. Every raw end consumes a
  current created by an arrival; raw currents are absent at birth. The initial
  queue and actual routed fanout therefore remain in the global bound.

`finite_prefix_event_budget` converts this real bound to one natural budget
shared by every finite admissible prefix with the same birth state and horizon.
Thus physical jump counts cannot grow without bound at bounded times. Splitting
a continuous flow into arbitrarily many pieces is not counted as a physical
event. This settles the uniform finite-prefix event-count obligation under
bounded fanout; it does not establish existence of a future flow, availability
of an occupied destination port, or terminal saturation. Concrete protocol
wiring and initial queue adequacy still need to be proved.

## Connection to finite-chain composition

`Execution.signal` extracts a `Chain.Signal` from actual fire jumps, retaining
the exact number of emissions. `hasPacket_of_emission_witness` exposes both
outstanding packet obligations: exact event count and every actual emission date.
It connects to PR #6's interface but does not supply its leaf or `RelayLaw` witness.

## Remaining obligations for the complete theorem

1. Instantiate and review the semantics with the supplied protocols, including
   staged births where relevant, and prove routing adequacy and port separation.
2. Prove the main/auxiliary interactions in each actual pulse case, including
   combined MARK/ERROR, strict cap inactivity, variable-gain raw-tail overlap
   and absence of extra firings. Sensor triggering, the protected auxiliary
   cycle and phase selection are now derived from actual executions; their
   synchronization with main firing and reopening remains open.
3. Establish sound real enclosure membership for the remaining root, calendar,
   recovery and residual-tail expressions in the certificates. Exact comparisons
   of stored endpoints alone remain insufficient.
4. Prove protocol-specific execution existence, extension/progress and terminal
   saturation for all compatible event orders. Instantiate the checked uniform
   finite-prefix event budget with the concrete source queue and routing fanout.
5. Lift the resulting physical case theorem through preparation, the cadence
   cascade, retained probes and the packet induction for every finite chain.

Certificates, manifests, recordings and the pinned prototype ZIP retain their
existing identities and scope. No theorem asserts the complete physical result,
assumes a recorded pulse-case word, or treats finite counter replay as a trajectory
proof. The partial-dose calculation is not a reachable training counterexample.

## Validation

Use the pinned Lean/Mathlib versions and the standard project workflow:

```sh
lake build
lake build Audit
python scripts/check_audit_negative.py
python scripts/check_sources.py
python scripts/generate_evidence.py --check
python scripts/check_negative.py
python scripts/check_hybrid_negative.py
python scripts/check_hybrid_analytic_negative.py
python scripts/check_hybrid_event_negative.py
python scripts/check_hybrid_phase_negative.py
```

Every negative check first compiles its positive control. Existing physical
checks reject under-threshold firing, nonconsuming delivery, closed-gate positive
actuation, a rounded partial dose and an omitted raw current. Analytic controls
reject altered FAST/MARK durations, an invalid reserve floor and removal of the
attenuation of a raw tail. The axiom audit imports all new modules through KernelR.
Event controls reject removal of the unfinished-FAST allowance, altered FAST
departure and auxiliary bounds, strict future dating of a token due now, and
omission of routed fanout from the published global budget.

Phase controls reject an absent received input, altered sensor/error/return
dates, a shortened protected cycle, freezing a variable gain, an incorrect
clipped-dose coefficient, a retained expired raw current, and omission of
routed tokens from delivery provenance.
