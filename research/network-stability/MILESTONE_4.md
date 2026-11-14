# Milestone 4 — robust need on a routed calendar

[RoutedCalendar.lean](RoutedCalendar.lean) models any finite list of probes on $N$ cells. A probe selects a cell and reads its offset plus $d$ times its stored write count plus the sum of its listed incoming contributions. Each contribution is active exactly when its source slot fired. A causal calendar points only to earlier slots. FIRE occurs at a nonnegative score after adding the read error. It protects the memory. A silent probe writes one dose of size $d$ and emits no FIRE. Initial memory is included in the slot offset for purposes of the score, and stored memory is tracked as initial memory plus completed doses. There is no clipping in the transition.

**Network need.** The nominal run uses zero read error. For each slot, take its clean score $s$ on that run and an error interval $[\ell,h]$. A nominal silence requires $s+h<0$, and a nominal FIRE requires $s+\ell\ge0$. The induction in `run_eq_of_margins` compares the next decision after equal earlier histories. Both write counts and routed contributions therefore agree at the next probe. The conclusion is equality of the entire ordered FIRE word and write vector. The same result holds at every prefix. `recovers_three_probe_model` identifies the milestone-2 episode as a special case, for every triple of read errors.

**Uniform headroom and write bounds.** In the same guarded transition, `certified_episode` fixes $Q,d,B,U$ before $N$. The calendar offers at most $Q$ probes per cell. Initial stored memories are at most $B$, and $B+dQ<U$. Every prefix has at most $Q$ writes per cell, at most $QN$ writes in total and stored memory at most $B+dQ$, strictly below the rail $U$. The finite calendar is exhausted after one step per slot, with no writes outside the scheduled opportunities. In score units, the free part of the score uses an offset calibrated for the initial memory. This is a local admission budget, so the theorem applies to any topology that meets it, including reciprocal and self contacts. It leaves the generation of a finite calendar by autonomous feedback open.

**Structural certificate.** Fix $E,R$ before $N$, where $E$ is the absolute read-error bound and $R$ bounds the sum of contact weights per slot. Write $f$ for the free port score before incoming contributions. `full_load_window` proves that $f+R+E<0$ guarantees silence, and $f\ge E$ guarantees FIRE for every incoming contribution between $0$ and $R$. The strict silence inequality accounts for the threshold convention. This full-range test forces a decision independently of routing. To certify useful routed signals, `structural_episode` accepts a planned decision word and checks each receiving window $[L,H]\subseteq[0,R]$ against the FIREs already in that word. At each step the planned silence requires $f+H+E<0$ and the planned FIRE requires $f+L-E\ge0$. The proof establishes the entire planned FIRE word inductively, so the resulting trajectory is a conclusion.

## Certified task — conjunction with reciprocal acknowledgement

[RoutedCalendarExamples.lean](RoutedCalendarExamples.lean) checks all four Boolean inputs with one set of constants, $Q=2$, $d=2$, $B=1$, $U=6$, $E=1$ and $R=6$. A sends its input bit to B. B combines it with its own bit and sends the conjunction back to A. The contacts are causal at the slot level and form a cycle on the two cells. The returned result changes A's third-slot write decision.

| A | B | FIRE word (A, B, A) | Terminal writes (A, B) |
| --- | --- | --- | --- |
| 0 | 0 | 0, 0, 0 | 2, 1 |
| 0 | 1 | 0, 0, 0 | 2, 1 |
| 1 | 0 | 1, 0, 0 | 1, 1 |
| 1 | 1 | 1, 1, 1 | 0, 0 |

For inputs $(1,1)$ both contacts carry FIRE. Removing the return contact leaves B's result intact and makes A write on its acknowledgement probe. Thus the return contact has an observable effect on stored memory. The scope is the discrete guarded model. Realizing the scheduled contributions, margin measurements and write exposures in native hybrid R remains a separate proof obligation.

The existing network-stability check compiles both modules and audits their dependencies. Paired controls reject an upper silence bound that allows equality at threshold and the expected acknowledgement after removing the return edge.
