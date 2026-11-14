# Native hybrid bridge — proposed, no refinement proof yet

Start with [NativeReciprocal.lean](NativeReciprocal.lean) and the existing
`ConstructedReverseTeaching` execution. Freeze the same post-birth snapshot,
parameters, external calendar and router as in milestone 3. The first proof
target is the finite observation at $4599/10$. The final snapshot still has
future deliveries, so queue exhaustion at that time would concern only the
chosen episode. The forward and reverse contact gates are distinct. Preserve
their timing and prove which issued contacts are due in each gate before
abstracting them to successors.

## Obligations in proof order

1. **Choose observable cuts and an abstraction relation.** At a settled
   cut record the gains relative to their own initial values, the recovery
   memory, pending *eligible* pulse occurrences and the FIRE events already
   represented. Preserve token multiplicity, recipient and port. Keep
   delayed external deliveries in a separate dated calendar. Establish a
   domain of complete executions from the same post-birth state and prove
   that every relevant native segment is represented, with inactive time
   and non-learning jumps allowed to stutter.
2. **Derive exclusivity from timing and eligibility.** A refractory bound
   prevents overlapping eligible transactions only with admission and
   separation bounds on pulse arrivals, completion and reset. Prove at
   most one eligible transaction per coordinate at each cut. A native
   pending list may contain several future arrivals at the same port.
   Same-cell ports share charge and protection, so prove that their reads
   and recovery effects are independent at these cuts before invoking the
   per-port diamond. If that fails, use cell-level exclusivity or prove a
   commutation lemma for the actual joint read/write footprint.
3. **Derive the score margins and routing correspondence.** For each
   eligible transaction bound the actual peak relative to the realized
   threshold, including residual charge, coincident arrivals, the
   exponential gain law, recovery, and bounded measurement and timing
   perturbations. Prove strict silence and valid upward crossing for the
   FIRE branch, including any required transversality. Use the local
   tolerance theorems where their prepared-probe hypotheses hold.
   A magnitude bound on the threshold error alone is insufficient. Exact
   integer score equality is unnecessary if the decisions agree throughout
   the admitted envelope. Match each native FIRE and its admissible routed
   occurrences to the abstract successor list.
4. **Close the dose, reserve and rail obligations.** Use
   `HybridDoseCounting.lean` and the exposed ERROR/MARK section covers. Prove
   that a counted native write completes without clipping, and that
   protected sections do not change the relevant memory. Account for
   recovery MARKs separately. The current per-port lift has one common
   discrete dose and independent addressed updates. Native ERROR and MARK
   doses differ, and one pulse may affect more than one coordinate.
   Select exact per-coordinate dose units with suitable gains, or extend
   the guarded step to a multi-coordinate footprint and reprove its
   reserve and commutation laws. Use an intermediate-state invariant to
   establish interior headroom throughout flow, including partial writes.
5. **Check the first witness and then widen the domain.** Native ports
   are indexed by `Fin 3`. The reciprocal instance uses ports 0 and 2 on A,
   ports 1 and 2 on B, and both recovery memories. Start with a cell-specific
   renaming of just those active ports, carrying the inactive port as a
   frozen projection if its section ledger proves that. Compare birth
   offsets, port 2 increments $9/5$, recovery increments $1/10$ and
   per-cell FIRE dates against the existing milestone-3 result. Add a
   semantic negative control for overlap, a clipped section, or an
   uncertified guard. For longer runs, prove non-Zeno progress and a
   scheduler fairness condition separately. The finite reciprocal witness
   supplies neither a native perpetual-traffic refinement nor fairness.

The per-port abstract lift itself admits separate events for two gain
memories and one recovery memory. It gives $Q$ writes per coordinate,
$3Q$ per cell and $3QN$ overall, with the same rail, margin and confluence
arguments under coordinate-local guards and updates.
