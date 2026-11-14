# Guarded learning with recovery writes

A probe reads its selected gain and the cell's shared recovery count. Its
score is the bias plus the gain count times `d` plus the recovery count
times a signed coefficient. A FIRE emits the usual successors and can
commit a MARK dose. A silent probe can write its gain, its recovery
coordinate, both, or neither, as specified by its footprint. Allowing a
silent MARK matters for the native protected pulse.

## Network theorem

`MarkFeedback.network_memory` uses a branchwise certificate. For each
probe, outcome and coordinate, the reserve pays for the footprint and
leaves enough credit for the successors. Every prefix therefore has at
most `Q` writes per coordinate, at most `3 * Q` per cell, and at most
`3 * Q * N` overall. The rail bound uses a common dose upper bound in
normalized units. The native comparison uses coordinate units of
`3/5` for ERROR and `1/10` for MARK. The bounded, nondecreasing counts
freeze even for arbitrary FIFO read errors and perpetual traffic.

Nominal FIFO margins give equality of noisy and clean FIFO prefixes.
For an arbitrary order, a certified trace checks its margin at the
actual cut. Distinct cells commute modulo queue permutation. For probes
on the same cell, require either cell exclusivity or that the nominal
guard tolerate the full score displacement of each possible competing
footprint. A signed recovery coefficient can move a guard in either
direction. Under this condition FIFO matches every finite continuation
in write counts. Certified fair schedules have the same frozen memory
as FIFO, with no queue rank required. With a strict queue rank, Newman
gives the same terminal memory for all certified orders and FIFO drains
by `W * N`. The rank decreases along every probe-type edge.
The constants `Q`, `d`, `W` and `eta` are explicit before `N`.

`MarkCounterexample.lean` checks a one-cell self-contact whose two ports
are initially exclusive. A FIRE with MARK moves the second port over
threshold. Two zero-error orders drain with different gain memories
even with a strict rank and reserves. FIFO then misses an attainable
write. The CI mutation turns on this cross-port recovery influence.

## Native witness

`NativeMarkTrace.lean` projects the actual post-birth reciprocal history
to a single ordered list of FIREs and arrivals. The two projections equal
the native emission and delivery words. Actual arrivals at the same
port have disjoint unit raw windows. This statement concerns raw
occupancy. Eligibility for a full guarded transaction also depends on
the time needed to settle the main and auxiliary states.

The forward receiving prefix through time 184 compares the first three
B receptions with a fixed three-probe guarded run. It checks B's FIRE
word, the gain dose and recovery dose, and the measured arrival gaps.
The sole B FIRE lies between the second and third receptions. Each of
the three B arrivals is matched to an actual A FIRE at the nominal
wire delay.
The native third contact is protected and adds recovery while emitting
no B FIRE. A FIRE jump itself preserves all physical values, and any
positive MARK dose requires elapsed native time. A physical refinement
must therefore associate abstract commits with flow intervals and
carry the FIRE timestamp within the interval.

The full two-cell guarded replay remains open. It requires pairing
the remaining deliveries, FIREs and flow doses at common cuts, retaining
the routed occurrence identities and deriving transaction eligibility
through completion. The native event projection and the B-prefix
comparison are the checked scope here.
