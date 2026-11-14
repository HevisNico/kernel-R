# Checked native endpoint projection

[NativeEndpoint.lean](NativeEndpoint.lean) starts from the existing nominal
milestone-3 reciprocal witness, with the same post-birth execution and
observation horizon $4599/10$. Its per-address decoding uses an ERROR unit
of $3/5$ and a recovery MARK unit of $1/10$. The actual native final values
agree with the discrete per-port counts. A's active gains are ports 0 and
2, and B's are ports 1 and 2. The inactive gain at each cell agrees with its
birth value.

The discrete execution in the endpoint theorem is a memory ledger. It
records twelve full-dose equivalents and never fires. Its state equality
claim is about the final six stored coordinates. The negative controls
make the limits observable: the ledger cannot reproduce the native
FIRE count, the native horizon still retains sixteen future deliveries,
and a proposed rail equal to A's attained gain fails the strict headroom assertion. This is a semantic headroom control for the witness, without changing the native cap in its dynamics.
The common-unit control also rejects equating the native ERROR and MARK
doses.

## Status against the bridge obligations

| Obligation | Checked on the witness | Still required |
| --- | --- | --- |
| 1. Cuts and abstraction | Endpoint relation and multiplicity-preserving native token balance | Segment the actual execution and relate eligible queues and every relevant cut |
| 2. Eligibility and exclusivity | Final future deliveries are distinguished from work in the chosen episode | Derive the admission rule from the actual arrivals, refractory windows and shared state |
| 3. Guard margins and routing | The nominal reciprocal router is causal and the native token ledger is conserved | Relate each native read and its score envelope to the discrete decision and successor list |
| 4. Doses, reserves and rails | Endpoint increments in coordinate-specific units and strict headroom along the post-birth trace | Assign actual exposed ERROR and MARK sections to discrete steps and prove a reserve for that trace |
| 5. First witness | The original complete witness supplies the projected endpoint and native FIRE count | Verify one observation-preserving replay of the actual episode |

The native FIRE protects gain, yet native recovery MARK actuation occurs
in the protected mode. A direct one-pulse encoding by the current guarded
step has only a FIRE-without-write branch and a silence-with-one-write
branch. A proof would need a verified decomposition into separate
transactions, or a guarded transition that can emit and schedule a
recovery update. The endpoint result supplies neither proof. This is
partial progress on the requested native refinement.
