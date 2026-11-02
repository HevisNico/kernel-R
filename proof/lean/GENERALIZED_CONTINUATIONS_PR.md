# Draft: reuse learned terminal cells and a connected pair under irregular future inputs

Target base: `proof/physical-finite-chain`, starting from
`98b802fa77a065b72496e7d482a0ace4f2ecb079`.
Local branch: `proof/generalized-continuations`.

The finite-chain endpoint has gains and recovery outside the existing
repeatable one-cell `LearnedRest` domain. This change derives a separate
high-gain domain from each actual terminal cell, then constructs arbitrary
nonempty finite irregular input trains while retaining that cell's learned
memories, sensor residues and reserve. Inputs and final settling are separated
by at least `3.7`; the first new input occurs strictly after the endpoint.
Every input is consumed by an actual arrival and has exactly one derived
response. The returned high domain supports another train from the actual
final state. The bridge also accepts the endpoint of any complete original
chain execution, rather than only the constructor's witness.

For a connected two-cell pair, the receiver input calendar is derived from
actual leaf FIREs and a fixed positive wire delay. A causal weave issues and
delivers the wire tokens; only leaf sources are externally queued. The actual
birth prefix, future-source framing and connected continuation compose under
one fixed extended router with exact cumulative ledgers.

The existing lower-gain `7.5`-spaced repeatable regime additionally gains
universal wrappers: every complete execution of a settled prefix has the
same physical endpoint, retained memories and exact per-cell response dates.
At every finite horizon a complete witness exists and all complete executions
from its same finite source queue agree observationally.

These are isolated and finite two-cell post-training continuations with
canonical prequeued inputs. They preserve learned responsiveness; they do not
add further learning, indefinite network operation, online source
injection, operational drift/noise, or a maximal-run progress theorem. The
original finite-chain router closes at `T+1`; the connected result explicitly
constructs a future-extended router preserving the earlier FIRE ledger.

All three modules join the project-wide axiom audit. A new paired-control suite
checks exact response dates, preserved memories, sensor bounds, actual
deliveries, terminal queue emptiness and the universal runtime-endpoint bridge.
The workflow invokes that suite after existing proof controls. The global
README is unchanged.

Validation results are recorded in `GENERALIZED_CONTINUATIONS.md` when the
local compilation and controls complete.

This description is prepared for a draft pull request. No merge is authorized.
