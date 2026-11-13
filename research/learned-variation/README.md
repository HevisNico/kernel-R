# Learning a refutable sampled-variation envelope

This isolated preparation depends on R1 (#117). Its promotion to a new
milestone is gated on all workflows and latest-attempt jobs of R1's reviewed
head `c6684f796d092b2324489cb9920f78a9fcca7a5a` succeeding. R1 and the earlier
experiments remain unchanged. See [PROTOCOL.md](PROTOCOL.md).

The learner receives rate intervals and learns B in the upward-excursion
rule `rate(t+k) <= rate(t)+B` for a fixed horizon H. It starts at zero and
monotonically enlarges B from observations. A finite cap limits search; it is
not an assumed upper bound on the physical plant. There is no future-rate
input, retrospective tuning or supplied true variation constant.

For each new interval, it checks **every** earlier accepted interval whose
time gap lies in `(0,H]`. The required B is the maximum of
`new.upper - old.lower`, truncated at zero, and all earlier requirements.
If this exceeds the cap, the learner exhausts instead of clamping the result
and declaring success. It retains the offending trigger and witnesses in
the journal, outside the accepted fitted history.

Two event labels remain distinct:

- **Demonstrated refutation:** `new.lower > old.upper + oldB`. With honest
  sensor intervals, this proves a real violation between those sample times.
- **Ambiguous enlargement:** robust fitting needs a larger B, but the above
  separation is absent. This is not proof of physical change. Even constant
  truth 10 with radius-one reports 9 then 11 requires conservative B=4.

Each enlargement starts a new prospective window of W one-period transitions.
W is fixed in advance and must be at least H; the default protocol uses
H=W=41. The triggering sample is the anchor, not the first successful check.
The candidate is frozen until a contradiction/enlargement; ordinary renewal
cannot restart a completed window at the same B. This first observer kernel
keeps one-period sampling even after validation. Adaptive plant-policy
composition is not implemented here.

The result is an `EmpiricalProposal`, always labelled
`provisional-unguaranteed`. It is never converted into R1's external `Permit`.
The proved bound concerns accepted **sample pairs** under honest interval
measurements. It establishes neither the smallest physical B, unsampled
continuous-time behavior, nor future service. A constructive theorem shows
that an identical finite observation prefix admits a continuation violating
any proposed finite future B.

## Proof and accounting map

| Module | Result |
|---|---|
| `Envelope` | Exact robust demand over all eligible pairs; sound sampled excursion/refutation; monotone widening; cap exhaustion; finite-prefix limitation |
| `Learner` | Entire accepted prefix fits the current B; paid attempts plus remaining credit conserved; at most cap strict refinements |
| `Window` | Fixed prospective dates, no early completion, and total successful validation steps at most `(cap+1)W` |
| `Ledger` | Whole accepted-prefix sampled soundness; unchanged old annotations; affected witness dates; monotone B; accepted history length at most the sample budget |
| `Examples` | Nonvacuous fitting/validation and adverse fixtures, including noise-only enlargement and cap exhaustion |
| `Runtime` | Observation-only decoding and snapshots; malformed declared attempts fail closed and are charged |

The state machine has a predeclared total observation budget N. Its proved
price bound is `probePrice*N`. This includes explicitly failed attempts and
ordinary monitoring after validation. Successful validation transitions and
widening witnesses are accounted separately; the training trigger is never
counted twice or reused to shorten the next window. No credit is refunded.
This is a sensing-price model, not CPU time, energy or actuator cost.

Annotations retain the triggering interval, all affected earlier witness
intervals, old B, required B and the demonstrated/ambiguous classification.
Their affected calendar intervals are `[witness.time, trigger.time]`. Old
annotations are never rewritten. Annotations also retain the cap-overflow
witness: the final B does **not** claim to fit that rejected sample. The
history-length theorem does not bound total byte memory; witness lists and
arbitrary-precision integers also occupy memory.

## Executable finite-prefix interface

The IO bridge runs the actual Lean state machine; Python only supplies test
fixtures. From this directory:

```sh
lake build
lake env lean --run Bridge.lean
```

First send `init H cap W startTime sampleBudget`. Then send one line per
declared sensing attempt: `time rateReport errorRadius`. For example,
`init 41 200 41 0 100` followed by `0 10 1` supplies the first anchor. The
radius is a supplied honest interval premise, not a learned sensor bound.
The bridge emits one JSON snapshot per processed attempt, with the exact
proposal dates, counters and chronological annotation journal.

An explicit missing or malformed reading faults and consumes one credit.
Stale/skipped timestamps fault. `can_observe=false` means terminal status or
no credit; the bridge then stops accepting observations. EOF merely ends a
finite-prefix inspection; it does not simulate a missing physical period or
run a wall-clock timer. The bridge cannot autonomously detect an absent
sensor callback. Timing, latency and end-to-end refinement of the IO layer
remain outside these pure transition proofs.

## Verification and next boundary

```sh
python3 -B verify.py --report .lake/validation.json
```

The verifier audits all seven package modules, runs nine stream tests against
Lean, and rejects eleven paired semantic mutations. Window-transition
mutations compile the transition and window proofs together, so an old
compiled dependency cannot hide an invalid update. Parser/import failures do
not count as semantic rejection. Frozen prerequisites are checked unchanged.

This milestone supplies the learned envelope and its validation protocol.
It does not yet connect a provisional proposal to repair/cadence decisions,
establish a statistical confidence level, or demonstrate performance gains.
That composition and the randomized scenario suite need their own declared
protocol before execution. No plant trajectory, randomized experiment or
transistor simulation was run here.
