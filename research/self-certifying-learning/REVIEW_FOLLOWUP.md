# Review follow-up: availability, observation cost and composition checking

## Two corrections

The former `bad_deadlock` statement over Unit/False has been removed.
`Counterexamples.MissingAvailability` now has a functioning transition
`pending -> good`, a strictly decreasing rank on every enabled repair, and
an invalid `stuck` state with no valid reachable endpoint. This directly
refutes the conclusion of `repair_exists` when availability is omitted;
it is more than a truth-valued placeholder.

`OfferFactory.system_cost` now explicitly says in its docstring that it is a
pure count/accounting bound on generated write commands, not measured energy,
observation expense or actuator performance.

## Availability: a sufficient fixed-fallback theorem

`Availability.available` proves that a fresh one-decision offer always exists
for a fixed configuration when:

- The loss ceiling U is a hard bound that can legitimately be renewed.
- The write duration and maximum wait are positive, minimum dose exceeds
  `U * latency`, and usable capacity reaches `service + U*latency + U`.
- The current lower reserve is in the fallback's ready interval.
- Entry deficit is funded by carried debt plus remaining switching credit.

The funding condition matters: a positive repair margin and a ready reserve
do not alone guarantee admission in the current finite-credit coordinator.
The checked example rejects an unfunded ready state. After entry, the
fallback's own terminal debt is retained, so reissuing the same configuration
requires no further switching credit.

`completes_every_prefix` proves that the executable selector/renewal loop
completes every requested finite number of phases. `unbounded_time` proves
that calendar time advances without bound. `perpetual_service` then proves
service at every future tick, provided **one physical state trajectory
realizes every prefix**. This premise means the hard ceiling and commanded
write-delivery laws remain true indefinitely; it is not an assumption of
safety or of non-blocking.

This is a sufficient theorem for a fixed conservative fallback. It does not
make arbitrary adaptive offer generation permanently available, establish a
hard bound from finitely many observations, or model an inexhaustible battery
as a measured fact. Positive unbounded drift with finite repair power cannot
be turned into a permanent guarantee by extrapolating a local slew bound.

## Explicit observation prices and constrained optimization

`ObservationCost` counts one observation **attempt** per processed phase
request, including the attempt that blocks. Unprocessed future requests are
not charged. This accounting convention must be matched by the eventual
measurement implementation; observation latency is still absent.

The modeled total is

`observation_price * attempts + write_price * write_commands`.

`select_spec` proves that the executable selector returns a minimum-cost
candidate from a supplied finite catalogue of certified plans that both
complete and end at the **same calendar deadline**. `selected_service`
retains the existing service theorem under physical realization. Blocking or
ending early cannot win by avoiding observation work.

A checked comparison has two writes ending at time 6 in both plans. Bundling
them into one observation phase costs 12 with prices (10,1); using two phases
costs 22. The selector chooses the one-attempt plan. This demonstrates a real
tradeoff in the declared discrete objective, not calibrated hardware energy.

The minimum is exact only within the supplied catalogue and objective. It
is not a theorem of global optimality among all online adaptive policies,
and does not predict future unknown measurements without evidence.

## Exact composition verifier

`CompositionCheck.Witness` holds the supplied natural-tick weights, local
progress, cross-coordinate damage and margin. `check` uses finite exact
`decide` to verify positive weights, positive margin and every weighted
coupling inequality. `certify` turns acceptance into the existing
`CouplingCertificate`; `verified_decrease` applies it to actual coordinate
contracts.

The two-level witness is accepted. Zero margin, zero weights and the
three-level accumulating-spillover example are rejected. The separate
counterexample already excludes all positive integer weights for that chain.
No eigenvalue computation, weight search or M-matrix equivalence is needed.
Rational data require a justified exact common scaling; arbitrary real
bounds and approximate floating-point checks are outside this checker.

## R bridge

[R_BRIDGE.md](R_BRIDGE.md) records the concrete source correspondence and
remaining proof obligations. No empirical calibration has been promoted to
a deterministic assumption and the four R results are not relabeled as
corollaries of this package.
