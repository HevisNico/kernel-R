# Dated refinement of the reciprocal witness

## Native transactions

`nominal_composed_cuts` retains exact execution factorizations on either
side of birth. In the same witness it certifies the protected B pair and
five prepared blocks. Each prepared transaction carries its real native
span, a single exact FIRE date, a return to READY, and zero gain and
recovery doses.

| Native block | Source transactions | Wire transactions |
| --- | ---: | ---: |
| Initial A train, from 40 through preparation | 11 | 0 |
| Forward learned train | 13 at A | 13 at B |
| Reverse learned train | 9 at B | 9 at A |

For both wire blocks, the sender starts at resting charge. Its unique
physical latency and the fixed wire delay give a translated copy of the
source calendar. The idle prefix preserves READY until the first wire
arrival. For the following contacts, the native return bound is strictly
below 6.991 after admission and the spacing is at least 7.5.
`PreparedTransactions.return_windows` retains the separation at each
certified return cut.

## Phase and reopening

After the unit FAST interval, reopening requires an integrated recovery
of log(5/2). If recovery is bounded by positive rates L and U, the
reopening date lies between F + 1 + log(5/2)/U and
F + 1 + log(5/2)/L, where F is the preceding FIRE. The SLOW classifier
requires a date strictly after FAST and strictly before the lower bound.
The READY classifier requires a date strictly after the upper bound
and no intervening same-cell FIRE. It leaves the uncertainty interval
unclassified. The lower-rate proof uses the native recovery evolution,
and the upper-rate proof uses the recovery bound over each flow.

`third_forward_predicted_slow` computes SLOW for the protected B
receipt using its preceding source, physical latency, recovery band
and wire gap. The phase calculation does not inspect the receipt mode.

## Replay and scope

`TransactionReplay` checks the abstract queue, nominal decision,
read margin, emitted contacts and normalized write footprint at each
admission. It composes at matching intermediate configurations.
`replay_network_memory` applies the dated network theorem to any such
composed replay, yielding write bounds, strict normalized headroom and
an identical zero-error execution.

The witness-level proof composes native cuts. It still lacks one guarded
trace of the entire staged history. The weak-learning and first
strong-response intervals outside the certified blocks need their own
per-transaction bridge, and their queue and memory boundaries must
connect to the prepared blocks. The native phase calendar is therefore
derived for the prepared blocks and the protected receipt only. At the
full native horizon 459.9, sixteen sources at dates 480 and later
remain in the queue. Preserving them yields horizon completion.
The verified horizon projection removes later work from the source
queue and every emitted batch while preserving decisions and writes.
`through_terminal_unique` applies Newman on the clipped calendar
when the clipped system has a rank and the footprint diamond.

## Earliest-date fairness

`earliest_write_fair` uses date clearance. For each date currently in
the queue, some later cut has no pending occurrence at or before that
date. Under the MARK diamond, the actual schedule can match the first
choice of any finite continuation before the clearing cut. Induction
on the residual continuation yields its write counts. With a reserve,
`earliest_limit_unique` gives the same frozen memory as FIFO.

A decreasing natural budget for each occupied date sublevel suffices.
Another sufficient hypothesis is local finiteness of service: for each
cutoff, only finitely many selected occurrences have dates at or below
it. It allows infinitely many FIREs overall. The starvation example has
a causal router, a reserve, and the MARK diamond. It reissues a FIRE
at date zero forever, so the later write remains pending.
