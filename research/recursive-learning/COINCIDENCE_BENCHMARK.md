# Learned routing into a coincidence receiver

## Protocol registration

This protocol defines a prospective simulated benchmark. A previous one-cell
calculation used nominal thresholds and an illustrative latency window. That
calculation is exploratory. This benchmark uses a different decision rule
whose timing comes from a published task. Record this commit before running
the comparative sweep. Record any later protocol changes in a new revision
and keep results from the original protocol.

## Task and timing

Two R cells represent the left and right channels. Each cell has two
selectable input ports, A and B, with identical initial gain 1.2. All other
birth coordinates follow the pinned single-cell
[training start](https://github.com/HevisNico/kernel-R/blob/11f476c3eb299263b980d5b69fb4592e8c0c093b/research/recursive-learning/native/TrainingRead.lean#L11),
with the unused port at gain 0.3. The implementation source is commit
`11f476c3eb299263b980d5b69fb4592e8c0c093b`. Train both cells with one canonical pulse at time zero on
the selected port. Run separate experiments with A and B selected. The
network wiring and read schedule are the same in both experiments.

Each test starts from a fresh birth and repeats its assigned training.
Deliver one test pulse per cell on independently specified ports. Keep the
state reached by training. The left test arrives at 17 plus its timestamp
error. The right test arrives at 17 plus the input offset and its timestamp
error. There are no other external pulses. Collect test emissions through
time 20 and observe their deliveries through time 20.35.

The synthetic input offsets are −30, 0 and +30 µs. Use independent
timestamp errors in [−5, 5] µs on each side. These values and the 100 µs
interspike interval come from Lagorce et al., section 4.3. Define one R time
unit as 100 µs for this benchmark. This choice fixes the difficulty, because
the model's response times are expressed in R units. Include time scale in
the sensitivity study, with 50, 100 and 200 µs per unit, holding the input
offsets, jitter and receiver aperture fixed in physical time. This is a
simulation convention. The test uses isolated event pairs and does not reproduce the
published spike trains. [Lagorce et al., section 4.3](https://www.frontiersin.org/journals/neuroscience/articles/10.3389/fnins.2015.00206/full)

The receiver accepts exactly one report from each cell if their arrival
dates differ by strictly less than 15 µs (0.15 R units at the primary time
scale). Fifteen microseconds is half the spacing of the source task's offset
classes. The paper describes a 15 µs detector window. This protocol chooses
15 µs as the maximum absolute difference and does not assume that this is
the same half-width as the paper's detector.
The receiver uses the same fixed delay of 0.35 units on both lines, with
the same delay in all comparisons. The expected decision is acceptance
only when both test ports match the trained ports and the programmed
offset is zero. An arrival exactly on the aperture boundary is rejected.
A missing or additional report also fails a positive trial. Report
training emissions and false positives separately.

The first benchmark reads the receiver's contract from emitted events.
A native receiver milestone must exhibit an R circuit that implements
this contract on the admitted input ranges. The existing
[LearnerConjunction](https://github.com/HevisNico/kernel-R/blob/11f476c3eb299263b980d5b69fb4592e8c0c093b/research/recursive-learning/native/LearnerConjunction.lean)
counts reports in separated slots. It does not establish this aperture.

## Comparators

Keep the same births, pulses, sensor guards, FIRE and recovery dynamics,
router and readout contract. Vary the rule that writes the active
log-gain. For every rule retain the READY, reserve and gain cap gates.
Account for the actual write in energy expenditure.

1. **Kernel R.** The ERROR current writes the memory while the sensor
   discharges between its realized entry and exit thresholds.
2. **Constant-current timed write.** Start at the same ERROR entry.
   Hold the write current constant for one shared duration D, with
   a fixed per-device multiplier on current. The timer ends the write
   independently of the sensor's return to READY. With all gates open,
   the dose is I times D. Use I = 4 in log-gain units per unit time and
   D = 0.15 for the nominally matched 0.6 dose. Allow a second comparator
   to choose the best shared nominal current and
   duration for the registered worst-case criterion. Require the timer
   to finish by time 16 on all allowed devices. Keep cap contact in the
   model and report whether it changes the outcome.
3. **Timed-discharge ablation.** At ERROR entry start an independent
   copy of the exponential discharge at the realized upper threshold.
   Use that current for the timer's duration under the same gates.
   The sensor still follows its original guards. Include long
   durations up to the same time-16 limit. With uninterrupted exposure
   the dose tends to eight times the entry charge as duration increases.
   This control can retain the binary distinction between trained and
   untrained ports. Its coincidence performance is part of the test.

Fixed-width writes motivate comparator 2. Its constant-current law is a
model of one programming mechanism. [Figueroa et al., section 3.2](https://papers.nips.cc/paper_files/paper/2004/file/f6185f0ef02dcaec414a3171cd01c697-Paper.pdf)

## Variation and outcomes

Use the existing independent fixed fabrication boxes of ±0.3% and ±10%,
plus a nominal control. Vary the two ERROR thresholds independently within
relative boxes with radii 0%, 0.3%, 1%, 2%, 3% and 5%. Independently vary
the FIRE threshold within a box with the same set of radii. Sweep the two
radii separately, including nominal FIRE with varying ERROR thresholds and
the reverse. Other guards stay nominal. Use the same realized guards and
common fabrication values in paired comparisons. In comparator 2, independently
sweep bounded current mismatch of 0%, 0.3%, 1%, 3%, 5% and 10%. For the ablation
the discharge rate comes from the same fabrication draw as in R.
Treat the cross-product as a sensitivity study. These intervals are model
inputs and are not a joint tolerance specification for a fabricated circuit.

## Registered local prediction

For the nominal positive trial at 17, a rested charge of 0.1, and the
residual from the time-zero training pulse, the closed-form READY response
gives a read latency of approximately 0.45137 model units. At the nominal
crossing, its local sensitivities are approximately −0.76823 units per unit
of log-gain dose and +0.85376 units per unit of FIRE threshold.

If each ERROR endpoint has independent relative error at most ε_E, its
worst-case dose error is approximately ε_E in log-gain units. A constant
current write with relative error ε_I around its matched 0.6 dose has
worst-case dose error 0.6 ε_I. FIRE threshold relative error is ε_F.
With independent opposing changes in the two cells, and the ±0.10 units
of relative input jitter, predict the primary-scale coincidence boundary

    R:                0.76823 ε_E + 0.85376 ε_F < 0.025
    nominal timer:    0.46094 ε_I + 0.85376 ε_F < 0.025

These are first-order estimates for the positive pair and the two adjacent
offset classes. They assume no missed or extra fires, open gates, no cap
contact and a single transverse crossing. Test all of those conditions.
Common-mode ERROR threshold errors produce a different, smaller dose
sensitivity than independent opposite-sign endpoint errors. The formulas
do not prove a box-wide result or a hardware tolerance.

## Execution and conclusion rule

Before the first run, commit the complete runner, its exact dependencies,
event-order policy and numerical solver settings. Record the full runner
commit and the protocol commit in every result. Use the pinned model commit
above. Do not describe this registration as preceding the earlier one-cell
exploration.

For each box and time scale evaluate the nominal point, all single-variable
endpoint perturbations, and 512 independently drawn paired parameter vectors
using NumPy PCG64 with seed 20261110. Generate the draws once in a fixed,
documented parameter order and reuse them across methods. For every draw test
both training labels, all four input port pairs, the three offsets and all
four jitter endpoint pairs. Record actual vectors, results, software versions
and hashes. A Monte Carlo pass is a sampled result. A universal result needs
a proof or certified enclosure for the entire box, including interior
parameter values and legal event orderings.

Report a separation only if R satisfies the full decision contract for every
admissible execution in the declared box and the comparison establishes
failure for every permitted common timer setting. Certify both statements
or identify the exact conditional assumptions and scope. If both pass, both
fail, or the comparison remains undecided, report that outcome directly.
Do not infer impossibility from failure of the nominal timer alone. Report
binary recognition and coincidence results separately.

Report a worst-case coincidence margin for the positive class and a
worst-case rejection margin for wrong-offset pairs with two reports.
Report missing reports, extra reports and responses on untrained ports.
Separately score recognition of the trained port pair using the two FIRE
bits alone, without the offset requirement. Include
outcomes where the best timed write meets the contract. For Lean,
separate existence of a complete run, the decision in every complete
run and any impossibility theorem for a comparator. An impossibility
claim must cover every allowed shared setting. A sampled sweep can
supply witnesses and estimates.

Published measurements establish that analog mismatch can be material
and that comparator offsets can be reduced by circuit techniques. They
refer to other circuits. A hardware comparison requires a selected
implementation and paired bounds or distributions for the effective
threshold differences, FIRE threshold, write currents and timing.
An experiment with recorded inputs additionally requires a frozen
trace manifest and a common encoder selected before running either
variant. [DYNAP-SE mismatch study](https://www.nature.com/articles/s41598-021-02779-x)
[Measured comparator offset study](https://www.mdpi.com/2079-9292/8/1/13)
