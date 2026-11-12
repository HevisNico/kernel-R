# Predictions

Written on 2026-11-12, after the netlist was frozen and before any run
of the campaign. This file is not edited after the campaign starts.

## What was known when this was written

These predictions are not blind. An earlier pass of the same circuit
was run on 2026-11-11 with ideal stimulus edges, other seeds and
another noise wiring. Its results were known:

- nominal cell: 4 silent pulses per port, a step of 1.3465 mV, joint
  read at 0.267;
- 20 noisy runs: 4 silent pulses in every run, sigma of the joint read
  0.0006, sigma of a silent step 0.087 mV, sigma of the change of a
  port at rest 0.076 mV;
- 84 cells with mismatch and noise: 2 to 7 silent pulses, joint read
  from 0.259 to 0.273 with sigma 0.0033, 14 ports of 168 with one
  silent pulse after their first FIRE;
- corners: joint read from 0.2635 to 0.2705;
- refresh: a relapse every 22 or 23 periods under 0.1 TΩ, every 221 or
  222 periods under 1 TΩ.

Every run below uses seeds that were never run. Predictions 14 and 18
are about experiments that were never run in any form.

A dose is the step of the nominal cell, 1.3465 mV. Latencies are in
time units of 20 µs. A relapse is a silent pulse after the first FIRE
of a port.

## Checks: the frozen netlist reproduces the bring-up

Not predictions. The nominal cell without noise:

- C1. pattern `ssssFFFFFF` on both ports, FIRE on the joint pulse;
- C2. every silent step between 1.345 and 1.348 mV;
- C3. every firing step below 0.002 mV in size;
- C4. write window from 1.777 to 2.040, end of the protection at 5.59;
- C5. joint read between 0.2665 and 0.2685.

## Noise on the nominal cell, 20 runs

- P1. **The stop does not move.** 4 silent pulses on both ports in at
  least 18 runs. Never fewer than 3, never more than 5.
- P2. **The read barely moves.** Sigma of the joint read below 0.0012.
  Every joint read between 0.264 and 0.271.
- P3. **The read of the stored voltage is noisy.** Over one period the
  stored voltage of a port at rest changes with a sigma between 0.05
  and 0.10 mV.
- P4. **The write is cleaner than its read.** The sigma of a silent
  step, with the sigma of P3 removed in quadrature, is below 5% of a
  dose (0.067 mV).
- P5. **A firing pulse writes nothing.** The firing steps have a mean
  within 0.01 mV of zero and a sigma within 25% of the sigma of P3.

## Mismatch and noise together, 100 cells

- P6. **Every cell stops.** Both ports of every cell stop within 10
  pulses, after 2 to 8 silent pulses.
- P7. **The joint read agrees between cells.** Every cell fires on the
  joint pulse. Sigma between 0.0025 and 0.0042. Every joint read
  between 0.250 and 0.280. Every pair of cells within 0.05.
- P8. **Only a late stop relapses.** A port relapses only if its first
  FIRE came later than 0.95. Between 4% and 14% of the ports relapse.
  No port relapses twice. Every relapse writes a step within 20% of a
  dose.
- P9. **Nothing accumulates at the firing pulses.** For the ports
  without relapse, the total change of the stored voltage over all
  their firing pulses has a mean within 0.03 mV of zero and a sigma
  below 1.5 times the sigma of the change of a port at rest.
- P10. **The gate holds.** In every run of the campaign, no firing
  pulse steers the sensor current to the integrator.

## After the stop, nominal cell without noise

- P11. Over 22 firing pulses the stored voltage moves by less than
  0.01 mV in total.

## Corners and temperature, without noise

- P12. The cell stops at ss, ff, sf and fs at 27 °C, and at the typical
  corner at −40 and 125 °C. Silent pulses per port: 4 at the four
  corners at 27 °C, 2 at −40 °C, 7 at 125 °C. Joint read between 0.262
  and 0.272.

## Refresh under continued pulses, one port

The leak is a resistance from the summing node of the integrator to
ground.

- P13. **No leak, no noise, 150 pulses.** No relapse. The stored
  voltage moves by less than 0.05 dose after the stop.
- P14. **No leak, with noise, 150 pulses.** At most one relapse.
- P15. **0.1 TΩ, no noise, 150 pulses.** A relapse every 22 or 23
  periods. Never two silent pulses in a row. Every relapse writes
  between 1.27 and 1.31 mV. The stored voltage stays within 1.05 dose
  after the stop.
- P16. **1 TΩ, no noise, 560 pulses.** First relapse between pulses 85
  and 100. Two consecutive relapses 220 to 224 periods apart.
- P17. **0.1 TΩ, with noise, 150 pulses.** Two consecutive relapses 17
  to 28 periods apart. Never two silent pulses in a row. The stored
  voltage stays within 1.6 dose after the stop.
- P18. **0.1 TΩ, mismatch and noise, 8 cells, 100 pulses each.** Every
  cell maintains itself. In every cell the mean distance between two
  relapses is between 17 and 29 periods, two silent pulses in a row
  happen at most once after the stop, and the stored voltage stays
  within 1.8 dose after the stop.

## Anomalies

- P19. No run fails. The guard reports nothing: no protection that
  rises within 0.05 of the pulse edge or before it, after the pulse,
  twice in a period, without an end, or in the period at rest.

## What would count against the mechanism

- A cell that does not stop, or a port that keeps writing after its
  stop without relapsing (P6, P9, P10).
- A stop set by noise and not by the gain (P1 failing by several
  pulses).
- A cell that falls silent under a leak and does not recover, or a
  stored voltage that leaves a band of three doses (P15, P17, P18).

## What this campaign does not test

The joint read of this circuit is near 0.267. The window proved for
the ideal model is (0.239, 0.2554]. The circuit is outside it, and no
result here is a test of that window. The campaign tests the
mechanism: write on a silent pulse, no write on a firing pulse, a stop
that holds, and a read that agrees between cells.
