# The learned AND-OR circuit: campaigns 4 and 5, in plain words

**Neither campaign tested its claim.** This page says what they tried, why each one stopped, and where their full
records are. Both are kept on their own branches, as an archive. They are not merged here.

## What they tried

Three transistor-level cells (SKY130, simulated with ngspice), each with its own random manufacturing mismatch, are
wired as a small network. Trained only by their own pulses, they should learn `(A and B) or (C and D)`. The test is
whether each cell's answers can be **predicted in advance from measures of that cell alone**, with the prediction
checked by a Lean proof (#177, #178), and whether the network then answers as predicted. Each campaign wrote its rules
down before any data (a preregistration), measured the cells (stage M), and would then have run the networks.

## Campaign 4: stopped by a time limit

Every "guard on" calibration run of stage M reached its time limit of 660 s, so no instance could be measured and
nothing was predicted or tested. The limit had been set at 1.3 times one run on the nominal cell. Campaign 5 later
measured these runs at 485 to 514 s on the nominal cell and 705 to 734 s on mismatched cells, under the same load.
Mismatched cells take longer to simulate, and every one of them would have been cut.

## Campaign 5: closed before its campaign stages

Campaign 5 fixed the limits at twice the cost model (1 850 s for these runs). It rehearsed under the campaign's real
conditions, on development cells that enter no claim, and the time limits held with a wide margin (at most 0.45 of a
limit). But the rehearsal showed a deeper problem:

- Under mismatch, each cell's latch fires at its own charge level, spread by about ±2 % around the nominal level.
- The preregistered rules compare every reading with the nominal level, and allow about 1 % of error.
- So most mismatched cells would have been set aside: only 1 of the 3 development instances was usable, and it was not
  eligible for a prediction.

The campaign would most likely have ended "not established". It was closed before any campaign cell was simulated.

## What comes next

A sixth campaign, if any, starts from a short design note in plain language, reviewed before any rule is written. It
is to start from what worked: campaign 3's threshold scan, which handled mismatch, the launch kit and the Lean gate.

## The records

- Campaign 4: [`REPORT.md`](https://github.com/HevisNico/kernel-R/blob/6232e16859b09b58dffd25bafac114e05ed905cb/research/learned-dnf-circuit-campaign-4/REPORT.md)
  on the branch `research/learned-dnf-circuit-campaign-4`, with its preregistration and eleven amendments.
- Campaign 5: [`PREDICTION.md`](https://github.com/HevisNico/kernel-R/blob/a2d8badd7a5dea5322a743189b8e2497373c8089/research/learned-dnf-circuit-campaign-5/PREDICTION.md),
  [amendment 1](https://github.com/HevisNico/kernel-R/blob/fb5a79f79dfbf51a3f481a21994e6f9431cc77ee/research/learned-dnf-circuit-campaign-5/AMENDMENT_1.md)
  and the closing
  [amendment 2](https://github.com/HevisNico/kernel-R/blob/8f74544abbfc15f657af8da6057ec545b506e66b/research/learned-dnf-circuit-campaign-5/AMENDMENT_2.md),
  on the branch `research/learned-dnf-circuit-campaign-5`. The code is on `research/learned-dnf-circuit-campaign-5-wip`
  and the rehearsal on `research/learned-dnf-circuit-campaign-5-rehearsal`, with its evidence on the
  `evidence/learned-dnf-circuit-campaign-5-*` branches.
