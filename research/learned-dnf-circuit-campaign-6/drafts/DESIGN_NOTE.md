# Campaign 6 of the learned AND-OR circuit: design note

**Draft for review by the owner and both coordinators. It sets no rule.** Rules come only later, in one
self-contained `PREDICTION.md`, and only if the development batch below says so.

## The goal, unchanged

Three SKY130 cells with their own mismatch, trained only by their own pulses, learn `(A and B) or (C and D)`. Each
cell's answers are predicted in advance from measures of that cell alone. The prediction is checked by the Lean gate
(#177, #178), and the network runs then test it.

## Why campaigns 4 and 5 stopped

Campaign 4's time limit was set from the nominal cell, and mismatched cells take longer to simulate. Campaign 5 fixed
that. But it measured each read's charge and compared it with the *nominal* firing level, while under mismatch each
cell's latch fires at its own level, about ±2 % away. The budgets were about 1 %, so most cells were set aside.

## The idea: measure where each cell fires, instead of assuming it

Campaign 3 handled mismatch: 11 of 12 instances were measured, 7 were eligible, and its primary claim held. It never
compared anything with a nominal level. Its robust scan (`robustscan.py`) brought a port to chosen stored voltages
and found, by bisection to 20 uV, the state at which that cell fires. Reads that disagree near the threshold are read
three times and decided by majority. The need follows from the measured threshold, and the bisection's half bracket
enters the budget.

Campaign 6 applies the same scan to the reads the AND-OR theorem uses:

- layer 1: the pair read of `a` (A with B) and of `b` (C with D), along the direction training moves them (both
  ports dosed together), and each port alone at the trained state;
- layer 2: each line of `c` alone, and both lines together.

## What is reused as it is

- the launch kit, the stage protocols, safeguards (i) and (ii), and the seed and noise-model guards;
- the Lean gate, its checkers and its audit;
- exact arithmetic and the pinned toolchain;
- the time limits of twice the expected cost, and a rehearsal under real conditions before any launch;
- the injected noise model, with decision 5's constants;
- the robust scan and the majority rule of campaign 3, adapted only to two-port reads and to routed pulses.

## The few rules the preregistration would hold

1. Each read kind's threshold is measured by the robust scan on that cell, never assumed: mismatch moves it.
2. Disputed states are read three times and decided by majority, as in campaign 3: it removes most near-threshold
   disagreements without any tolerance band.
3. An instance is measured when every scan gives a consistent bracket: otherwise it has no prediction.
4. Needs and budgets come from the measured thresholds, and the half bracket enters every budget: that is the
   measure's own error.
5. An instance is eligible when every relevant read clears its threshold by its budget: only eligible instances get
   network runs.
6. The claims hold for eligible instances only, which are selected from per-cell measures before any network run: they
   are not claims about mismatched cells at large.
7. Time limits are twice the expected cost, and a rehearsal under real conditions comes before any launch: campaigns
   4 and 5 showed both are needed.

## The development batch and the stopping rule

Ten fresh development seeds (7701 to 7710) are scanned and calibrated under this design, with code pushed before it
runs, outside any campaign. If at least 2 of the 10 are eligible, and 12 instances fit within 8 h of expected compute
at the batch's measured costs, campaign 6 is preregistered with 12 instances, seeds from 7801. Otherwise the circuit
campaigns stop, and the diagnostic is published as the result.

## Questions the batch must answer before any rule is written

- **Does a cell's firing level depend on the read kind** (a single port, both ports, a routed line)? Campaign 5's
  development data hint that it does for `c`, by about 0.4 %. The kernel's model has one threshold per cell, so if
  the level depends on the kind, the mapping from the scans to the gate's fields has to be settled first. That is a
  question for the theory, not a rule to choose.
- **What the scans cost.** A campaign-3 scan took 400 to 520 s on the nominal cell, and this design needs several per
  instance. The batch measures it.
- **Whether two-port and routed reads scan as cleanly** as campaign 3's single ports did, with brackets as narrow.

## What it cannot show

Nothing about silicon, layout, wires or a real router. Nothing about noise other than the injected model. Nothing
about cells that are not eligible.
