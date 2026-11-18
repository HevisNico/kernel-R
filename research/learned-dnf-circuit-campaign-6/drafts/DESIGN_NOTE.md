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

Campaign 3 handled mismatch: 11 of 12 instances were measured, 7 were eligible, and its primary claim held
([its report](https://github.com/HevisNico/kernel-R/blob/8bcd3d744f101378c308a0af9da80631dded715f/research/network-circuit-ring-campaign-3/REPORT.md)).
It never compared anything with a nominal level. Its robust scan
([`robustscan.py`](https://github.com/HevisNico/kernel-R/blob/8bcd3d744f101378c308a0af9da80631dded715f/research/network-circuit-ring-campaign-3/robustscan.py))
brings a port to chosen stored voltages and finds, by bisection to 20 uV, the state at which that cell fires.

- **Disputed states.** A read depends a little on what came just before it: the previous pulse, and the direction from
  which the stored voltage was brought. So a state that fired can turn out no stronger than one that stayed silent.
  Such a state is brought back twice more, from its neighbours, and read again in isolation. It counts by the majority
  of its three reads.

Campaign 6 applies the same scan to the reads the AND-OR theorem uses:

- layer 1: the pair read of `a` (A with B) and of `b` (C with D), along the direction training moves them (both
  ports dosed together), and each port alone at the trained state;
- layer 2: each line of `c` alone, and both lines together.

Campaign 3's cells did not learn, but these do. **A need is then predicted from two measures:** the scanned threshold,
in stored-voltage space, and each dose's measured move of the stored voltage (campaign 5's joint dose). This assumes
that a state imposed from outside fires where the same state reached by training fires. The batch tests that first.

## What is reused as it is

- the launch kit, the stage protocols, and the checks that the frozen code and its protocol have not changed since the
  freeze;
- the Lean gate, its checkers and its audit;
- exact arithmetic and the pinned toolchain;
- the time limits of twice the expected cost, and a rehearsal under real conditions before any launch;
- the injected noise model, with decision 5's constants;
- the robust scan and the majority rule of campaign 3, adapted only to two-port reads and to routed pulses.

## The few rules the preregistration would hold

1. Each read kind's threshold is measured by the robust scan on that cell, never assumed: mismatch moves it.
2. Disputed states are read three times and decided by majority, as in campaign 3: a read depends a little on its
   history, and the majority settles it without a tolerance band.
3. An instance is measured when every scan gives a consistent bracket: otherwise it has no prediction.
4. Needs come from the scanned thresholds and the measured dose moves, and the half bracket enters every budget: that
   is the measure's own error.
5. An instance is eligible when every relevant read clears its threshold by its budget on both sides of its crossing:
   only eligible instances get network runs.
6. The claims hold for eligible instances only, which are selected from per-cell measures before any network run: they
   are not claims about mismatched cells at large.
7. Time limits are twice the expected cost, and a rehearsal under real conditions comes before any launch: campaigns
   4 and 5 showed both are needed.

**One threshold per cell.** The kernel's model has one threshold per cell. By default, each cell's threshold is the
lowest of its scanned levels, and the largest spread across its read kinds is added to its budgets. This keeps the
theory unchanged. The alternative, a threshold per read kind, would need a change of the theory first.

## The development batch and the stopping rule

Ten fresh development seeds (7701 to 7710) are scanned and calibrated under this design, with code pushed before it
runs, outside any campaign. With `k` of them eligible, the campaign size is `I = ceil(30 / k)`, for 3 expected eligible
instances. Campaign 6 is preregistered, with seeds from 7801, only if `k >= 2`, `I <= 40`, and the expected compute is
at most 28 800 s at the batch's measured costs. Otherwise the circuit campaigns stop, and the diagnostic is published
as the result.

## Questions the batch must answer before any rule is written

1. **Does the scan predict training?** On each instance, do the scanned threshold and the measured dose moves predict
   the stage at which the calibration deck's training actually crosses?
2. **Where do crossings land within a step?** Training advances in steps of about 3.8 % of the score. Scanning removes
   the ±2 % spread between cells, but not where a crossing falls within its step. For each crossing, the batch reports
   the margin on both sides (stage `need - 1` and stage `need`), and which budget term dominates: the half bracket, the
   variation of the dose moves, or the noise constants.
3. **Does a cell's firing level depend on the read kind** (a single port, both ports, a routed line)? Campaign 5's
   development data hint that it does for `c`, by about 0.4 %. The batch reports the spread, which the default above
   adds to the budgets.
4. **What do the scans cost?** A campaign-3 scan took 400 to 520 s on the nominal cell, and this design needs several
   per instance.
5. **Do two-port and routed reads scan cleanly**, with brackets as narrow as campaign 3's single ports?

## What it cannot show

Nothing about silicon, layout, wires or a real router. Nothing about noise other than the injected model. Nothing
about cells that are not eligible.
