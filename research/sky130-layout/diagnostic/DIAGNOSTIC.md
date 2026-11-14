# Diagnostic of the stage-P report

**Exploratory. Not a campaign, nothing preregistered, no verdict.** It
reads [`../phase1/P_REPORT.md`](../phase1/P_REPORT.md), which is not
changed.

```sh
cd research/sky130-layout/diagnostic
python3 -I diag.py refusals && python3 -I diag.py levels && python3 -I diag.py ablate && python3 -I diag.py report
```

What was run: nothing for point 1; **six exploratory simulations of the
nominal cell** for points 2 and 3, on the stage-P netlist with the
primary list, no noise, 27 °C. One of three periods with every node
saved, and five trains of 22 periods with some capacitances taken out.
Outputs are in `build/`, not committed; hashes in
[`SHA256SUMS`](SHA256SUMS).

## 1. The refusals: the upper side of the rest band, by 0.00089

The condition is the same in status 3 and in rule A1: on every read
from 0 to the need `m` of the port, in its noisy test run,
`0.1 ≤ c_pre ≤ 0.1001`. `c_pre` is the charge of the main capacitor
just before the pulse; 0.1 is rest, and 0.0001 is 50 µV on `vq`.

**On all 16 ports it is `c_pre ≤ 0.1001` that fails, by 0.000887 to
0.000890.** `c_pre` is 0.10098 to 0.10099: `vq` is 0.49 mV below rest.

- It fails **on every read that follows a period in which port 1 was
  pulsed**, and on no other: reads 1 to `m` of a port 1, and the first
  read of a port 2 (pulse 10, which follows the last pulse of port 1).
- After a period of port 2, `c_pre` is 0.100001.
- On 6 ports a read is also below 0.1, by 2.4 × 10⁻⁶ at most. In the
  committed runs of the schematic the lowest value for these cells is
  0.1000000.
- On the schematic `c_pre` goes up to 0.10004.

**One capacitance does it: 1.674 fF between `vq` and `x1.ad`.**

- `x1.ad` is the delayed output of latch A of port 1. It falls by 1.8 V
  0.1 µs before the end of a period in which port 1 was pulsed.
- By arithmetic, 1.674 fF × 1.8 V on 5.076 pF moves `vq` by −0.594 mV.
  All capacitances on `vq` together give −0.542 mV; `vq` then leaks
  back for 4.2 µs. The simulation gives −0.472 mV.
- **Taken out, the refusal changes side.** Without that one
  capacitance the rest charge after a period of port 1 is 0.099945:
  below 0.1 by 0.000055, pushed by three smaller ones (`x1.adb`,
  `x1.vs`, `x1.vrefs`). The band is one-sided: any net push upward on
  `vq` leaves it.
- The same node of port 2 does not do it: `vq` has 0.082 fF to
  `x2.ad`, twenty times less. The two ports are mirror images; the wire
  of `vq` between them is not.

## 2. L4: not the FIRE path. Two nodes of the port next to the summing node

**The 0.014 mV is not a step of a firing pulse of one port.** In the
nominal run those are 0.000 and 0.001 mV. It appears where a port
passes between "pulsed" and "idle":

| Pulse of `nom_cell` | Port 1 | Step of port 1 |
|---|---|---|
| 10, the first pulse of port 2 | becomes idle | +0.014 mV |
| 20, the joint pulse | is pulsed again, and fires | −0.014 mV |
| 0, its first pulse | is pulsed for the first time | 1.343 mV written, against 1.357 after |

The joint pulse fires, so L4 counted it. **It is an offset of the
reading, not a loss of the stored charge:** the stored voltage is read
at the end of a period, and at that instant some nodes of the port sit
at another level when the port was pulsed than when it was idle. Each
moves the summing node through its capacitance to it.

Capacitances to `x1.sum`, ranked by `C × ΔV / C_f`, with the levels
read in the three-period simulation:

| Node | Capacitance to `x1.sum` | Its level, pulsed against idle | Move of the stored voltage |
|---|---|---|---|
| `x1.vs`, sensor node | 0.918 fF | −0.900 V | **+27.5 µV** |
| `x1.ad`, delayed latch A | 0.173 fF | +1.800 V | **−10.4 µV** |
| `x1.preb`, precharge control | 0.049 fF | +1.800 V | −3.0 µV |
| `x1.adb` | 0.006 fF | −1.800 V | +0.4 µV |
| every other node | | 0 or below 0.1 V | below 0.1 µV |
| **Sum** | | | **+14.5 µV; observed 14 µV** |

Port 2: 0.920 fF, 0.178 fF and 0.049 fF, the same sum within 0.3 µV.

Confirmed by taking them out: without the capacitances between a
summing node and the nodes of its own port, the steps at pulses 10 and
20 are 0.000 mV and the first silent step equals the later ones
(1.354 mV).

`p`, `pb` and the nodes of the FIRE comparator do not appear: no
capacitance is extracted between them and a summing node. The steering
control `si` has 0.226 fF to the summing node of its port; it is at the
same level at the end of a pulsed period and of an idle one, so it adds
nothing to this offset.

## 3. The link: one shared aggressor, two separate effects. L4 does not explain the refusals

| Nominal train, exploratory | Rest charge after a period of port 1 | Step when port 1 becomes idle |
|---|---|---|
| Primary list, as in stage P | 0.100983 | +0.014 mV |
| Without `vq`–`x1.ad` | 0.099945 | +0.014 mV |
| Without the summing-node capacitances of section 2 | 0.100983 | 0.000 mV |
| Without both | 0.099945 | 0.000 mV |
| No capacitance, areas of the layout alone | 0.100031 | 0.000 mV |

- **Removing the L4 disturbance leaves the refusals as they are**, and
  removing the cause of the refusals leaves L4 as it is.
- What they share is one wire: `x1.ad` is the aggressor on `vq`
  (1.674 fF) and the second one on `x1.sum` (0.173 fF).
- The count of silent pulses is 4 and 4 in all five trains.

**The rest band is not the only reason for the refusals.** 14 of the 16
ports also have a room that is not positive at status 3. Only
`t6065` port 2 and `t6074` port 2 are refused for the rest state
alone, and neither is one of the four ports of L12.

- The four ports of L12 were chosen for their room, and their room was
  large because they sat at the centre of their dose interval: start
  distance `a_s` of 0.0001 to 0.0011.
- Post-layout the gap of every port moves by +0.0122 to +0.0146
  (prediction L8, which holds). Their `a_s` becomes 0.0115 to 0.0141,
  against a half dose of 0.0211, and their room goes from +0.006 …
  +0.009 to −0.003 … −0.011.
- The capacitance added to `vq` is 75.6 fF on 5 pF: `log(1.0151)` is
  +0.0150. This is arithmetic, close to the shift; it was not tested by
  taking those capacitances out.

So L12 would fail without any coupling from the logic: **a common
shift of a third of a dose is enough.** This is the case that
[`../PHASE1_PLAN.md`](../PHASE1_PLAN.md) called the weakest candidate.

## What this diagnostic does not show

- Nominal cell only. The refusals are read on the 8 cells with
  mismatch; the mechanism is shown on the nominal cell.
- The capacitances are those Magic extracts, with the plate rule of
  [`../AMENDMENT_3.md`](../AMENDMENT_3.md). No field solver.
- Taking a capacitance out of a list is not a layout. A layout without
  it would have others.
