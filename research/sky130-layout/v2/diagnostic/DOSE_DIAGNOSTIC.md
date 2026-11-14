# Second layout: diagnostic of the dose

**Exploratory. Not a campaign, nothing preregistered, no verdict.** It
reads [`../S_REPORT.md`](../S_REPORT.md), which is not changed: S5 and
L3 fail because a silent pulse writes 1.309 mV where the schematic
writes 1.3465 mV.

```sh
cd research/sky130-layout/v2/diagnostic
python3 -I dose.py groups && python3 -I dose.py singles x vgd vs && python3 -I dose.py report
```

What was run: **37 exploratory simulations of the nominal cell**, each
the read of the certification campaign (three periods, one pulse on
each port of a fresh cell) on the netlist of the second layout, primary
list, with some capacitances taken out of the list. No noise, 27 °C.
Outputs in `build/`, not committed; hashes in
[`SHA256SUMS`](SHA256SUMS). The two ports give the same step in every
run, within 0.001 mV.

## Node by node

| Capacitances taken out | How many, in both ports | Silent step | Against the second layout |
|---|---|---|---|
| none: the second layout | | 1.309 mV | |
| all: the areas alone | 2 283 fF | 1.349 mV | +0.040 mV |
| every one on a node `x` | 12.0 fF | **1.361 mV** | **+0.052 mV** |
| every one on `vgd` | 18.8 fF | 1.321 mV | +0.012 mV |
| every one on a summing node | 319.5 fF | 1.314 mV | +0.005 mV |
| every one on `vrefs` or `vrefsn` | 13.7 fF | 1.309 mV | 0 |
| every one on a sensor node `vs` | 23.9 fF | **1.273 mV** | **−0.036 mV** |

**The dose is not lost on the sensor node or in its array.** The
capacitances on `vs` add to the dose, as arithmetic says they must: they
add to `cs`. **It is lost on `x`**, the node between the sensor and the
two steering switches.

## Pair by pair

Every capacitance of at least 0.05 fF on `x`, `vgd` and `vs`, taken out
alone, in both ports at once. Those that move the step by 0.002 mV or
more:

| Capacitance | Size, per port | Step without it | What it does to the dose |
|---|---|---|---|
| `x`–`sd` | 1.11 fF | 1.368 mV | **−0.059 mV, −4.5%** |
| `vs`–`sd` | 0.25 fF | 1.323 mV | −0.014 mV |
| `vgd`–`si` | 1.10 fF | 1.322 mV | −0.013 mV |
| `vs`–`0` | 5.39 fF | 1.291 mV | +0.018 mV |
| `vs`–`si` | 0.20 fF | 1.296 mV | +0.013 mV |
| `vs`–`vdd` | 2.28 fF | 1.302 mV | +0.008 mV |
| `vs`–`vmem` | 1.68 fF | 1.304 mV | +0.006 mV |
| `x`–`si` | 0.98 fF | 1.304 mV | +0.005 mV |
| `vgd`–`0` | 6.44 fF | 1.306 mV | +0.004 mV |
| `vs`–`vpre` | 0.71 fF | 1.307 mV | +0.002 mV |
| `x`–`0` | 2.67 fF | 1.307 mV | +0.002 mV |

The other 18 pairs move it by 0.001 mV or less.

**Three capacitances to the steering controls take 0.086 mV out; the
others put 0.058 mV back.** `si` and `sd` are the two controls of the
steering switches, each the inverse of the other.

- `x`–`sd` alone is the size of the whole effect. By arithmetic:
  1.11 fF × 1.8 V is 2.0 fC, and a silent pulse moves 40 fC
  (400 fF × 0.1 V): 5%. When the window opens `sd` falls while the
  switch to the summing node is on, and the charge is taken from the
  summing node; when it closes `sd` rises with that switch off, and the
  charge goes back to `vcm`.
- In the first layout `x`–`sd` was 0.13 fF and `x`–`si` 0.17 fF. The
  second layout protected `vq` and the summing nodes and left `x` a
  wire like the others; the router laid it along `sd` and `si`.

## What the dose would be without them

**It would not come back to the schematic.** The capacitances from `vs`
to nodes that do not move add 0.0033 mV to the dose for each
femtofarad: 5.39 fF to node 0 gives 0.018 mV, 2.28 fF to `vdd` 0.008 mV,
1.68 fF to `vmem` 0.006 mV.

- With the three capacitances to `si` and `sd` gone and the two that
  compensate them gone too, the table gives 1.309 + 0.086 − 0.018, about
  **1.377 mV**: above the range of S5 (1.340 to 1.365 mV), on the other
  side.
- The areas alone give 1.349 mV. Each femtofarad of wire on `vs` then
  adds a quarter of a percent. The range of S5 leaves room for about
  5 fF; the second layout has 11 fF on `vs` to nodes that do not move.
- The first layout wrote 1.357 mV, inside the range. Its `vs` had 19 fF;
  it was inside by compensation, not by design.

This sum is arithmetic on the table. The capacitances were taken out
one at a time and the effects are assumed to add; the group runs say
they nearly do (+0.052 mV for `x` as a group, against +0.051 mV for its
pairs one by one).

## What this diagnostic does not show

- Nominal cell only, and reads of a fresh cell only.
- The capacitances are those Magic extracts. Taking one out of a list
  is not a layout.
- Nothing about why `vgd`–`si` lowers the dose: `vgd` is the gate of
  the discharge device, and the size of the effect is consistent with
  its current being moved while the window is open. It was not looked
  into.
