# What the two-cell network should learn, written before it is simulated

**Exploratory. Not a preregistration.** Written and pushed before any
simulation of two cells joined by the router: at this commit the only runs
that exist are of one cell alone ([`PERCELL.json`](PERCELL.json)). It is a
first trial of the method that the decisive experiment needs: measure each
cell alone, apply the rule of the theorem, state the learned state, then run
the network.

## The rule

For a port, in mV counted from its service threshold:

- its **reserve** before a read is `-gap + (writes so far) x dose`;
- a pulse on the same cell `g` time units earlier **helps** the read by `h(g)`,
  the residual charge it left on the main capacitor: measured below;
- the read **fires** if `reserve + h >= 0`; otherwise it is silent and writes
  one dose. This is the guarded score of
  [`../network-stability/THEOREM.md`](../network-stability/THEOREM.md) with
  one dose as `d`, `-gap` as the bias and `h` as the contribution of the
  recent past;
- a FIRE of a cell is routed if its date is inside the gate of an edge; the
  pulse starts at the target `7/20` unit later;
- a pulse that finds its cell protected is not predicted here: none of the
  two calendars below sends one.

## The measures, on one nominal cell alone

Both cells of the network are this cell; their four ports measure the same.

| Quantity | Value |
|---|---|
| Gap of a port at its preset | 4.850 mV, 3.594 doses |
| Dose | 1.3495 mV |
| Need | 4 writes |
| Room of the last silence (before the 4th write), isolated | 0.801 mV |
| Room of the first FIRE (after the 4th write), isolated | 0.548 mV |
| Help from a pulse 8 units earlier | +0.63 mV after a silent pulse, +0.70 mV after a FIRE |
| Help from a pulse 6.5, 12, 16, 22 units earlier | +1.4 to +1.5, +0.12, +0.05, +0.015 mV |
| Latency of the first FIRE, isolated; 8 units after a FIRE | 0.914; 0.840 |
| Protected after a FIRE until | 5.5 to 5.6 units after the start of its pulse |

The fourth read of a train 8 units apart is the tight one: its reserve is
-0.801 mV and the pulse before it helps by +0.63 mV. It should stay silent,
by 0.17 mV. On one cell alone it does (train `8 units apart`: `ssssFFF`).

## Calendar N: the native reciprocal witness, as it is

Sources of A (cell `a`, port 1) at 0, 8, 16, 24, 32, 160, 168, 176; sources of
B (cell `b`, port 2) at 320, 328, ..., 368; forward edge for the FIRE of A
dated in [160, 184), return edge for the FIRE of B dated in [344, 376); both
delays 7/20; horizon 459.9. From `router.native_reciprocal()`.

| Port | Decisions expected, in order | Writes |
|---|---|---|
| `a1`, sources of A | `ssssFFFF`: four silences, then a FIRE at 32, 160, 168 and 176 | 4 |
| `b1`, forward wire | `sss`: three pulses, near 161.26, 169.19 and 177.19, all silent | 3 |
| `b2`, sources of B | `ssssFFF`: four silences, then a FIRE at 352, 360 and 368 | 4 |
| `a2`, return wire | `sss`: three pulses, near 353.20, 361.19 and 369.19, all silent | 3 |

A fires 4 times and B 3 times; 3 forward and 3 return pulses are routed; no
pulse finds its cell protected; nothing is left in the queue at the horizon.
Ports `b1` and `a2` end one dose short of their threshold: this circuit needs
four doses where the witness needs one (B, forward) or three (A, return),
and the witness sends three pulses.

This differs from the native witness in three places, all expected from the
measures: A's source at 24 is silent here (it fires in the witness) and its
source at 32 fires here (in the witness it is a protected arrival that
writes a recovery dose); the forward and return wires never fire.

## Calendar L: the same construction with longer trains

Eight forward sources of A (160 to 216), ten sources of B (320 to 392), gates
[160, 224) and [344, 400). From `router.longer_reciprocal()`.

| Port | Decisions expected | Writes |
|---|---|---|
| `a1` | `ssssF` then `FFFFFFFF` | 4 |
| `b1`, forward wire | `ssssFFFF` | 4 |
| `b2` | `ssssFFFFFF` | 4 |
| `a2`, return wire | `ssssFF` | 4 |

Every port ends trained, each with four writes; A fires 11 times (9 on its
sources, 2 on the return wire), B fires 10 times (4 on the forward wire, 6 on
its sources); 8 forward and 6 return pulses are routed.

## What would contradict this

A different decision anywhere, a write count other than the one given, a
pulse that arrives while its cell is protected, or a pulse left in the queue.
The fourth pulse of each wire in calendar L is the tight one (0.17 mV).
Dates of arrival are given to 0.05 unit only.
