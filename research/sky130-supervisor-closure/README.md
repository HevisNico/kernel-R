# SKY130 supervisor: closing the qualification

**Phase 1, exploratory. Nothing here is preregistered, no leakage jump was
simulated, and no registered run exists.** This folder continues
[`../sky130-supervisor-qualification`](../sky130-supervisor-qualification/README.md)
(PR 123) and answers the six points that were left open before a
PREDICTION.md can be written: the reads to guarantee, a capacity compatible
with all of them, the second port, the deterministic bounds, the launch kit,
the budget. It stops there, for the owner's review.

Everything is a transistor-level simulation (ngspice 42, SKY130 models) of the
two-port cell of [`../circuit/cell.spice`](../circuit/cell.spice). The circuit
is not changed; only its ideal stimulus is (see [`sim.py`](sim.py)).

**The qualification was done twice.** First on the netlists of the earlier
campaigns, which give the transistors no source or drain area. Then stage J
of the layout study (PR 125) showed that without those areas the device model
has no junction capacitance and a junction current that ignores temperature:
at 125 C the cell with areas loses 0.19 mV per period by itself. The whole
qualification was done again on netlists with the junction areas of stage J
([`JUNCTION_AREAS.md`](JUNCTION_AREAS.md)). **The results with areas are the
ones that count**: [`QUALIFICATION.json`](QUALIFICATION.json), and every table
of this page unless it says otherwise. The first qualification is kept as it
was, in [`QUALIFICATION_SCHEMATIC.json`](QUALIFICATION_SCHEMATIC.json), and
summarised at the end.

All numbers are recomputed from the raw waveforms by [`closure.py`](closure.py);
the tables of this page are written from the two files by [`tables.py`](tables.py).

## The netlist

`sim.deck(junction="areas")` expands the sub-circuits in place and gives each
of the 232 transistors the source and drain areas and perimeters of
[`junction/areas.csv`](junction/areas.csv), with
[`junction/netlist.py`](junction/netlist.py). Both files are those of stage J,
copied unchanged (same SHA-256 as in its manifest). The areas are those of
each transistor drawn alone; a layout that shares diffusions would have
smaller ones. No wire capacitance is added: there is no layout of the cell.

Identity test: the same expanded deck with every area at zero, against the
deck that is not expanded, on the nominal cell and on a mismatch instance:
the saved waveforms are identical point for point. The construction keeps the
cell and its mismatch sample.

## How the cell is operated here

Time is cut in slots of 220 us; the clocks of the cell repeat in every slot. A
port takes part in a slot only if it is selected. A **service period** is 440 us:

1. a **maintenance slot**: for each port, the supervisor either does nothing
   or runs one clock-only cycle (the port is selected and no input current is
   admitted). A clock-only cycle is a silent read: it writes one dose;
2. a **read slot**: the requested read. The reads cycle: port 1, port 2, both.

Before each maintenance slot the supervisor reads, for each port, the voltage
across its storage capacitor, `u = V(stored node) - V(summing node)`, as a
mean over 40 us that ended 20 us earlier. It turns it into a **reserve**,
`r = U_S - u`, counted in mV from the service threshold `U_S` of that port,
and gives it to the kernel, which answers `wait`, `maintenance` or `refuse`.
The kernel is [`kernel.py`](kernel.py): the definitions of
[`Model.lean`](../sky130-supervisor-qualification/lean/Model.lean) in exact
integers (unit 0.1 uV), tested against the properties that the Lean file
proves ([`test_kernel.py`](test_kernel.py)); it is a mirror, not a proved
translation. Each port has its own kernel and its own bounds.

Why the capacitor and not the stored node alone: the noise of the integrator
moves both nodes together. Measured on four noisy sequences of the first
qualification, a 40 us mean of the stored node alone has a standard deviation
of 0.048 mV and the kernel refused in all four; the difference of the two
nodes has 0.0001 mV.

Preparation comes before any service: from the preset of the deck, one
clock-only cycle per slot on each port that has its headroom
(`report + epsilon + Dmax <= C`), until both ports hold an entry certificate
(`report - epsilon >= S + H` and `report + epsilon <= C`). Nothing in the
preparation is a service.

## 1. The reads to guarantee

The cell was trained for three reads; these are the reads of the contract.

| Read | Correct when | Origin of the window |
|---|---|---|
| port 1 alone | exactly one FIRE, latency in [0.5, 1.0] pulse lengths, no write | the service read: a FIRE inside the pulse; 0.5 keeps it apart from a joint read |
| port 2 alone | the same | the same |
| both ports | exactly one FIRE, latency in [0.250, 0.280], no write | criterion P7 of [`../circuit/PREDICTION.md`](../circuit/PREDICTION.md), the cohort window of the trained cell |
| no port (idle slot, clock-only slot) | no FIRE | the output must stay silent outside reads |

Latency is counted from the start of the pulse, in units of its length (20 us).
A read that fires does not write; a silent read writes one dose and is a
failed service.

**The joint window is a proposal for the owner's decision.** Three historical
windows exist for the joint read: C5 [0.2665, 0.2685] (nominal), P12
[0.262, 0.272] (corners and temperature), P7 [0.250, 0.280] (cohort). P7 is
the widest; it is taken because the narrower ones leave no room for a
supervisor at all (one dose moves the latency by about 0.007). The window
(0.239, 0.256] of the ideal model is **not** claimed: the circuit reads near
0.267, outside it, as PR 123 already said. No decoding of a stored voltage
into a trained count is claimed either.

The joint latency falls when the reserves rise, and depends on their **sum**:
about -0.005 per mV at 27 C. So the lower edge of the joint window, 0.250,
is what limits the capacity. The upper edge of the joint window is never
approached (the joint latency is at most 0.277), nor the lower edge of the
single reads (at least 0.58 over the whole map). The upper edge of a single
read, 1.0, is the threshold `U_S` itself:

<!-- table reads -->
| Configuration | joint reads | joint latency near zero reserve (at sum, mV) | at the largest sum measured (mV) | largest single latency | smallest single latency (at reserve, mV) |
|---|---:|---:|---:|---:|---:|
| tt27 | 37 | 0.2731 at 0.20 | 0.2282 at 9.60 | 0.980 | 0.626 at 4.80 |
| ss27 | 37 | 0.2733 at 0.21 | 0.2287 at 9.61 | 0.980 | 0.628 at 4.81 |
| ff27 | 37 | 0.2729 at 0.19 | 0.2277 at 9.60 | 0.981 | 0.624 at 4.80 |
| sf27 | 37 | 0.2730 at 0.19 | 0.2278 at 9.59 | 0.981 | 0.624 at 4.80 |
| fs27 | 37 | 0.2729 at 0.21 | 0.2284 at 9.61 | 0.978 | 0.628 at 4.81 |
| tt-40 | 37 | 0.2711 at 0.21 | 0.2172 at 9.61 | 0.973 | 0.580 at 4.81 |
| tt125 | 37 | 0.2763 at 0.17 | 0.2406 at 9.58 | 0.961 | 0.665 at 5.18 |
| mm2001 | 37 | 0.2646 at 1.81 | 0.2253 at 10.23 | 0.914 | 0.591 at 5.69 |
| mm2002 | 37 | 0.2711 at 0.54 | 0.2326 at 8.54 | 0.999 | 0.637 at 4.54 |
<!-- end -->

## 2. A capacity compatible with all the reads

For each configuration, the largest sum of the two reserves at which the
joint read is still inside its window is read on the measured curve (linear
interpolation between neighbours, no extrapolation). Each port receives half
of it: `C` = half the limit of the sum. With `r1 <= C` and `r2 <= C` the
joint read is then inside its window, and the single reads are far inside
theirs.

4 mV per port, the capacity that phase 0 proposed, is confirmed unqualified:
the limit of the **sum** is 3.4 mV at -40 C, 4.5 to 4.7 mV at 27 C and
6.7 mV at 125 C.

## 3. The second port

Both ports are observed and maintained, each by its own kernel with its own
threshold and bounds. The imposed leak acts on both; nothing is assumed
about port 2 that is not measured on port 2. In all the sequences below the
two ports were maintained independently, sometimes in the same slot; every
clock-only cycle wrote exactly one dose on the port it was commanded on and
none on the other.

What a maintenance costs: one clock-only cycle on one port, in a slot where no
read is requested. At the reference leak (1e11 ohm) and 27 C a port loses
about 0.059 mV per period and a dose is about 1.35 mV: one cycle every 23
periods per port. At 125 C the port loses 0.25 mV per period, of which 0.19
by itself: one cycle every 5 periods.

## 4. The bounds, their justification and their margin

The kernel needs, for each port: `S` (a reserve at or above `S` gives a
correct read), `C`, `Dmin <= Dmax` (dose of one maintenance), `epsilon` (error
of a report), `H` (largest loss in one whole period). The theorems of
`Model.lean` then give, for every trajectory inside these bounds: the reserve
stays in `[S, C]` at every period, the kernel never refuses, provided
`H <= Dmin` and `S + 2H + 2 epsilon + Dmax <= C`.

The deterministic domain is nine configurations, each with its own bounds:
the five corners at 27 C, the typical corner at -40 C and 125 C, and two
mismatch instances (seeds 2001 and 2002). It is a list of nine, not a
continuous range: nothing is claimed between them.

| Bound | How it is obtained | Kind | Margin |
|---|---|---|---|
| `U_S`, threshold | per port: a bisection. The scan steers the stored voltage to the middle of the bracket (by the cell's own drift, an imposed leak, or a clock-only dose), reads, and halves the bracket; `U_S` is the lowest reserve whose read was still correct (FIRE, latency <= 1) | measurement: 18 scans, bracket at most 20 uV; latency monotone in the reserve in all 18 | `S` = 0.03 mV above `U_S`, plus the noise margin |
| `C` | half the limit of the sum, section 2; the level is 0.250 + 0.0005 + noise margin | measurement: 9 curves of the joint latency against the sum | 0.0005 on the latency (about 0.1 mV of the sum) |
| `Dmin`, `Dmax` | step of the reserve across each maintenance, plus the loss of the same period; smallest and largest over the sequences at the reference leak and at a larger one | measurement on the capacitor voltage itself, 27 sequences | 0.005 mV on each side, plus the noise margin |
| `epsilon` | the report is the capacitor voltage itself, read by the simulator's own mean; difference with the mean recomputed from the saved waveform | model (an ideal observer of two nodes; no converter is claimed) and measurement | 0.002 mV, against a largest measured difference below 0.001 mV |
| `H` | what the room condition leaves: `H = (C - S - 2 epsilon - Dmax) / 2`. It is not a property of the circuit but the domain of loss for which the guarantee holds. The loss of a period is measured as a line: what the cell loses by itself, plus a part proportional to the imposed conductance (measured at two leaks) | theorem (room condition) and measurement | 3 % on both parts of the loss |
| linear capacity | the largest reserve up to which doses were measured (nine sequences run 0.1 mV above the capacity for that purpose). The kernel uses the smaller of the two capacities | measurement | none |

Thresholds, in the capacitor coordinate, with what the scans saw on the way:

<!-- table thresholds -->
| Configuration | silent reads to learn (port 1, port 2) | own drift (mV per period) | Port 1: U_S (mV) | bracket (uV) | latency at U_S | Port 2: U_S (mV) | bracket (uV) | latency at U_S |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| tt27 | 4, 4 | 0.000 | -15.4500 | 14.9 | 0.9989 | -15.4482 | 15.5 | 0.9992 |
| ss27 | 4, 4 | 0.000 | -15.6803 | 12.4 | 0.9977 | -15.6727 | 15.1 | 0.9992 |
| ff27 | 4, 4 | 0.000 | -15.1913 | 14.3 | 0.9995 | -15.2033 | 14.8 | 0.9971 |
| sf27 | 4, 4 | 0.000 | -15.1308 | 15.6 | 0.9994 | -15.1309 | 15.4 | 0.9994 |
| fs27 | 4, 4 | 0.000 | -15.6873 | 15.5 | 0.9971 | -15.6874 | 15.5 | 0.9971 |
| tt-40 | 2, 2 | 0.000 | -12.6767 | 15.6 | 0.9979 | -12.6768 | 15.6 | 0.9978 |
| tt125 | 8, 8 | 0.193 | -19.6464 | 11.7 | 0.9992 | -19.6465 | 11.8 | 0.9992 |
| mm2001 | 5, 3 | 0.000 | -18.5106 | 16.3 | 0.9984 | -6.6382 | 12.1 | 0.9999 |
| mm2002 | 5, 5 | 0.000 | -18.7674 | 16.4 | 0.9980 | -23.6671 | 17.1 | 0.9987 |
<!-- end -->

Losses and doses, without noise:

<!-- table losses -->
| Configuration | own loss, port 1 (mV per period) | port 2 | added per 1e-11 S, port 1 (mV) | port 2 | dose, port 1 (mV) | port 2 |
|---|---:|---:|---:|---:|---:|---:|
| tt27 | 0.0001 | 0.0001 | 0.0587 | 0.0587 | 1.3495 to 1.3495 | 1.3495 to 1.3495 |
| ss27 | 0.0001 | 0.0001 | 0.0587 | 0.0587 | 1.3505 to 1.3505 | 1.3505 to 1.3505 |
| ff27 | 0.0001 | 0.0001 | 0.0587 | 0.0587 | 1.3491 to 1.3492 | 1.3491 to 1.3492 |
| sf27 | 0.0001 | 0.0001 | 0.0587 | 0.0587 | 1.3519 to 1.3520 | 1.3519 to 1.3520 |
| fs27 | 0.0001 | 0.0001 | 0.0587 | 0.0587 | 1.3574 to 1.3574 | 1.3574 to 1.3574 |
| tt-40 | 0.0001 | 0.0001 | 0.0587 | 0.0587 | 1.3472 to 1.3472 | 1.3472 to 1.3472 |
| tt125 | 0.1935 | 0.1935 | 0.0587 | 0.0587 | 1.3561 to 1.3561 | 1.3561 to 1.3561 |
| mm2001 | 0.0001 | 0.0001 | 0.0591 | 0.0574 | 1.3481 to 1.3481 | 1.3510 to 1.3510 |
| mm2002 | 0.0001 | 0.0001 | 0.0591 | 0.0599 | 1.3575 to 1.3575 | 1.3472 to 1.3473 |
<!-- end -->

The own loss at 125 C, 0.1935 mV per period, is the junction leakage that
stage J measured (0.193). Elsewhere it is below 0.0002 mV.

### Noise is not in the deterministic domain

With the calibrated noise sources on, a read at a given reserve does not
always give the same latency, and a dose is not always the same. Measured on
noisy supervised sequences, against the noiseless curves of the same
configuration:

<!-- table noise -->
| Configuration | noisy sequences | joint reads | sd of joint latency | largest shift | single reads | sd as reserve (mV) | largest (mV) | doses | sd of dose (mV) | largest (mV) |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| tt27 | 4 | 32 | 0.00085 | 0.00208 | 64 | 0.099 | 0.380 | 23 | 0.0080 | 0.0174 |
| ss27 | 4 | 32 | 0.00101 | 0.00253 | 64 | 0.104 | 0.252 | 24 | 0.0065 | 0.0181 |
| ff27 | 4 | 32 | 0.00093 | 0.00294 | 64 | 0.138 | 0.384 | 24 | 0.0088 | 0.0215 |
| sf27 | 4 | 32 | 0.00075 | 0.00223 | 64 | 0.102 | 0.231 | 16 | 0.0069 | 0.0188 |
| fs27 | 4 | 32 | 0.00081 | 0.00176 | 64 | 0.081 | 0.245 | 32 | 0.0070 | 0.0158 |
| tt-40 | 4 | 32 | 0.00113 | 0.00221 | 64 | 0.097 | 0.234 | 24 | 0.0082 | 0.0174 |
| tt125 | 4 | 32 | 0.00059 | 0.00206 | 64 | 0.090 | 0.242 | 72 | 0.0069 | 0.0147 |
| mm2001 | 4 | 32 | 0.00088 | 0.00169 | 64 | 0.087 | 0.309 | 24 | 0.0106 | 0.0296 |
| mm2002 | 4 | 32 | 0.00069 | 0.00137 | 64 | 0.087 | 0.288 | 16 | 0.0074 | 0.0154 |
<!-- end -->

A guarantee proved on the deterministic domain says nothing of a read whose
latency is 3 standard deviations early. The bounds are therefore given in
three versions, with a margin of `k` standard deviations of the measured
noise on the three places where noise enters (`S`: single read; `C`: joint
read; `Dmin`, `Dmax`: dose). `k = 0` is the deterministic guarantee alone.
The noise margin does not turn noise into a bounded error: under noise the
claim stays statistical, to be measured by repetitions.

**`k = 0`: deterministic bounds, no noise margin** (reserves, doses and losses in mV)

<!-- table design0 -->
| Port | limit of the sum (mV) | S | C | Dmin | Dmax | epsilon | room for 2H | H | own loss | largest imposed leak (x 1e-11 S) |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| tt27 port 1 | 4.634 | 0.0300 | 2.3168 | 1.3444 | 1.3545 | 0.0020 | 0.8914 | 0.4457 | 0.0001 | 7.37 |
| tt27 port 2 | 4.634 | 0.0300 | 2.3168 | 1.3444 | 1.3545 | 0.0020 | 0.8932 | 0.4466 | 0.0001 | 7.39 |
| ss27 port 1 | 4.728 | 0.0300 | 2.3640 | 1.3454 | 1.3555 | 0.0020 | 0.9285 | 0.4642 | 0.0001 | 7.68 |
| ss27 port 2 | 4.728 | 0.0300 | 2.3640 | 1.3454 | 1.3555 | 0.0020 | 0.9361 | 0.4680 | 0.0001 | 7.74 |
| ff27 port 1 | 4.545 | 0.0300 | 2.2725 | 1.3440 | 1.3542 | 0.0020 | 0.8590 | 0.4295 | 0.0001 | 7.10 |
| ff27 port 2 | 4.545 | 0.0300 | 2.2725 | 1.3440 | 1.3542 | 0.0020 | 0.8470 | 0.4235 | 0.0001 | 7.00 |
| sf27 port 1 | 4.559 | 0.0300 | 2.2793 | 1.3469 | 1.3570 | 0.0020 | 0.8295 | 0.4147 | 0.0001 | 6.86 |
| sf27 port 2 | 4.559 | 0.0300 | 2.2793 | 1.3469 | 1.3570 | 0.0020 | 0.8294 | 0.4147 | 0.0001 | 6.86 |
| fs27 port 1 | 4.627 | 0.0300 | 2.3135 | 1.3523 | 1.3625 | 0.0020 | 0.8892 | 0.4446 | 0.0001 | 7.35 |
| fs27 port 2 | 4.627 | 0.0300 | 2.3135 | 1.3523 | 1.3625 | 0.0020 | 0.8891 | 0.4445 | 0.0001 | 7.35 |
| tt-40 port 1 | 3.398 | 0.0300 | 1.6990 | 1.3421 | 1.3523 | 0.0020 | 0.2937 | 0.1468 | 0.0001 | 2.43 |
| tt-40 port 2 | 3.398 | 0.0300 | 1.6990 | 1.3421 | 1.3522 | 0.0020 | 0.2937 | 0.1468 | 0.0001 | 2.43 |
| tt125 port 1 | 6.732 | 0.0300 | 3.3661 | 1.3510 | 1.3612 | 0.0020 | 1.7829 | 0.8914 | 0.1935 | 11.44 |
| tt125 port 2 | 6.732 | 0.0300 | 3.3661 | 1.3510 | 1.3612 | 0.0020 | 1.7827 | 0.8913 | 0.1935 | 11.44 |
| mm2001 port 1 | 4.577 | 0.0300 | 2.2886 | 1.3430 | 1.3532 | 0.0020 | 0.8707 | 0.4353 | 0.0001 | 7.15 |
| mm2001 port 2 | 4.577 | 0.0300 | 2.2886 | 1.3460 | 1.3561 | 0.0020 | 0.8322 | 0.4161 | 0.0001 | 7.04 |
| mm2002 port 1 | 4.625 | 0.0300 | 2.3126 | 1.3524 | 1.3625 | 0.0020 | 0.8859 | 0.4429 | 0.0001 | 7.28 |
| mm2002 port 2 | 4.625 | 0.0300 | 2.3126 | 1.3422 | 1.3523 | 0.0020 | 0.9096 | 0.4548 | 0.0001 | 7.37 |
<!-- end -->

**`k = 2`**

<!-- table design2 -->
| Port | limit of the sum (mV) | S | C | Dmin | Dmax | epsilon | room for 2H | H | own loss | largest imposed leak (x 1e-11 S) |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| tt27 port 1 | 4.301 | 0.2286 | 2.1504 | 1.3284 | 1.3705 | 0.0020 | 0.5473 | 0.2736 | 0.0001 | 4.52 |
| tt27 port 2 | 4.301 | 0.2286 | 2.1504 | 1.3284 | 1.3705 | 0.0020 | 0.5473 | 0.2736 | 0.0001 | 4.52 |
| ss27 port 1 | 4.308 | 0.2375 | 2.1539 | 1.3324 | 1.3685 | 0.0020 | 0.5439 | 0.2719 | 0.0001 | 4.50 |
| ss27 port 2 | 4.308 | 0.2375 | 2.1539 | 1.3324 | 1.3685 | 0.0020 | 0.5439 | 0.2719 | 0.0001 | 4.50 |
| ff27 port 1 | 4.184 | 0.3054 | 2.0917 | 1.3264 | 1.3719 | 0.0020 | 0.4104 | 0.2052 | 0.0001 | 3.39 |
| ff27 port 2 | 4.184 | 0.3054 | 2.0917 | 1.3264 | 1.3719 | 0.0020 | 0.4104 | 0.2052 | 0.0001 | 3.39 |
| sf27 port 1 | 4.267 | 0.2343 | 2.1335 | 1.3332 | 1.3707 | 0.0020 | 0.5245 | 0.2622 | 0.0001 | 4.34 |
| sf27 port 2 | 4.267 | 0.2343 | 2.1335 | 1.3332 | 1.3707 | 0.0020 | 0.5245 | 0.2622 | 0.0001 | 4.34 |
| fs27 port 1 | 4.322 | 0.1930 | 2.1611 | 1.3384 | 1.3764 | 0.0020 | 0.5877 | 0.2938 | 0.0001 | 4.86 |
| fs27 port 2 | 4.322 | 0.1930 | 2.1611 | 1.3384 | 1.3764 | 0.0020 | 0.5877 | 0.2938 | 0.0001 | 4.86 |
| tt-40 port 1 | 3.106 | 0.2246 | 1.5530 | 1.3257 | 1.3687 | 0.0020 | -0.0443 | none | 0.0001 | none |
| tt-40 port 2 | 3.106 | 0.2246 | 1.5530 | 1.3257 | 1.3687 | 0.0020 | -0.0443 | none | 0.0001 | none |
| tt125 port 1 | 6.443 | 0.2107 | 3.2213 | 1.3373 | 1.3749 | 0.0020 | 1.5885 | 0.7942 | 0.1935 | 9.84 |
| tt125 port 2 | 6.443 | 0.2107 | 3.2213 | 1.3373 | 1.3749 | 0.0020 | 1.5883 | 0.7941 | 0.1935 | 9.84 |
| mm2001 port 1 | 4.225 | 0.2035 | 2.1122 | 1.3218 | 1.3744 | 0.0020 | 0.5303 | 0.2651 | 0.0001 | 4.36 |
| mm2001 port 2 | 4.225 | 0.2035 | 2.1122 | 1.3247 | 1.3773 | 0.0020 | 0.5274 | 0.2637 | 0.0001 | 4.46 |
| mm2002 port 1 | 4.338 | 0.2044 | 2.1689 | 1.3376 | 1.3773 | 0.0020 | 0.5832 | 0.2916 | 0.0001 | 4.79 |
| mm2002 port 2 | 4.338 | 0.2044 | 2.1689 | 1.3273 | 1.3671 | 0.0020 | 0.5934 | 0.2967 | 0.0001 | 4.81 |
<!-- end -->

**`k = 3`**

<!-- table design3 -->
| Port | limit of the sum (mV) | S | C | Dmin | Dmax | epsilon | room for 2H | H | own loss | largest imposed leak (x 1e-11 S) |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| tt27 port 1 | 4.126 | 0.3278 | 2.0628 | 1.3204 | 1.3785 | 0.0020 | 0.3525 | 0.1762 | 0.0001 | 2.91 |
| tt27 port 2 | 4.126 | 0.3278 | 2.0628 | 1.3204 | 1.3785 | 0.0020 | 0.3525 | 0.1762 | 0.0001 | 2.91 |
| ss27 port 1 | 4.097 | 0.3412 | 2.0484 | 1.3259 | 1.3750 | 0.0020 | 0.3282 | 0.1641 | 0.0001 | 2.71 |
| ss27 port 2 | 4.097 | 0.3412 | 2.0484 | 1.3259 | 1.3750 | 0.0020 | 0.3282 | 0.1641 | 0.0001 | 2.71 |
| ff27 port 1 | 3.993 | 0.4430 | 1.9964 | 1.3175 | 1.3807 | 0.0020 | 0.1687 | 0.0843 | 0.0001 | 1.39 |
| ff27 port 2 | 3.993 | 0.4430 | 1.9964 | 1.3175 | 1.3807 | 0.0020 | 0.1687 | 0.0843 | 0.0001 | 1.39 |
| sf27 port 1 | 4.126 | 0.3364 | 2.0631 | 1.3263 | 1.3776 | 0.0020 | 0.3451 | 0.1725 | 0.0001 | 2.85 |
| sf27 port 2 | 4.126 | 0.3364 | 2.0631 | 1.3263 | 1.3776 | 0.0020 | 0.3451 | 0.1725 | 0.0001 | 2.85 |
| fs27 port 1 | 4.159 | 0.2744 | 2.0793 | 1.3315 | 1.3833 | 0.0020 | 0.4176 | 0.2088 | 0.0001 | 3.45 |
| fs27 port 2 | 4.159 | 0.2744 | 2.0793 | 1.3315 | 1.3833 | 0.0020 | 0.4176 | 0.2088 | 0.0001 | 3.45 |
| tt-40 port 1 | 2.925 | 0.3219 | 1.4623 | 1.3175 | 1.3769 | 0.0020 | -0.2405 | none | 0.0001 | none |
| tt-40 port 2 | 2.925 | 0.3219 | 1.4623 | 1.3175 | 1.3769 | 0.0020 | -0.2405 | none | 0.0001 | none |
| tt125 port 1 | 6.244 | 0.3010 | 3.1218 | 1.3304 | 1.3818 | 0.0020 | 1.4350 | 0.7175 | 0.1935 | 8.57 |
| tt125 port 2 | 6.244 | 0.3010 | 3.1218 | 1.3304 | 1.3818 | 0.0020 | 1.4350 | 0.7175 | 0.1935 | 8.57 |
| mm2001 port 1 | 4.034 | 0.2902 | 2.0172 | 1.3112 | 1.3850 | 0.0020 | 0.3380 | 0.1690 | 0.0001 | 2.78 |
| mm2001 port 2 | 4.034 | 0.2902 | 2.0172 | 1.3141 | 1.3879 | 0.0020 | 0.3351 | 0.1675 | 0.0001 | 2.83 |
| mm2002 port 1 | 4.195 | 0.2915 | 2.0975 | 1.3302 | 1.3847 | 0.0020 | 0.4173 | 0.2086 | 0.0001 | 3.43 |
| mm2002 port 2 | 4.195 | 0.2915 | 2.0975 | 1.3199 | 1.3745 | 0.0020 | 0.4275 | 0.2137 | 0.0001 | 3.46 |
<!-- end -->

The last column is the largest constant imposed leak, in units of the
reference one (1e-11 S, that is 1e11 ohm), such that the own loss of the cell
plus the loss of that leak stays within `H`.

What the three versions allow, as the largest constant imposed leak in units
of the reference one (the smaller of the two ports):

| Version | corners at 27 C and mismatch instances | 125 C | -40 C |
|---|---|---|---|
| `k = 0` | 6.9 to 7.7 | 11.4 | 2.4 |
| `k = 2` | 3.4 to 4.9 | 9.8 | no bounds |
| `k = 3` | 1.4 to 3.5 | 8.6 | no bounds |

The room is small because one dose is large: at 27 C the capacity of a port
is 2.0 to 2.4 mV and a dose is 1.35 mV. What is left, 0.7 to 0.9 mV, is
shared between the floor `S`, twice the loss `H` and the margins. Each 0.001
of latency given up at the lower edge of the joint window costs about 0.2 mV
of the sum, 0.1 mV of capacity per port, 0.05 mV of `H` — a little less than
one reference leak. The trade is between three things only: the width of the
joint window, the noise margin, and the leak that can be withstood. With
`k = 3` the weakest configuration is the FF corner, which holds 1.4 times the
reference leak: its single read is the noisiest measured (0.14 mV).

At 125 C the cell has more room (the joint latency falls more slowly with the
reserve: the capacity of a port is 3.1 to 3.4 mV), and it needs it: by itself
it loses 0.19 mV per period, a quarter of `H` at `k = 3`.

At -40 C the joint latency falls faster with the reserve: the limit of the
sum is 3.4 mV, the capacity of a port 1.70 mV, and a dose takes all of it but
0.35 mV. Without noise margin the bounds exist and hold 2.4 times the
reference leak; with a margin of 2 standard deviations there are no bounds:
the versions `k = 2` and `k = 3` of `tt-40` are not well-formed.

These bounds are in [`BOUNDS_JUNCTION.json`](BOUNDS_JUNCTION.json), pushed
at 22:56:33 UTC (commit `b12f7a0`), four seconds before the confirmation batch
was started.

### Confirmation

After the bounds were fixed, supervised sequences of 24 services were run
with them: for each configuration and each version that has bounds, without
noise at the reference leak and at the largest leak of the version, and with
noise at the largest leak (twice; for `k = 0`, only at -40 C, where no other
version has bounds). These sequences set no bound. In the table, `design k`
is the version with a margin of `k` standard deviations.

<!-- table confirmation -->
| Version | sequences | services | correct | refusals | writes not as commanded | FIRE outside a read | enclosures broken | smallest joint latency | largest single latency | largest observer error (uV) |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| design 0, no noise | 18 | 432 | 432 | 0 | 0 | 0 | 0 | 0.2516 | 0.9415 | 0.204 |
| design 0, noise | 2 | 48 | 48 | 0 | 0 | 0 | 0 | 0.2555 | 0.9707 | 0.096 |
| design 2, no noise | 16 | 384 | 384 | 0 | 0 | 0 | 0 | 0.2525 | 0.9086 | 0.233 |
| design 2, noise | 16 | 384 | 384 | 0 | 0 | 0 | 0 | 0.2531 | 0.9416 | 0.188 |
| design 3, no noise | 16 | 384 | 384 | 0 | 0 | 0 | 0 | 0.2536 | 0.9076 | 0.200 |
| design 3, noise | 16 | 384 | 384 | 0 | 0 | 0 | 0 | 0.2530 | 0.9374 | 0.171 |
<!-- end -->

All 84 sequences: 2016 services, 2016 correct. No refusal; every clock-only
cycle wrote one dose on the port it was commanded on and none elsewhere; no
FIRE outside a read; every observation stayed inside the enclosure the kernel
had computed; every read happened with both reserves between `S` and `C`.

For the 50 sequences without noise this is the deterministic guarantee,
observed on the nine configurations. For the 34 noisy ones (816 services) it
is a count, not a rate, and the services of one sequence are not independent:
34 sequences without a failed service allow, at 95 %, up to 8.4 % of such
sequences to have one. The confirmation does not separate the versions: none
of them failed, the version without margin included (two noisy sequences, at
-40 C only).

The batch was cut once. From about 23:27 to 23:31 UTC the disk of the
container was full (the raw waveforms of the two qualifications). Of the 84
sequences, 31 had ended; 4 were running and were cut (`confn2-mm2002-0`,
`confn0-tt-40-0`, `confn0-tt-40-1`, `conf3-tt27-base`: listed at the end of
this page, with what they left); 49 could not start. Room was made without
deleting any waveform (those of finished runs are stored through gzip, each
archive checked against the recorded SHA-256), and the 53 sequences were run
again under their name followed by `-again`. No sequence that ended was run
again, and none was discarded.

### What is not guaranteed

- Anything outside the nine configurations, or outside one read per 440 us
  preceded by its maintenance slot.
- A loss above `H`: an imposed leak above the largest one of the table, a leak
  that is not a conductance on the summing node, or a junction leakage larger
  than that of the areas used here. After a refusal, nothing.
- Under noise: the bounds have margins, not proofs. A noisy read can be
  incorrect at any reserve with a small probability; only repetitions measure it.
- -40 C under noise: there are no bounds with a noise margin. With this dose
  and the P7 window, the supervisor cannot be given a margin there.
- Temperatures between or beyond the three simulated ones. The own loss grows
  fast with temperature; 125 C is the hottest point measured.
- The junction areas are those of devices drawn alone, and there is no wire
  capacitance: this is not a post-layout result.
- The window of the joint read is P7, not the window of the ideal model.
- The observer is ideal: it reads two node voltages of the simulation. No
  measuring circuit is designed or claimed.
- No energy statement of any kind.

## 5. The launch kit

[`launchkit/`](launchkit/README.md) is a second version of the kit of PR 123;
the first is left as it was. What changed, each item with its test:

- **Python 3.12.3** (Ubuntu 24.04 package `python3.12-minimal`
  `3.12.3-1ubuntu0.17`) and **numpy 2.3.5**, both pinned by hash. The 23
  diagnostics without noise of PR 123 replayed under this interpreter give
  the same decks, the same waveforms and the same analysis results, byte for
  byte ([`PYTHON_IDENTITY.json`](PYTHON_IDENTITY.json)).
- **The launcher sets `SPICE_SCRIPTS` itself**, to the folder of the committed
  [`runtime/spinit`](runtime/spinit) (`set num_threads=1`), frozen by hash; a
  registered launch refuses a caller that sets it.
- **Noise fingerprint** of every run, and a command that lists the runs that
  share one. The noise cannot be replayed; this is stated. Measured here: two
  runs that get the same process number draw the same noise even on different
  corners, and two containers number their processes alike — so each run on a
  corner without mismatch must receive its own `setseed`, which changes the
  noise and nothing else ([`fingerprint_check.py`](fingerprint_check.py)).
- **Round-robin manifest**: any prefix of a machine's list is balanced over
  the scenarios.
- **Truncated campaign** and **shared fingerprints**: the rules that
  PREDICTION.md must fix are written out in the kit's README.
- **Resume rule**: after a container restart, the runs never started
  proceed; a run that had started is recorded as lost and never run again.
  Refused when the container did not restart.
- **Executor**: a Claude Code cloud session on behalf of the owner, on two
  cloud containers whose inventories are recorded. The sentence "the owner
  alone, on the owner's machines" of PR 123 is corrected in its two README
  files; no other file of PR 122 or PR 123 is touched (the CI checks it).

The end-to-end test of the kit ([`launchkit/SYNTHETIC_TEST.json`](launchkit/SYNTHETIC_TEST.json))
uses an RC circuit and a local Git remote.

## 6. Budget: at most 4 h for the two machines together

Measured on the noisy confirmation sequences, four at a time on a
four-processor container — the conditions of the campaign:
a simulated slot costs at most 4.52 s (4.12 s on average), 1.61 times what it
costs without noise; the longest preparation took 13 slots (at 125 C). With a
time limit of 1.5 times the estimate of a run:

<!-- table budget -->
| Services per run | estimate (s) | time limit (s) | runs per machine | runs | services | bound per machine | expected per machine |
|---|---:|---:|---:|---:|---:|---:|---:|
| 12 | 172 | 258 | 103 | 206 | 2472 | 1.99 h | 1.23 h |
| 18 | 226 | 339 | 78 | 156 | 2808 | 1.99 h | 1.22 h |
| 24 | 280 | 420 | 62 | 124 | 2976 | 1.97 h | 1.21 h |
| 36 | 389 | 584 | 44 | 88 | 3168 | 1.98 h | 1.19 h |
<!-- end -->

"Bound" is what the launcher enforces (time limits included); "expected" is
what the measured times predict. Setting up the containers, pushing and
collecting the evidence are outside these times. The scope is to be chosen in
this table before PREDICTION.md, and not changed after.

## The first qualification, without junction areas

Kept as it was when the result of stage J was received; nothing of it is a
result on the cell with junctions. Its bounds are in
[`BOUNDS.json`](BOUNDS.json), which is not edited. They differ from the bounds
above mostly at 125 C, where they count no own loss (0.059 mV per period at
the reference leak instead of 0.25). In that file the bounds of `tt-40` with
a noise margin of 2 and of 3 standard deviations are not well-formed, as here.

`BOUNDS.json` was committed 30 s after its confirmation batch was started and
three minutes before the first sequence of the batch ended (its commit message
says "before the first confirmation sequence was run", which is not exact).
That batch of 100 sequences was stopped when stage J was received: 65 had
been run, 35 never started. What the 65 gave, on netlists without areas:

<!-- table schematic -->
| Version | sequences | services | correct | refusals | writes not as commanded | FIRE outside a read | enclosures broken | smallest joint latency | largest single latency | largest observer error (uV) |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| design 0, noise | 18 | 432 | 432 | 0 | 0 | 0 | 0 | 0.2526 | 0.9456 | 0.179 |
| design 2, noise | 16 | 384 | 384 | 0 | 0 | 0 | 0 | 0.2536 | 0.9090 | 0.183 |
| design 3, no noise | 15 | 360 | 360 | 0 | 0 | 0 | 0 | 0.2533 | 0.9107 | 0.189 |
| design 3, noise | 16 | 384 | 384 | 0 | 0 | 0 | 0 | 0.2545 | 0.9312 | 0.174 |
<!-- end -->

### The simulator aborted on some noisy runs, and why

<!-- table aborted -->
| Run | netlist | ammeter | noise | message of the simulator |
|---|---:|---:|---:|---:|
| nz-fs27-0 | without areas | yes | yes | doAnalyses: TRAN:  Timestep too small; time = 3.1e-06, timestep = 2.5e-19: trouble with node "v.x1.vdose#branch" |
| nz-sf27-0 | without areas | yes | yes | doAnalyses: TRAN:  Timestep too small; time = 3.1e-06, timestep = 2.5e-19: trouble with node "v.x2.vdose#branch" |
| nz-sf27-1 | without areas | yes | yes | doAnalyses: TRAN:  Timestep too small; time = 3.1e-06, timestep = 2.5e-19: trouble with node "v.x1.vdose#branch" |
| nz-sf27-2 | without areas | yes | yes | doAnalyses: TRAN:  Timestep too small; time = 3.1e-06, timestep = 2.5e-19: trouble with node "v.x1.vdose#branch" |
| nz-sf27-3 | without areas | yes | yes | doAnalyses: TRAN:  Timestep too small; time = 3.1e-06, timestep = 2.5e-19: trouble with node "v.x2.vdose#branch" |
| conf3-tt27-base | with areas | no | no | none: the disk of the container was full from about 23:27 to 23:31 UTC |
| confn0-tt-40-0 | with areas | no | yes | none: the disk of the container was full from about 23:27 to 23:31 UTC |
| confn0-tt-40-1 | with areas | no | yes | none: the disk of the container was full from about 23:27 to 23:31 UTC |
| confn2-mm2002-0 | with areas | no | yes | none: the disk of the container was full from about 23:27 to 23:31 UTC |
<!-- end -->

The first decks carried a 0 V source in series with the write switch of each
port, to measure the write current, as PR 122 did. With noise on, at the SF
corner, the solver gives up on the current of that source ("timestep too
small"): 12 short sessions out of 12, against none out of 3 without the
source, with 1 ohm in series, or with a looser current tolerance. No bound
uses that current. The source was removed: `sim.deck` no longer inserts it
unless asked. The aborted runs are kept and listed. Twelve sessions of the
first qualification were run again without the source: the same FIRE and the
same writes in every slot, capacitor voltages within 0.6 uV. No run of the
qualification with junction areas carries the source. The four runs of
that qualification in the table are those the full disk cut (see the
confirmation above); they carry no message of the simulator.

## Evidence

The raw waveforms of the two qualifications are not in Git, as in PR 123.
Every deck, simulator log, record and waveform is identified by its SHA-256
in the two JSON files (`evidence_files`), and `closure.py DATA --check`
recomputes every published number from them; before using a run it checks
that its waveform and deck are the recorded ones and that the deck is the one
the committed tools build. For the registered campaign the rule is different
and stays the owner's: the raw evidence is committed unchanged with its
SHA-256 list.

## Reproduce

```sh
python -B research/sky130-supervisor-closure/verify.py
```

checks, without any waveform, that the published bounds follow from the
published measurements and satisfy the conditions of the kernel, that the
files pushed before the confirmations hold the bounds that were confirmed,
that the tables of this page are those numbers, and that the kit records
belong to the committed files. CI runs it with the tests of the kernel and of
the kit.

The measurements themselves: [`qualify.py`](qualify.py) (thresholds, maps),
[`supervise.py`](supervise.py) (supervised sequences),
[`fingerprint_check.py`](fingerprint_check.py), then
`closure.py DATA`, `budget.py`, `tables.py`.

## What comes next, and not before the owner approves this step

PREDICTION.md alone, pushed before any implementation: scenarios (with the
leakage jump, which nothing here simulated), the version of the bounds, the
configurations, the machine split, every `setseed`, the rules for a truncated
campaign and for shared fingerprints, the budget. Then the implementation
and the frozen kit, all CI green on that exact head, and an independent
review of the preregistration.
