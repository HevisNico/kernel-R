# Layout 2.2: diagnostic of C1, the rest charge before the first read

**Exploratory. Not a campaign, nothing preregistered, no verdict, no new
layout.** It reads [`../C_REPORT.md`](../C_REPORT.md), which is not
changed: C1 fails, three ports are refused for their rest state.

```sh
cd research/sky130-layout/v2.2/diagnostic
python3 -I rest.py table     # what the committed results already say: no simulation
python3 -I rest.py runs      # the exploratory simulations: about 35 minutes on four cores
python3 -I rest.py report    # the tables below
```

What was run: **45 exploratory simulations.** 44 are noisy test runs of
the campaign (`cert_run.py`, unchanged, the noise of stage C: identifier
700000 + the seed) with something taken out; one is the read of the
nominal cell without noise. Only the first row of each is read. Outputs
in `build/`, not committed; hashes in [`SHA256SUMS`](SHA256SUMS).

The rest charge is `q = 0.1 + (1.25 V − vq) / 0.5 V`, read 1 ps before
the pulse. The band of rule A1 is 0.1 to 0.1001. **The tables are in
billionths of a level unit above 0.1: one is 0.5 nV on `vq`. Negative
is refused.**

## 1. Which side, and by how much

**The lower side, on the first read only.** `vq` is above its rest
reference `vr0` by nanovolts:

| Port refused | Rest charge before its first read | Below 0.1 by | `vq` above `vr0` by |
|---|---|---|---|
| `t6051` port 1 | 0.0999998190 | 181.0 | 90.5 nV |
| `t6082` port 1 | 0.0999999873 | 12.7 | 6.4 nV |
| `t6031` port 1 | 0.0999999967 | 3.3 | 1.7 nV |

On the upper side nothing is near: the largest rest charge of the eight
noisy runs is 0.1000416, with the band ending at 0.1001. The overshoot
of the first layout (0.10098) is gone.

## 2. Why port 1 only

**Because port 1 has the first read of the run, not because it is
port 1.** A noisy test run pulses port 1 ten times, then port 2 ten
times, on a fresh cell.

| | Rest charge above 0.1, the eight noisy runs of stage C |
|---|---|
| Before the first read of the run (port 1, row 0) | −181 to +434 |
| Before every later read of port 1 | +31 400 to +41 600 |
| Before the first read of port 2 (row 10) | +37 500 to +41 000 |

After one pulse the cell rests 17 µV below `vr0`, two hundred times the
spread of the first read. A fresh cell rests 21 nV below it, and the
noise is larger than that.

## 3. What drives it

Each line is the same noisy run with one thing changed.

| Cell | Stage C | No noise on the FIRE reference | Only the noise of the FIRE reference | No capacitance (areas alone) | Without `vq`–`dq` (0.35 fF) | Without `vq` to node 0, `vdd`, `vr0`, `vpre` (48.4 fF) | Without `vq` to the FIRE comparator (3.6 fF) | Schematic, same noise |
|---|---|---|---|---|---|---|---|---|
| `t6051` | **−181.0** | +38.4 | −177.0 | −173.0 | −175.4 | −183.1 | −175.6 | +109.6 |
| `t6082` | **−12.7** | −11.0 | +41.0 | +41.1 | +38.0 | −13.3 | −12.6 | +322.8 |
| `t6031` | **−3.3** | +32.6 | +6.8 | +7.7 | +6.2 | −3.7 | −2.3 | +289.7 |
| `t6065` | +434.3 | +41.7 | +435.3 | +427.2 | not run | not run | +424.9 | +710.3 |
| `t6074` | +72.1 | not run | not run | +119.7 | +117.2 | +72.3 | not run | +401.9 |
| `t6002` | +43.7 | not run | not run | +36.3 | not run | not run | not run | +317.5 |
| `t6003` | +61.0 | not run | not run | +52.0 | not run | not run | not run | +336.5 |
| `t6030` | +148.1 | not run | not run | +163.0 | not run | not run | not run | +445.1 |

Without noise the rest charge before the first read is **+42.6 for
every cell**: the nominal cell, the 8 calibration cells and the 8 cells,
on layout 2.2 and on the first layout alike, and with the areas alone.
On the schematic it is +324.0 for every cell.

Three things add up.

**a. The source and drain areas take most of the margin, in every
layout.** A fresh cell without noise rests 162 nV below `vr0` on the
schematic and 21 nV below it once the areas are in the netlist: 281 of
the 324 are gone. The same noise on the schematic gives the same cell
281 to 285 more, for the eight cells. It is the areas, not the
capacitances: the first layout and layout 2.2 share the file of areas
and give the same +42.6, and so does the netlist with no capacitance.
By arithmetic on the ideal leak resistor (8 MΩ) the current that leaves
`vq` at rest goes from 20 fA to 2.7 fA. Which junction was not looked
into.

**b. The noise of the FIRE reference moves `vq` by more than what is
left.** With that source turned down a million times the first read
comes back to +33 to +42 on three of the four cells run (`t6082` keeps
what point c describes). With the three other sources turned down
instead, the first read is that of the netlist with no capacitance,
within 8. No
extracted capacitance carries it: between `vq` and `vrefmn` Magic
extracts nothing on layout 2.2, and the netlist with no capacitance at
all shows the same excursion (−216 for `t6051`, +385 for `t6065`). It
goes through the input devices of the comparator themselves, as on the
schematic. Over the eight cells this part is −216 to +385, 159 in
standard deviation, against a margin of 42.6.

**c. One extracted capacitance adds to it: `vq`–`dq`, 0.18 fF in each
port.** It is the only capacitance on `vq` that moves the first read:
−54 for `t6082`, −48 for `t6074`, −11 for `t6031`, −8 for `t6051`.
What it carries is not the noise of the FIRE reference (for `t6082` the
−54 are there without that source and gone with it alone), so it is one
of the three other sources; `dq` is the node where the noise current of
the mirror is injected. The 48 fF from `vq` to the rails and the 3.6 fF
to the nodes inside the comparator change the first read by less than 5.

For the three refused ports:

| Port | Margin without noise | Noise of the FIRE reference | `vq`–`dq` and the rest | Rest charge |
|---|---|---|---|---|
| `t6051` port 1 | +42.6 | −215.6 | −8.0 | −181.0 |
| `t6082` port 1 | +42.6 | −1.5 | −53.8 | −12.7 |
| `t6031` port 1 | +42.6 | −34.9 | −11.0 | −3.3 |

- `t6051` is refused by the reference noise alone; no capacitance
  matters to it. With another noise draw it was already refused on the
  schematic, in the committed campaign (−9.8).
- `t6082` is refused by `vq`–`dq`: without those 0.35 fF it passes.
- `t6031` needs both.

## 4. The mismatch parameters

**None could be found, and the results say why.** Without noise the
rest charge before the first read is the same to the tenth of a
billionth for 17 cells with 17 different draws of mismatch: no
mismatch parameter moves it. Under noise it differs from cell to cell,
but each cell has its own noise draw: with one draw per cell the cell
and the draw cannot be told apart. What can be said is that the three
refused ports are not three weak cells: they are three first reads out
of eight, where the noise happened to push `vq` up.

On the schematic the same thing is rare and not absent: 2 of the 100
noisy test runs of the committed campaign have their first rest charge
below 0.1.

## What this diagnostic does not show

- One noise draw per cell: no rate. With a margin of 42.6 and an
  excursion of 159 in standard deviation, a first read below 0.1 is not
  an accident of these eight cells; how often it happens was not
  measured.
- The two runs with a noise source turned down need the noise file of
  the mirror changed, and its hash in the manifest of the mirror with
  it; `cert_run.py` is unchanged. Which of the three other sources
  `vq`–`dq` carries was not separated.
- Why the areas lower the current that leaves `vq` was not looked into.
- Taking a capacitance out of a list is not a layout.
