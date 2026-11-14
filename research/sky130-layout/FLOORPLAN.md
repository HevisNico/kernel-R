# Floorplan and area estimate

Phase 0, item 3. **No cell was laid out.** The figures below are the
footprints of the parts, each drawn alone by the device generator of
Magic, added up with two stated assumptions. They are estimates.

```sh
cd research/sky130-layout/footprints && sh run.sh       # Magic generator: footprints and DRC counts
cd ../checks && sh run.sh                               # ngspice: capacitance of the MIM model (step 1)
```

Outputs are in `build/`, not committed. Their hashes are in
[`footprints/SHA256SUMS`](footprints/SHA256SUMS) and
[`checks/SHA256SUMS`](checks/SHA256SUMS).

## The capacitor figure, checked

The figure to check: 30 pF is about 15 000 µm² of MIM capacitor at about
2 fF/µm².

**The density holds** (simulation of the pinned model, typical corner).
An AC analysis of `sky130_fd_pr__cap_mim_m3_1` in ngspice gives:

| Plate drawn | Capacitance | Per drawn µm² |
|---|---|---|
| 30 µm × 30 µm | 1.8198 pF | 2.022 fF |
| 14.14 µm × 14.14 µm | 0.4092 pF | 2.047 fF |
| 10 µm × 10 µm | 0.2066 pF | 2.066 fF |

`cap_mim_m3_2`, the capacitor one metal level higher, gives the same
1.8198 pF for 30 µm × 30 µm. At 2.022 fF/µm², 30 pF is **14 840 µm² of
plate**. The figure of 15 000 µm² is right for the plate.

**The footprint is larger than the plate.** The generator accepts plates
up to 30 µm × 30 µm, so 30 pF is an array, and each plate needs its
bottom-plate margin and its spacing.

| Array drawn by the generator | Capacitance | Footprint | Per µm² of footprint | DRC errors |
|---|---|---|---|---|
| One plate 30 × 30 | 1.82 pF | 32.16 × 30.40 = 978 µm² | 1.86 fF | 0 |
| 4 × 4 plates of 30 × 30 | 29.1 pF | 138.63 × 128.00 = 17 745 µm² | **1.64 fF** | 0 |
| 9 × 9 plates of 14.14 × 14.14 | 33.1 pF | 173.34 × 145.26 = 25 179 µm² | **1.32 fF** | 0 |

So one feedback capacitor of 30 pF takes:

- about **18 300 µm²** as large plates (1.64 fF/µm²), 22% more than the
  figure to check;
- about **23 300 µm²** as 75 unit plates of 0.4 pF, matched to the unit
  plate of the sensor capacitor (311 µm² per unit, 1.32 fF/µm²).

A cell has two of them.

**Stacking the two MIM types would halve this. It was not achieved.**
The generator has a `stack` option; with `stack 2` it drew the same
single capacitor. Drawing a `cap_mim_m3_1` and a `cap_mim_m3_2` on top
of each other is DRC clean (33.60 × 30.81 µm), but the extraction shows
the lower capacitor with both plates on one net: shorted. A stacked
capacitor needs its plates and vias drawn by hand. Its area is not
counted on below.

## Footprints of the other parts

Each transistor is drawn alone, with the default options of the
generator, which include a guard ring. A width above 10 µm is split into
fingers.

| Part | Count | Footprint, each | Total |
|---|---|---|---|
| Gain mirror device, 40 / 2.5 in 4 fingers | 4 | 12.83 × 12.10 = 155 µm² | 621 µm² |
| Other transistors of the op-amps, comparators, mirrors and switches | 66 | 6.5 to 110 µm² | 1 892 µm² |
| **The 70 transistors outside the logic** | | | **2 513 µm²** |
| Logic: 162 transistors in 53 gates | | 12.1 µm² per pair of devices, the inverter of [`TOOLCHAIN.md`](TOOLCHAIN.md) | about 980 µm² |
| Resistor of 8 MΩ: 20 strips of 70 µm of the 2 kΩ per square poly, 0.35 µm wide | 1 | 17.78 × 75.82 | 1 348 µm² |
| Resistors of 100 kΩ | 5 | 2.01 × 23.32 | 234 µm² |
| Resistors of 4 kΩ | 2 | 2.01 × 10.22 | 41 µm² |
| **Transistors and resistors, drawn alone** | | | **about 5 100 µm²** |

The drawn gate area is 1 159 µm² ([`INVENTORY.md`](INVENTORY.md)): the
guard rings, contacts and well spacings multiply it by a little over two
for the 70 transistors outside the logic (1 138 µm² of gate, 2 513 µm²
drawn).

The figure for the logic is an upper one: it gives every pair of devices
the two guard rings of the inverter drawn in phase 0. Rows of gates that
share wells and taps are smaller. The logic is 2% of the cell either
way.

The generator's default devices are not all DRC clean when drawn alone:
the 1 / 0.15 and 2 / 0.15 switches show metal-1 minimum-area errors on
their contact pads, and a single resistor shows an implant-width error.
Both are expected to go away once the devices are wired or arrayed. It
was not checked.

## Floorplan

Not drawn. The proposed arrangement, for one cell of two ports:

```text
 ┌──────────────────────────┬──────────────────────────┐
 │  C_f port 1, 30 pF       │  C_f port 2, 30 pF       │
 │  with its C_s unit       │  with its C_s unit       │
 │  (MIM array)             │  (MIM array)             │
 ├───────────┬──────────────┴──────────────┬───────────┤
 │ port 1:   │ shared: C_q 5 pF, R_leak,   │ port 2:   │
 │ mirror,   │ FIRE comparator,            │ mirror,   │
 │ op-amp,   │ protection latch, 2 pF      │ op-amp,   │
 │ sensor,   │ delay                       │ sensor,   │
 │ window    │                             │ window    │
 │ comparator│                             │ comparator│
 │ logic     │                             │ logic     │
 └───────────┴─────────────────────────────┴───────────┘
   references, bias currents, clocks and pulses enter as pins
```

- The two ports are mirror images, with the shared blocks between them.
- Each integrator sits against its feedback capacitor, so that the
  summing node is short.
- The logic of a port is one row, away from the summing node and from
  the gate of the mirror.
- The top plate of each capacitor goes to the sensitive node: `sum` for
  `cf`, `vs` for `cs`, `vq` for `cq`. The bottom plate, which carries
  the parasitic to the substrate, goes to the driven or grounded side.

## Honest total area

Two assumptions carry the total:

- **Wiring and spacing double the area of the transistors and
  resistors**: 5 100 µm² becomes about 10 200 µm². This factor is a rule
  of thumb for a small analog block, not a measurement.
- **Transistors are placed beside the capacitors, not under them.** A
  MIM capacitor sits on metals 3 to 5 and transistors can go below it,
  wired on the lower metals. That would save the 10 200 µm², and put
  the summing node and the mirror gates under a large plate. The
  estimate does not count on it.

| | Large plates | Unit plates for `cf` and `cs` |
|---|---|---|
| Two feedback capacitors, 60 pF | 36 600 µm² | 46 600 µm² |
| The other capacitors, 11.6 pF | 7 100 µm² | 7 200 µm² |
| Transistors and resistors, with wiring | 10 200 µm² | 10 200 µm² |
| **One cell of two ports** | **about 54 000 µm²** | **about 64 000 µm²** |
| | 0.054 mm², 232 µm × 232 µm if square | 0.064 mm², 253 µm × 253 µm |
| Share of the two feedback capacitors | 68% | 73% |
| Per port | 27 000 µm² | 32 000 µm² |
| Ports per mm² | 37 | 31 |

**The honest figure is 0.05 to 0.065 mm² for one cell of two ports, on a
single MIM layer.** That is about 30 to 40 ports per mm². The feedback
capacitors are about 70% of it. The unit-plate option is the one that
controls the ratio `C_s / C_f`, which is the dose.

Not in this figure, and all of it needed around a cell on a chip:

- the eight reference voltages, the five 10 µA bias sinks and the
  8.2 nA references;
- the detection of the pulse and the three clocks it must produce;
- the preset of the integrator;
- supply decoupling, pads and their protection;
- metal fill, and whatever the antenna and density rules add.

## What the figure says about density

A port is one stored gain. At 27 000 to 32 000 µm² per port this cell is
not a memory element of a dense array. The area is set by the 30 pF
feedback capacitor, and that value is set by the design choice of a dose
of 1.33 mV from a 400 fF sensor capacitor and a window of 100 mV
([`../circuit/DESIGN.md`](../circuit/DESIGN.md)). Changing it changes
the circuit, which is outside the layout bet: phase 1 lays out the
circuit as it was simulated.
