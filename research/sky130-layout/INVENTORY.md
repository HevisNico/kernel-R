# Inventory of one R cell

Phase 0, item 2. Read from [`../circuit/cell.spice`](../circuit/cell.spice),
[`../circuit/blocks.spice`](../circuit/blocks.spice) and
[`../circuit/DESIGN.md`](../circuit/DESIGN.md). Nothing here is a
simulation: it is a reading of the netlists.

"One cell" is what `cell.spice` simulates: **two ports** (`x1`, `x2`),
each with its gain mirror, sensor, window comparator, sequencing logic
and integrator, and the **shared** main capacitor, FIRE comparator and
protection latch.

The tables come from [`inventory.py`](inventory.py), which flattens the
two netlists and fails if it meets an element it cannot classify.

```sh
cd research/sky130-layout && python3 -I inventory.py
```

It writes `inventory_devices.csv` (334 rows, one per element; sha256
`805fc71a507d082e42ae9adfac4536d0dd42857b7425620644a33b9eef570ac1`) and
`inventory_summary.md` (sha256
`a578540f285146c32a26c0c6739d1b5a61bb7838b8027cac02f98e4e0e047469`).
Neither is committed.

## Totals

| | In one cell |
|---|---|
| Transistors | **232** (97 per port, 38 shared) |
| Drawn gate area, sum of W × L | 1 159 µm² |
| Capacitors that belong to the cell | 12, **71.6 pF** in all |
| of which the two feedback capacitors | 2 × 30 pF = 60 pF, 84% of the capacitance |
| Resistors that belong to the cell | 8, of which one of 8 MΩ |
| Ideal sources that a chip must replace | 33 |
| Elements of the test bench only | 49 |

Every transistor is a 1.8 V device of `sky130_fd_pr`, drawn once
(multiplicity 1, one finger) in the netlists.

## Transistors, block by block

W and L in micrometres. "×2" means once per port.

### Gain mirror, per port (×2)

| Device | Model | W / L | Role |
|---|---|---|---|
| `xmin` | `nfet_01v8` | 40 / 2.5 | Input device, diode-connected, source at `vcm` (0.4 V) |
| `xmout` | `nfet_01v8` | 40 / 2.5 | Output device, source on the stored voltage `vmem` |

Both work in subthreshold: 50 nA standing, 173 nA at the peak of a pulse.

### Integrator op-amp, per port (×2): subcircuit `opamp`

| Device | Model | W / L | Role |
|---|---|---|---|
| `xm1`, `xm2` | `pfet_01v8_lvt` | 16 / 1 | Input pair |
| `xm3`, `xm4` | `nfet_01v8` | 4 / 2 | Load mirror |
| `xm5` | `nfet_01v8` | 16 / 1 | Second stage |
| `xmb`, `xmt` | `pfet_01v8` | 8 / 2 | Bias diode and tail source, 1 : 1 |
| `xm6` | `pfet_01v8` | 32 / 2 | Second-stage source, 4 times `xmb` |
| `rz`, `cc` | | 4 kΩ, 1.5 pF | Compensation |

### Window comparator, per port (×2), and FIRE comparator, shared (×1): subcircuit `comp`

| Device | Model | W / L, window | W / L, FIRE | Role |
|---|---|---|---|---|
| `xm1`, `xm2` | `pfet_01v8_lvt` | 4 / 1 | 16 / 4 | Input pair |
| `xm3`, `xm4` | `nfet_01v8` | 2 / 1 | 2 / 1 | Load mirror |
| `xm5` | `nfet_01v8` | 2 / 0.5 | 2 / 0.5 | Second stage |
| `xmb` | `pfet_01v8` | 8 / 2 | 8 / 2 | Bias diode |
| `xmt` | `pfet_01v8` | 16 / 2 | 16 / 2 | Tail source, 2 times `xmb` |
| `xm6` | `pfet_01v8` | 16 / 2 | 16 / 2 | Second-stage source, 2 times `xmb` |
| `xi1`, `xi2` | two inverters | | | Output buffer |

### Sensor, steering and switches, per port (×2)

| Device | Model | W / L | Role |
|---|---|---|---|
| `xmbd`, `xmdis` | `nfet_01v8` | 0.42 / 8 | Discharge mirror, 1 : 1, 8.2 nA |
| `xmpre` | `pfet_01v8` | 2 / 0.5 | Precharge of the sensor capacitor to 1.3 V |
| `xmsi`, `xmsd` | `nfet_01v8` | 1 / 0.15 | Steering: discharge current to the summing node or to the dump node |
| `xms1`, `xms2` | `nfet_01v8` | 1 / 0.15 | Admission: mirror output to the main capacitor or to the rest level |
| `xmr1n`, `xmr2n` | `nfet_01v8` | 1 / 0.15 | Reference switches of the window comparator |
| `xmr1p`, `xmr2p` | `pfet_01v8` | 2 / 0.15 | Same, the PMOS halves |

Shared: `xmm1n`, `xmm2n` (1 / 0.15) and `xmm1p`, `xmm2p` (2 / 0.15),
the reference switches of the FIRE comparator.

### Logic

| Gate | Devices | Per port | Shared | In one cell |
|---|---|---|---|---|
| Inverter | PMOS 1 / 0.15, NMOS 0.42 / 0.15 | 11 | 5 | 27 |
| Two-input NAND | 2 PMOS 1 / 0.15, 2 NMOS 0.84 / 0.15 | 10 | 4 | 24 |
| Three-input NAND | 3 PMOS 1 / 0.15, 3 NMOS 1.26 / 0.15 | 1 | 0 | 2 |

The counts include the two output inverters of each comparator and the
two NAND gates of each of the seven latches. 162 transistors in all.

### All transistors by size

| Model | W | L | Count | Gate area each (µm²) | Total (µm²) |
|---|---|---|---|---|---|
| `nfet_01v8` | 40 | 2.5 | 4 | 100 | 400 |
| `pfet_01v8` | 16 | 2 | 6 | 32 | 192 |
| `pfet_01v8` | 32 | 2 | 2 | 64 | 128 |
| `pfet_01v8_lvt` | 16 | 4 | 2 | 64 | 128 |
| `pfet_01v8` | 8 | 2 | 7 | 16 | 112 |
| `pfet_01v8_lvt` | 16 | 1 | 4 | 16 | 64 |
| `nfet_01v8` | 4 | 2 | 4 | 8 | 32 |
| `nfet_01v8` | 16 | 1 | 2 | 16 | 32 |
| `pfet_01v8_lvt` | 4 | 1 | 4 | 4 | 16 |
| `nfet_01v8` | 0.42 | 8 | 4 | 3.36 | 13.4 |
| `pfet_01v8` | 1 | 0.15 | 81 | 0.15 | 12.2 |
| `nfet_01v8` | 2 | 1 | 6 | 2 | 12 |
| `nfet_01v8` | 0.84 | 0.15 | 48 | 0.126 | 6.0 |
| `nfet_01v8` | 2 | 0.5 | 3 | 1 | 3 |
| `nfet_01v8` | 1 | 0.15 | 14 | 0.15 | 2.1 |
| `pfet_01v8` | 2 | 0.5 | 2 | 1 | 2 |
| `pfet_01v8` | 2 | 0.15 | 6 | 0.3 | 1.8 |
| `nfet_01v8` | 0.42 | 0.15 | 27 | 0.063 | 1.7 |
| `nfet_01v8` | 1.26 | 0.15 | 6 | 0.189 | 1.1 |
| **Total** | | | **232** | | **1 159** |

Four gain-mirror devices are a third of the gate area. The 162 logic
transistors are 2% of it.

## Capacitors and resistors of the cell

| Element | Value | Count | Between | Role |
|---|---|---|---|---|
| **`cf`** | **30 pF** | 2 (one per port) | summing node `sum` and stored voltage `vmem` | Feedback capacitor of the integrator. The dose is `(C_s / C_f) × 100 mV` |
| `cq` | 5 pF | 1 | `vq` and ground | Main capacitor |
| `cdp` | 2 pF | 1 | ground | Delay of the protection latch, 200 ns with `rdp` |
| `cc` | 1.5 pF | 2 | inside the op-amp | Miller compensation |
| `cs` | 0.4 pF | 2 | `vs` and ground | Sensor capacitor |
| `cda`, `cdl` | 0.2 pF | 2 each | ground | Delays of the sequencing, 20 ns with `rda`, `rdl` |
| `rleak` | 8 MΩ | 1 | `vq` and the rest level `vr0` | Leak of the main charge, time constant two units |
| `rda`, `rdl` | 100 kΩ | 2 each | | Delays of the sequencing |
| `rdp` | 100 kΩ | 1 | | Delay of the protection latch |
| `rz` | 4 kΩ | 2 | inside the op-amp | Compensation zero |

In the netlists every one of them is an ideal element: no parasitic, no
mismatch, no voltage or temperature coefficient.

## Matching-sensitive pairs and ratios

What the circuit asks of each, and what the campaigns already say about
it. The mismatch of the campaigns is that of the device models, per
device, with no layout effect.

| Pair or ratio | Devices | What a mismatch does |
|---|---|---|
| **Gain mirror** | `xmin` / `xmout`, 40 / 2.5, per port | Sets the start gain, hence the need of the port. Training absorbs it (DESIGN.md). It is the main source of the spread of the need. The two sources sit at different voltages, so the pair is matched in size and not in bias |
| **Op-amp input pair** | `xm1` / `xm2`, lvt 16 / 1 | Offset of the summing node against `vcm`. The dump node is at `vcm`, so an offset changes the voltage the discharge device sees when the steering switches |
| Op-amp load mirror | `xm3` / `xm4`, 4 / 2 | Adds to the same offset |
| Op-amp bias mirror | `xmb` : `xmt` : `xm6` = 1 : 1 : 4, L = 2 | Tail and second-stage currents |
| **Window comparator input pair** | `xm1` / `xm2`, lvt 4 / 1, per port | Moves the entry and the exit level together: their difference, which is the dose, is unchanged. It moves the time of the write |
| **FIRE comparator input pair** | `xm1` / `xm2`, lvt 16 / 4, shared | Moves the FIRE level directly (DESIGN.md), hence the need of both ports |
| Comparator load mirrors | `xm3` / `xm4`, 2 / 1, three times | Add to the comparator offsets |
| Comparator bias mirrors | `xmb` : `xmt` : `xm6` = 1 : 2 : 2 | Currents, speed |
| Discharge mirror | `xmbd` / `xmdis`, 0.42 / 8, per port | Sets the discharge current, hence the dates of entry and exit. The dose does not depend on it |
| **Capacitor ratio** | `cs` : `cf` = 0.4 pF : 30 pF = 1 : 75, per port | **It is the dose.** A ratio error is a dose error of the same relative size. Not modelled in the campaigns ("capacitor mismatch", DESIGN.md) |
| Main capacitor | `cq`, and `rleak × cq` | The capacitance sets the gain a port needs to fire. The product sets the time constant of the leak |
| Steering pair | `xmsi` / `xmsd`, per port | Charge injected on the summing node when the steering switches. Already in the schematic simulation for the devices alone |
| Admission pair | `xms1` / `xms2`, per port | Charge injected on the main capacitor at the edges of the admission |

Not a pair, but placed with the same care: the two ports of a cell. They
share the FIRE comparator and the main capacitor, and nothing in the
circuit asks that they match.

## Ideal sources that a chip must replace

| Element | Count | What it is in the netlist |
|---|---|---|
| `vdd` | 1 | Supply, 1.8 V, ideal |
| `vr0`, `vfire`, `vreopen` | 1 each | Rest, FIRE and reopen levels of the main capacitor: 1.25 V, 0.80 V, 1.20 V |
| `vcm`, `vhi`, `vlo`, `vpre`, `vinit` | 1 each | 0.4 V, 0.6 V, 0.5 V, 1.3 V, 0.3895 V |
| `ibo`, `ibs` | 2 each | Bias sinks of the op-amp and of the window comparator, 10 µA each |
| `ibm` | 1 | Bias sink of the FIRE comparator, 10 µA |
| `idis` | 2 | Reference of the discharge mirror, 8.2 nA |
| `bip` | 2 | The pulse: a current that falls by a factor of four over 20 µs, 173 nA at its peak; 50 nA outside the pulse |
| `vksen`, `vkrst`, `vkpreb` | 1 each | The three clocks of a pulse: admission, reset of the latches, end of precharge |
| `bsen`, `brst`, `bpreb` | 2 each | Gating of the three clocks by the port that is pulsed |
| `vrsti`, `srst`, `bdrv` | 2 each | The preset of the integrator: an ideal switch (1 MΩ closed, 10 TΩ open) on the summing node, driven by an ideal amplifier of gain 10 |

By the mirror ratios above, the five bias sinks of 10 µA set a standing
supply current of about 0.27 mA for the cell: 60 µA per op-amp, 50 µA
per comparator. This is arithmetic on the netlist, not a simulated
figure.

## Test bench only

Nothing in this list is laid out: `rlk` (the imposed leak), the noise
sources `vnzc`, `vnzo`, `vnzi`, `vnzm` with their 1 kΩ resistors, the
adders `bvcmn`, `bvrs`, `bvrm` and the source `gnm` that inject the
noise, and the 10 kΩ / 20 fF and 1 kΩ / 20 fF networks that shape the
ideal signals. A layout must still give the bench a pin wherever these
connect: see [`RISKS.md`](RISKS.md).
