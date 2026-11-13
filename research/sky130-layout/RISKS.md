# Risk list for the layout of one R cell

Phase 0, item 4. What can make the post-layout cell differ from the
simulated one, and what the post-layout simulation will and will not
see. Each risk says where its numbers come from. "Probe" means a small
simulation of phase 0, on one device or one model, nominal, typical
corner: [`checks/run.sh`](checks/run.sh). **No probe is a simulation of
the cell.**

Orders of magnitude used below, from
[`../circuit/DESIGN.md`](../circuit/DESIGN.md):

| Quantity | Value |
|---|---|
| Charge of one dose | 400 fF × 100 mV = 40 fC |
| One dose on the stored voltage | 1.3465 mV, 0.042 in log-gain at 27 °C |
| Half a dose, the budget of the need theorem | 0.021 in log-gain |
| Period between pulses | 440 µs |
| Imposed leak of the refresh runs | 0.1 TΩ on the summing node at 0.4 V: 4 pA |

## Found in phase 0

Three findings change how phase 1 must be run. They come first.

### F1. The schematic netlists give the transistors no source or drain area

`cell.spice` and `blocks.spice` write `w=` and `l=` only. The model
wrapper of the PDK defaults `ad`, `as`, `pd`, `ps` to zero. An extracted
netlist carries them. So the campaigns were simulated with **no junction
capacitance and no junction area**, and every post-layout run adds both,
whatever the wires do.

Probe (step 2): the reverse current of the two n-diffusions of a
1 µm / 0.15 µm switch held at 0.4 V, gate off.

| Temperature | No area, as in the campaigns | With the areas Magic extracts |
|---|---|---|
| 27 °C | 20.0 fA | 2.4 fA |
| 85 °C | 20.0 fA | 1.06 pA |
| 125 °C | 20.0 fA | 26.4 pA |

- Without areas the current is 10 fA per junction at every temperature:
  a default of the transistor model, not a property of the process.
- With areas it is eight times lower at 27 °C and 1 300 times higher at
  125 °C.

What it means for the cell, by arithmetic and not by simulation: the
steering switch `xmsi` puts one such diffusion on the summing node. At
125 °C, about 13 pA there is 5.8 fC per period, 14% of a dose, three
times the imposed leak of the refresh runs. The run of the campaign at
125 °C carried the default of 10 fA instead. A post-layout cell at 125 °C may refresh every
few periods where the campaign shows a stop that holds. At 27 °C the
leak of the junctions is below what the campaigns carried.

### F2. A mismatch seed does not survive a change of the netlist

The certified ports are ports of cells defined by a seed: cell `t6002`
is seed 6002 on `cell.spice`. Probe (step 3): three devices, seeds 6002
and 6065, gate voltages printed with six digits.

| Netlist | Same mismatch sample as the reference? |
|---|---|
| Source and drain areas added to the devices, parasitic R and C appended after them | **Yes**, to the last printed digit, on both seeds |
| Same devices, written in another order | No: differences of 0.1 to 6 mV |
| One device split in two parallel fingers | No: differences of 1 to 6 mV |

The netlist that Magic extracts reorders the devices and writes fingers
as it finds them. Simulated with seed 6002 it is **another cell**, not
`t6002` with parasitics. "Certified ports stay certified" can only be
tested if the devices keep their order and their lines, and the
parasitics are added to them. Phase 1 must build that annotated netlist
and prove the identity before any other run:
[`PHASE1_PLAN.md`](PHASE1_PLAN.md).

### F3. The feedback capacitor is an array, and its footprint is 23 to 57% above its plate

See [`FLOORPLAN.md`](FLOORPLAN.md). The largest plate is 30 µm × 30 µm.
Stacking two MIM levels was tried and not achieved.

## 1. Matching

| Risk | Why it matters here | What phase 1 can do | Seen by post-layout simulation? |
|---|---|---|---|
| Gain mirror pair `xmin` / `xmout`, 40 / 2.5 | Its mismatch sets the need of the port. Training absorbs it, and the certification measures it | Interdigitated or common-centroid fingers, dummies, same orientation, one guard ring | **No.** Extraction does not turn a placement into a mismatch. The mismatch stays that of the device model |
| Input pairs of the op-amp and of the three comparators | Offsets of the summing node, of the window and of the FIRE level | Same | No |
| Bias mirrors 1 : 1 : 4 and 1 : 2 : 2 | Currents of every stage | Unit devices of 8 / 2, the ratio by count | No |
| Stress and well-proximity effects | Shift the threshold of a device near a well edge or at the end of a row | Dummies, distance to the well edge | No: Magic does not extract the stress parameters of the models |
| Fingers | A wide device is drawn in fingers. If the netlist then holds four devices of 10 µm for one of 40 µm, the mismatch sample changes (F2) | The annotated netlist keeps one device line per schematic device | Handled by construction, to be proved by the identity test |
| Monte Carlo parameters of the pinned models | `fossi-foundation/skywater-pdk-libs-sky130_fd_pr`, which continues the pinned repository, has since reworked its Monte Carlo parameters (16 commits after `1232782c…`) | Stay on the pinned commit, as required. Say in the report that the mismatch statistics are those of that commit | Not a layout question |

**Consequence.** A post-layout simulation cannot say whether the layout
matches well. It can only say what the parasitics do to cells whose
mismatch is the one the device models draw. Matching is argued by
construction and checked by review, not by a run.

## 2. Capacitor implementation

| Risk | Numbers | What phase 1 can do |
|---|---|---|
| **Ratio `C_s / C_f` = 1 : 75. It is the dose** | A ratio error of 1% is a dose error of 1%. The certification budget per write, `b`, has a target of 0.0026 in log-gain, 6% of a dose | Unit plates of 0.4 pF: 75 for `C_f`, 1 for `C_s`, dummies around. Costs about 10 000 µm² per cell against large plates |
| Parasitic on the sensor node `vs` adds to `C_s` | 1 fF is 0.25% of a dose. The schematic step is already 1% above `C_s / C_f × 100 mV` (1.3465 mV against 1.3333 mV) | Top plate on `vs`, short wire, report the extracted value |
| Parasitic between `sum` and `vmem` adds to `C_f` | 30 fF is 0.1% of a dose | Small by ratio |
| Parasitic from `sum` to ground | Does not change the charge transferred. Raises the gain of the op-amp noise by `C_sum / C_f` | Bottom plate of `C_f` on `vmem`, the driven side |
| Capacitor mismatch | Not modelled in the campaigns. The MIM model of the PDK has a mismatch term | Decision for the owner. If the annotated netlist keeps ideal capacitors, the mismatch sample of the transistors is kept (F2) and capacitor mismatch stays unmodelled. If it uses the MIM model, each capacitor draws random numbers and the cells are no longer the certified ones |
| Bottom-plate parasitic on the op-amp output | Loads the output that also drives the source of the mirror | Check the phase margin of the op-amp with the extracted load |
| Antenna rules | The summing node joins a gate of 16 µm² to a top plate of about 15 000 µm² | If a protection diode is needed on `sum`, it adds a junction to the node that stores the gain (F1). To check before the layout is frozen |
| Voltage coefficient, dielectric absorption, dielectric leakage | Not in the model used here | Not testable by simulation |
| Area | 18 300 to 23 300 µm² per feedback capacitor | See [`FLOORPLAN.md`](FLOORPLAN.md) |

## 3. Parasitics on the integrator and the summing nodes

The summing node `sum` holds the gain: nothing drives it but the
feedback capacitor. Any charge that reaches it is written.

| Risk | Numbers | Seen by post-layout simulation? |
|---|---|---|
| **Coupling from a switching net to `sum`** | A coupling of 1 fF from a net that swings 1.8 V moves 1.8 fC, 4.5% of a dose, at each edge. A net that returns to its level before the next read gives the charge back; the stored voltage is still wrong in between | Yes, with capacitance extraction. The first thing to look at |
| Coupling to the node `x` between the discharge device and the steering switches | Same mechanism, upstream of the steering | Yes |
| **Junction leak on `sum`** | F1: negligible at 27 °C, about 13 pA per switch diffusion at 125 °C by arithmetic | Yes, if the areas are annotated. Not at all in the campaigns |
| The preset switch | In the netlist it is ideal: 10 TΩ open. A real switch on `sum` adds a junction and a channel leak, and injects charge when it opens | Only if it is drawn. See section 4 |
| Charge injection of the steering switch | Already in the schematic for the device. The wires of `si` and `sd` add coupling | Yes |
| **Parasitic on the main capacitor node `vq`** | It adds to 5 pF and raises the gain a port needs to fire. 50 fF is 1%: 0.010 in log-gain, a quarter of a dose and **half the budget of the need theorem**. The resistor of 8 MΩ alone is 490 µm² of poly on that node | Yes. It shifts the predicted need of a port whose margin is thin |
| Parasitic on the gate of the mirror | The gate area is already 200 µm² per port. Coupling from the admission clock to this gate changes the current during the pulse | Yes |
| Resistance of the wires | Currents are nanoamperes to microamperes. Not expected to matter, except in the supply and ground of the logic | Partly: one nominal run with resistance extracted |
| Coupling through the substrate and the wells | Logic edges next to the summing node | **No.** Magic extracts no substrate network |
| Supply and ground bounce | DESIGN.md already lists it as not modelled | **No**, with an ideal supply |

## 4. Ideal signals that a real layout must still receive

The cell of `cell.spice` does not work alone. A layout of "one R cell"
must fix where the cell ends. Everything in this table is outside it in
the netlist, and enters through a pin.

| Signal | Count | In the netlist | A real chip needs |
|---|---|---|---|
| Admission clock `ksen` | 1, gated per port | Ideal, high during the pulse, 1 ns edges through 10 kΩ and 20 fF | A pulse detector. Not built (DESIGN.md) |
| Reset of the sequencing latches `krst` | 1, gated per port | Released 1 µs **before** the pulse | A detector cannot do that. A real cell must clear its latches at the end of the previous cycle (DESIGN.md) |
| End of precharge `kpreb` | 1, gated per port | Ideal | The same detector |
| Port selection | 2 ports | Behavioural sources choose the pulsed port | Routing of the clocks |
| Pulse current `bip` | 2 | Ideal current, exact exponential shape | The upstream cell or a pad |
| Preset of the integrator | 2 | Ideal switch on `sum`, ideal amplifier of gain 10 | A real switch on the node that stores the gain, and a servo |
| Bias sinks | 5 of 10 µA | Ideal | A bias generator and its mirrors, with their mismatch |
| Discharge reference `idis` | 2 of 8.2 nA | Ideal current into the diode of the mirror | A nanoampere reference |
| Reference voltages | 8 | Ideal, noiseless, zero impedance | References or pads. The window `vhi − vlo` = 100 mV **is the dose**; `vfire` and `vr0` set the need |
| Supply | 1 | Ideal | Decoupling, a real grid |
| Noise injection | 4 kinds | Behavioural adders in front of the op-amp and comparator inputs | Nothing on a chip. But the layout must leave these inputs as pins so that the bench can still inject the noise of the campaigns |
| Imposed leak `rlk` | 2 | A resistor on `sum` | Nothing on a chip. The bench needs `sum` as a pin, which puts a wire on the most sensitive node |

**Decision for the owner before phase 1:** the boundary of the layout.
The proposal is in [`PHASE1_PLAN.md`](PHASE1_PLAN.md): transistors,
capacitors and resistors of the cell inside; every row of this table
outside, as pins. With that boundary the layout bet tests the parasitics
of the cell, and says nothing about the timing signals, the references
or the preset.

## 5. Method

| Risk | What phase 1 does about it |
|---|---|
| A post-layout run is another cell (F2) | Annotated netlist and identity test |
| The post-layout result is seen before the predictions are fixed | The only run allowed before preregistration prints a wall time and nothing else |
| The calibration constants of the certification (`d0`, `kappa`, `mu`) belong to the schematic | Recalibrate on the annotated netlist by the registered procedure, on a smaller cohort; report the frozen constants as a second analysis |
| The runners of the campaigns check the hash of `cell.spice` | New runner and new manifest under this folder. No existing file is edited |
| Extraction is rule-based | Stated in the report. No claim of accuracy for the extracted values |
| A clean LVS that hides a size error | "Match uniquely" and no property error, both required ([`TOOLCHAIN.md`](TOOLCHAIN.md)) |
| The simulation slows down beyond the budget | Scope ladder fixed in advance |
