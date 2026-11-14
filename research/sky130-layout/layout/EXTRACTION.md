# Extraction of the cell

Written after [`README.md`](README.md), which it completes: the list
"Not done yet" there was true when it was pushed. **Nothing here is a
simulation of the cell.** No stage-P run has been made.

```sh
cd research/sky130-layout/layout && sh run.sh && sh run_pex.sh
```

Hashes: [`SHA256SUMS_PEX`](SHA256SUMS_PEX). The two tables are also
committed, as extracted, in `../phase1/p_areas.csv` and
`../phase1/p_caps.csv`.

## What was done

- The cell is flattened in Magic and extracted with capacitance only
  (decision D5): [`cell_pex.tcl`](cell_pex.tcl).
- [`pex.py`](pex.py) gives every extracted transistor and net the name
  it has in `cell.spice` as ngspice flattens it. It stops on a device or
  a net with no counterpart.

| | |
|---|---|
| Transistors found | 232 of 232, from 264 extracted fingers |
| Capacitances | 1 436 pairs between 149 nodes; 421 of them below 0.01 fF |
| Their sum | 5.585 pF, of which 1.880 pF to node 0 (substrate and `vss`) |

## Source and drain areas

20 transistors differ from the table of stage J
(`../phase1/areas.csv`): the 20 that have several fingers. A drain
shared by two fingers is counted once. Example, `x1.xmin`: drain 5.8 µm²
and source 8.7 µm², against 7.25 and 7.25 in stage J.

**The sum of all source and drain areas is the same in both tables,
339.8 µm².** No diffusion is shared between two transistors: each keeps
its guard ring.

## Capacitances on the main nodes

Port 1; port 2 is within 0.3 fF on each line.

| Node | To node 0 | To the other plate of its capacitor | To every other net | Largest of those |
|---|---|---|---|---|
| `x1.sum`, summing node | 29.7 fF | 1 443.5 fF to `vmem1` | 6.7 fF | `vdd` 1.1 fF |
| `x1.vs`, sensor node | 27.3 fF (its capacitor goes to node 0) | | 9.3 fF | `vdd` 1.9 fF, `vmem1` 1.7 fF, `x1.sum` 0.9 fF |
| `vq`, main capacitor | 253.1 fF (its capacitor goes to node 0) | | 44.2 fF | `vlo` 14.3 fF, `x2.dq` 9.1 fF |
| `vmem1`, stored voltage | 288.5 fF | 1 443.5 fF to `x1.sum` | 87.0 fF | `x1.xop.oz` 64.5 fF |

`vq` is not symmetric between the ports: 9.1 fF to `x2.dq` and 0.8 fF to
`x1.dq`. The two ports are mirror images; the wires that join them are
not.

## Finding F4: Magic counts the top plate of a MIM capacitor as a wire

**Between the two plates of every MIM capacitor, the extraction adds
4.3% to 5.1% of its value.** `pex.py` prints the table
(`build/pex.txt`):

| Capacitor | Ideal value | Extracted between its plates | Metal4 over metal3, by Magic's rule for wires |
|---|---|---|---|
| `cf` | 30 pF | 1 443.5 fF, 4.81% | 1 455.3 fF |
| `cc` | 1.5 pF | 64.5 fF, 4.30% | 68.1 fF |
| `cq` | 5 pF | 253.1 fF, 5.06%, wiring to the substrate included | 228.5 fF |
| `cdp` | 2 pF | 97.8 fF, 4.89%, wiring included | 92.2 fF |
| `cs` | 400 fF | 27.3 fF, 6.83%, wiring included | 19.4 fF |
| `cda`, `cdl` | 200 fF | 14.9 and 17.2 fF, wiring included | 10.2 fF |

What is known:

- Magic's technology file gives metal4 over metal3 84.03 aF/µm² and
  70.52 aF per µm of edge, as for two wires. The last column applies
  these two numbers to the metal4 of the plates alone. It accounts for
  what is extracted between the plates.
- One plate of 14 µm extracted alone gives 17.1 fF between its plates.
- The capacitor model of the PDK is the capacitance of the capacitor
  layer alone: `c = ca × (w + dw) × (l + dw)`. It has no other term.
- In a MIM capacitor the metal4 sits on the top electrode, is joined to
  it by vias, and the top electrode lies between it and metal3.

**Reading, not a measurement:** the capacitance between metal4 and
metal3 through the top electrode does not exist, and Magic counts it
on top of the device. No field solver was run. One attempt to make
Magic treat the capacitor layer as a shield, in a copy of the
technology file, changed nothing and was not pursued.

**Why it matters before stage P.**

- `cf` and `cs` both grow by about 4.8% from this term, so their ratio,
  the dose, hardly moves. With everything extracted the ratio
  `(cs + 27.3 fF) / (cf + 1 443.5 fF)` is 1.9% above `cs / cf`; with
  the plate term taken out by the rule of the last column it is about
  2.0% above. This is arithmetic on the table, not a simulation.
- `cq` grows by 253 fF as extracted, and by about 25 fF without the
  plate term. Prediction L8 was reasoned on "1% per 50 fF" on `vq`.

**This needs a decision of the owner, in an amendment, before the first
stage-P run:** take the extraction as it comes, as
[`../PREDICTION.md`](../PREDICTION.md) says ("the extracted
capacitances"), or take the plate term out by a rule fixed in advance,
or run both and say which one decides the predictions. Nothing was
simulated to inform that choice, and nothing will be before it is
made.

## Not done

- The run with resistance extracted (one nominal run, reported apart).
- The identity test I2 with these capacitances at 0 F, the timing run,
  the scope, the launcher of stage P: each waits for the owner.
