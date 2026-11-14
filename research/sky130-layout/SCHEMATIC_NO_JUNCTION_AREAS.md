# Note: the schematic campaigns had no source or drain areas

A statement about the earlier campaigns, found in phase 0 of the layout
study. It changes no file of those campaigns and no verdict.

**The netlists of the circuit study, `../circuit/cell.spice` and
`../circuit/blocks.spice`, give every transistor a width and a length
and nothing else.** The SKY130 model wrapper sets the source and drain
areas and perimeters (`ad`, `as`, `pd`, `ps`) to zero when they are not
given.

This holds for every simulation made from these two netlists: the
circuit campaign and its complement, the certification campaign, the
measured-conditions campaign and the repetition campaign.

What it means, in the transistor model of the simulator:

- **No junction capacitance** on any source or drain.
- **A junction current that is a default of the model**, not a property
  of the process: 10 fA per junction, the same at every temperature. A
  probe on one switch gives 20.0 fA for its two junctions at 27 °C,
  85 °C and 125 °C. With the areas an extraction gives the same switch,
  the model gives 2.4 fA, 1.06 pA and 26.4 pA.

So the run of the campaign at 125 °C had the same junction current as
the runs at 27 °C. The probe is on one device. Its
effect on the cell is not known until it is simulated: that is stage J
of [`PREDICTION.md`](PREDICTION.md).

Where it comes from: [`RISKS.md`](RISKS.md), finding F1, and
[`checks/jleak.spice`](checks/jleak.spice). These are simulations, at
the typical corner, with the device models of
`../circuit/fetch_pdk.sh`.

`../circuit/DESIGN.md` lists "leakage of the stored voltage beyond the
device models" as not modelled. This note adds that the device models
themselves were used without their junction areas.
