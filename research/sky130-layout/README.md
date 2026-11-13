# Layout of one R cell in SKY130: phase 0

**Phase 0 is exploratory. Nothing here is preregistered. No R cell was
laid out, no parasitic of the cell was extracted, and no post-layout
simulation of the cell exists.** What exists is a working toolchain, an
inventory, an area estimate, a risk list and a proposed plan.

The [circuit study](../circuit/README.md) simulates one R cell at
transistor level, at schematic level, with ideal timing. An external
assessment listed what it lacks: no layout, no energy figure, idealized
timing, a density incompatible with a crossbar. This folder takes the
first item.

**The layout bet:** lay out one R cell in SKY130 with the open-source
flow, extract its parasitics, simulate again, and test whether the
certified behaviour survives them.

## What phase 0 delivers

| | Deliverable | File | Status |
|---|---|---|---|
| 1 | Toolchain proof: the whole loop on one inverter, with versions and installation commands | [`TOOLCHAIN.md`](TOOLCHAIN.md), [`toolchain-inverter/`](toolchain-inverter/) | Run. DRC clean, LVS clean, extracted, simulated |
| 2 | Inventory of one cell: every device, the 30 pF feedback capacitors, the matching-sensitive pairs | [`INVENTORY.md`](INVENTORY.md), [`inventory.py`](inventory.py) | Read from the netlists |
| 3 | Floorplan and area estimate | [`FLOORPLAN.md`](FLOORPLAN.md), [`footprints/`](footprints/) | Estimate, from parts drawn alone |
| 4 | Risk list | [`RISKS.md`](RISKS.md), [`checks/`](checks/) | Three findings from small probes; the rest is reasoning |
| 5 | Proposed plan for phase 1, with candidate predictions and a compute budget | [`PHASE1_PLAN.md`](PHASE1_PLAN.md) | A proposal. Nothing registered, nothing run |

## What was found

- **The loop runs.** One inverter went through xschem, Magic, KLayout,
  netgen and ngspice 42: 0 DRC errors in Magic and in KLayout, LVS
  "Circuits match uniquely", parasitics extracted, schematic and
  extracted netlists simulated with the device models of the campaigns.
  Two planted errors were both caught.
- **Same PDK, same simulator.** The device models are those of
  `../circuit/fetch_pdk.sh`, and the ngspice binary has the hash the
  campaigns recorded. The nominal run of the circuit study, run again
  here, is identical byte for byte to the committed result.
- **The capacitor figure holds for the plate, not for the footprint.**
  The MIM model gives 2.02 fF/µm² (simulation): 30 pF is 14 840 µm² of
  plate. Drawn as an array it takes 18 300 to 23 300 µm².
- **One cell of two ports is about 0.05 to 0.065 mm²** on a single MIM
  layer: 30 to 40 ports per mm². The two feedback capacitors are about
  70% of it. This is an estimate with two stated assumptions.
- **The schematic netlists give the transistors no source or drain
  area.** The campaigns were therefore simulated with no junction
  capacitance, and with a default junction current that does not depend
  on temperature. A probe on one switch, with the areas an extraction
  gives it, puts the junction current eight times lower at 27 °C and
  1 300 times higher at 125 °C.
- **A mismatch seed does not survive a change of the netlist.** An
  extracted netlist simulated with the seed of a certified cell is
  another cell. A probe shows that the sample is kept when parasitics
  are added to the unchanged device lines. Phase 1 has to work that way.
- **Stacking two MIM levels was tried and not achieved.**

## What was not done

- No layout of the cell or of any of its blocks other than the inverter.
- No extraction of the cell. No post-layout simulation of the cell.
- No energy figure of the cell. The plan proposes to report one.
- No antenna, density or fill check.
- The slowdown of a post-layout simulation of the cell is not measured.
  The compute estimate of the plan rests on an assumption, and on a
  scope rule that a timing run settles before preregistration.

## Running

Tools and installation: [`TOOLCHAIN.md`](TOOLCHAIN.md).

```sh
cd research/circuit && sh fetch_pdk.sh        # device models, if not there yet
cd ../sky130-layout
python3 -I inventory.py                       # the inventory
(cd toolchain-inverter && sh run.sh)          # the loop on the inverter
(cd footprints && sh run.sh)                  # footprints of the parts
(cd checks && sh run.sh)                      # MIM density, junction current, mismatch identity, nominal run
```

Generated files go to `build/` folders and are not committed. Each
folder has a `SHA256SUMS` of the outputs that carry no date. The GDS and
the `.mag` files carry one and are not hashed.

No file outside this folder was changed.
