# Amendment to development lot 2: re-measure at the layered network's simulator directives

**Development work, not preregistered.**
- This amendment is committed alone, before any of its runs. It changes ONLY the simulator directives.
- The owner approved it, through the coordinator.

## What changes

The deck's `.lib`, `.param` and `.option` lines become exactly those of the layered network for an inverter
(`research/layered-networks` at a308eec: `instrument.deck_text` at the `calibration.json` design point):
- `.option reltol=1e-5 abstol=1e-13 vntol=1e-7 chgtol=1e-17`; lot 2 ran at reltol 1e-4;
- the network's six `.param` lines, including `vhi=0.7`, which only the R cells use;
- `.option scale=1e-6`, `.option gmin=1e-16`, `.option temp=27`, and the section `tt_mm`.

How:
- `config_netopts.json` holds those lines verbatim.
- `invinst/netdeck.py` swaps them into `cell.netlist`'s deck and changes nothing else.
- `invinst/measure2.py` and `invinst/driver2.py` are measure.py and driver.py at those directives. The pushed files
  stay as pushed.
- `tests/test_netopts.py` exports a308eec, builds the network's decks with its own builder, and asserts the
  identity. It passes.

Junction areas: the network gives the inverter's devices zero areas, which is the PDK subcircuits' default
(`ad = as = pd = ps = 0`). The inverter's deck leaves them implicit, as before. The test asserts the network's zeros.

**One stated difference that remains.**
- The transient's maximum step stays as in lot 2 (5 ns for R1, R2 and R5; 20 ns for R3 and R4). It is the
  measurement's time resolution for the integrals and the crossing dates.
- The network session runs `tran 1u ... 0 200n`.
- It is reported, not changed.

## What does not change

- **Design:** C5 (help mirror w 2, l 16; J0 4.0), `config.json` as at d25ee8e.
- **Seeds:** the same 9711-9770 (`JOBS`), N = 60.
- **Measures, gate, Lean library and open premises:** the same.
- **Target:** the min K3 silence margin over all instances is at least 0.05, and room is at least 57/60. Either missed:
  "C6 fallback". Both met: "C5 holds".
- **Early stop:** after 20 finished, fewer than 19 with room stops the lot. This is the same `rule.json`.
- **Limits:** a ceiling of 90 machine-minutes, 30 minutes per job, 4 at a time.

## Code and cost

- **Code:** the package at 5a26a40, run as `python -m invinst.driver2 dev_lot_2/JOBS OUT --stop dev_lot_2/rule.json`.
- **Cost:** at reltol 1e-5 a nominal instance took 71 s, against 59 s at 1e-4. That is about 71 machine-minutes for
  60, under the ceiling.
- **Nominal smoke check (tt, no draw):** kernel true at K0 and K3, silence margin K0 0.171 (0.189 at 1e-4), ηH 0.043
  (0.027 at 1e-4).

## Report

As lot 2's rule specifies, together with the per-instance differences against lot 2 (a55153a): eligible, room, K0
and K3 margins, ηH, δ, X and emission. It goes in `RESULT_LOT2_NETOPTS.md`. `RESULT_2.md` stays unchanged.
