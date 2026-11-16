# Campaign 4: wall times measured on the nominal cell for the cost model

Item 2 of the owner's cost-model decision ([`../COST_MODEL_DECISION.md`](../COST_MODEL_DECISION.md), commit
`2ffe04d`): a calibration deck and the untrained control run, measured before the preregistration of campaign 4, in
the conditions of the measured runs of the noise study (nominal cell, four runs at a time on one 4-processor
machine). **This is not campaign implementation**: it runs existing code only, on the nominal cell (section `tt`, no
mismatch seed), and touches no seed of campaign 4 (7501 onward) and no other mismatch seed. Exploratory, no claim.

- [`measure.py`](measure.py): the driver (wall time of each process, peak resident memory of its simulator by
  `wait4`). [`dnf_untrained.py`](dnf_untrained.py): a calendar shim, so that the noise study's `cost3.py` runs the
  untrained control calendar of [`../dnf.py`](../dnf.py).
- [`COST_MEASURES.json`](COST_MEASURES.json): the result, with the commits of the code it ran (this branch at
  `915daf7`; the noise study at `c2cb677`).

| Run | Code | Four at a time | Wall time | Peak memory |
|---|---|---|---|---|
| calibration deck, **one cell**, amplitude 0.49, 8 stages (2 guard on, 2 guard off) | `../calibrate.py` (phase 0) | yes | 123 to 127 s, mean 125.1 s | 378 to 380 MB |
| untrained control, three cells, 7.43 ms, 40 pulses | noise study's `cost3.py _run ... quiet` with `dnf_untrained.py` | yes (4 copies) | 368 to 371 s, mean 369.2 s | 399 MB |

Limits, stated for the use of these numbers:

- Phase 0's calibration code calibrates one cell. For sizing, its time is scaled to the three-cell calibration deck
  of campaign 4 by `dnf.cost`, as the cost-model decision scales calendars (accepted by the owner); the rehearsal
  measures the real three-cell deck, and the fixed rule of the preregistration can only lower `I`.
- The untrained control is run under `cost3.py`'s emulation of campaign 4's calendar, as its need-4 run of 814 s:
  every input at amplitude 1 and no read-only gate. Its words are not looked at.
- The extraction is not measured here; it is costed from the noise study's figures.

Reproduce (the environment of `research/network-noise-study/phase0/FEASIBILITY.md`; `NS_SRC` a checkout of
`c2cb677`):

```
python -B measure.py OUT.json WORK /usr/bin/ngspice $PDK $NS_SRC
```
