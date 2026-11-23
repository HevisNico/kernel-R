# Owner decisions on the layered calibration, continued (relayed by the coordinator)

DECISIONS.md is pushed and is not modified (owner rule); later decisions are recorded here.

| Date (UTC) | Decision |
|---|---|
| 2026-11-23 14:24 | A cell whose question-1 check disagrees (⌈s*⌉ differs from the training's first FIRE round) stays **not measured**, as fit.py has it, even when its bracket contains the stop state (the case of ANDOR3 c1_0 on 9802 at 2x, DESIGN_POINT_REPORT.md). It is not reclassified as measured and not eligible. |
| 2026-11-23 14:24 | XOR3 waits until the inverter is re-measured at the layered deck's options (reltol 1e-5, the network's max step), in a separate session. |
| 2026-11-23 14:24 | The 2x reruns (a308eec) are accepted. |
