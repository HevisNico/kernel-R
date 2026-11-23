# Owner decisions on the layered calibration (relayed by the coordinator)

| Date (UTC) | Decision |
|---|---|
| 2026-11-23 11:12 | The either cell's testError keeps the **max rule** of CALIBRATION_PROPOSAL.md (c): the max of the one-port rule and the two-port both-lines budget. No rule change after a failure is seen. (M3_REPORT.md reported the alternative; it is not adopted.) |
| 2026-11-23 11:12 | M4 starts with two instrument fixes: (a) every scan re-reads the training stop state, so that it has its own FIRE and its own silence (rule D3); (b) D4, parallel scans, is bounded by a solo scan of the same cell from the same state, turned into a budget term or, if it cannot be bounded, a rule. |
