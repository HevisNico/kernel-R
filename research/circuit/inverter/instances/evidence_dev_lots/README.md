# Per-instance files of the inverter development lots

These are development lots, not preregistered. Each folder holds exactly the files that its source sums file lists,
copied from the run folders. Its `SHA256SUMS` is that sums file, byte for byte. `sha256sum -c SHA256SUMS` passes in
every folder; it was checked before the copy, against the run folders, and again after it.

| Folder | Source sums file (research/inverter-instances) | Files | Lot |
|---|---|---|---|
| `lot1` | `dev_lot/RESULT_SHA256SUMS` | 180 | lot 1, seeds 9911–9970, original gates (dev_lot/RESULT.md) |
| `lot1_regate_single_source` | `dev_lot/REGATE_SINGLE_SOURCE_SHA256SUMS` | 120 | lot 1 re-gated against the single-source gate (REGATE_SINGLE_SOURCE.md) |
| `lot1_regate_vl` | `dev_lot/REGATE_VL_SHA256SUMS` | 120 | lot 1 re-gated with StateBound (REGATE_VL.md) |
| `lot2` | `dev_lot_2/RESULT_SHA256SUMS` | 180 | lot 2, C5, seeds 9711–9770, reltol 1e-4 (RESULT_2.md) |
| `lot2_netopts` | `dev_lot_2/netopts/RESULT_SHA256SUMS` | 180 | lot 2 at the network's directives (RESULT_LOT2_NETOPTS.md) |

- **What each file is:**
  - `gates/GATE_<seed>.json` is the gate record;
  - `gates/Inverter_<seed>.lean` is the Lean file that the kernel accepted;
  - `runs/<seed>/MEASURE.json` is the measures. The re-gates kept their measures from lot 1, so they have none here.
- **Not included:** the simulator traces (about 265 MB per lot). They are listed with their hashes inside each
  MEASURE.json (`runs.<run>.files`).
- **No file is split:** the largest is 16 020 bytes, far below the 90 000 000-byte limit, so there is no PARTS.txt.
- **Computation:** numpy 2.3.5 (pinned), ngspice 42, SKY130 at the pinned commit.
