# Exceptions to "a pushed file is never modified"

**The rule.** Once pushed, a file is never modified; corrections go as new files.

**The breach.** The four development files below were pushed at 280c6f6 and were modified afterwards, in local
commits. The worker found this itself before the next push. The owner granted an exception for exactly these four
files and these changes (14 lines in all). Each changed line is listed below.

**From now on** no pushed file is modified. Later changes go into new, versioned files.

| File | Commit | Change | Reason |
|---|---|---|---|
| `invinst/cell.py` | bb4b8cc | `.param vfire={{vr0 - 0.9*vunit}}` became `.param vfire={{vr0 - {c['level_x']:g}*vunit}}` (1 line) | the threshold lever of design sweep 2 (C3). At the configured level 0.9 the deck is byte-identical, as `tests/test_cell.py` checks |
| `config.json` | d25ee8e | `help_mirror` `{"w": 2, "l": 4}` became `{"w": 2, "l": 16}`, and the `_doc` string names redesign 2 (2 lines) | adoption of C5 (`design_sweep/SWEEP_2.md`), the owner's decision |
| `invinst/driver.py` | d25ee8e | the stop rule may also count room (`min_room`); `min_eligible` became optional; docstring updated (10 lines) | lot 2's rule (`dev_lot_2/rule.json`) stops on room. Lot 1's behaviour (`min_eligible`) is unchanged |
| `tests/test_cell.py` | d25ee8e | `REDESIGN` lists `help_mirror` 2×16 beside `J0` 4.0 (1 line) | the test asserts the deck equals the pushed cell apart from the listed redesign |

Lot 1 (`dev_lot/`, 96b867b and the re-gatings) ran on the files as pushed at 280c6f6 or earlier. Lot 2
(`dev_lot_2/`, a55153a) ran on the files as at d25ee8e.
