# Combined campaign: preregistration note 1 (2026-11-27, before any seed draw)

This note clarifies three passages of `PREDICTION.md` (commit `321284af`, left unchanged). It is pushed before the rehearsal's announcement and before any seed draw. It changes no rule of the frozen code (`5d02acce`); where the text and the frozen code differ, the frozen code and `FREEZE.txt` govern, as stated here.

## 1. §7, the draw command

The command shown in §7 (`draw BEACON ROUND EXCLUDED.json DRAW.json …`) is the form of `draw_seeds.py`'s arguments, not the campaign's procedure. Run as written for the campaign, it would give a draw the analysis refuses. The procedure is the `draw` block of `FREEZE.txt`, run verbatim:

- it draws on the published list X: for the campaign, that is `EXCLUDED_SECOND.json` as announced, not `EXCLUDED.json`;
- it writes `DRAW_CORE.json`;
- it then adds the verified round (`beacon_round`) and the announcement (`announce`) to give `DRAW.json`.

The rule that §7 states after the command is unchanged.

## 2. §5, fewer than 12 machines: the trial of two plans in a row

The move rule and the disk rule of §5 stand. The order is fixed now:

- **12 machines pass the rehearsal:** the campaign runs as planned, one plan per machine.
- **8 to 11 machines pass:** before the campaign's announcement, a trial of two plans in a row on one machine is run.
  - The trial uses test-mode plans on `evidence/devtest-run<N>-K<nn>` branches, in the order that §5's rule gives: a home plan first.
  - It passes if both runs end (DONE) and `analysis.py` in test mode accepts both roots.
  - Its record is published before the announcement.
- **The trial fails:** the draw is postponed.
- **Fewer than 8 machines:** the campaign is postponed (§5).

## 3. §6, the U control

§6 says "one run per group on its first eligible instance". The frozen code does this:

- `plan_split.py` gives a group's U to the plan that holds the group's first drawn seed;
- the driver (`campaign.py`) then runs U, in that plan only, on the smallest seed of that group that is eligible at K0.

If none of that plan's instances of the group is eligible at K0, the group has no U, even when instances on other plans are eligible. The analysis then lists that group's expected U as not present: "no eligible instance of the group, or the run stopped".

U is a control. Its absence changes no count and no verdict of §4. The report states it plainly.
