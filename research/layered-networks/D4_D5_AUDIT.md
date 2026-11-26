# D4 and D5: the recursion and the guard's reach, and an audit of the driver chain (2026-11-26). Development only

## D4: campaign_run16's recursion
- **The bug.** campaign_run16.step (the comparison exemption) called `C4.Instance.step(...)`. At run time
  campaign_run5.cmd_run sets `C4.Instance = Instance` (campaign_run5.py:132). That is campaign_run5's class, whose
  `step` campaign_run16 had replaced with campaign_run16.step, so the call returned to itself. Every instance stopped
  at C0 with RecursionError.
- **The fix in campaign_run17.** It binds, at import, before any cmd_run:
  - `_C5` = campaign_run5's Instance class;
  - `_C5_STEP` = its step;
  - `_PARENT_STEP` = `_C5.__mro__[1].step`, campaign_run4's Instance.step;
  - the original campaign_run7.untrained_with, campaign_run9.drop_raw and campaign_run10.remote_duplicate.

  It patches `_C5.step` on that class object, not through `C5.Instance`. Its replacements call only the bound
  functions.

## The audit: every replacement that calls "its parent"
Method: every run-time reassignment in campaign_run2–17, and every call inside an installed replacement that goes
through a module attribute (grep of both, then read).

| replacement (installed by) | calls | bound at import? | reassigned at run time? | can recurse |
|---|---|---|---|---|
| campaign_run16.step (16) | `C4.Instance.step` | no | yes (campaign_run5.py:132) | **yes: D4** |
| campaign_run17.step (17) | `_PARENT_STEP`, `_C5_STEP` | yes | — | no |
| campaign_run5.drop_raw (5, as CR.drop_raw) | `_drop_raw` = CR.drop_raw at import | yes | — | no |
| campaign_run9.drop_raw (9, as C5.drop_raw) | `_c5_drop_raw` | yes | — | no |
| campaign_run14.drop_raw (14–17, as C9.drop_raw) | `_c9_drop_raw`, `_cr_drop_raw` | yes | — | no |
| campaign_run9.remote_duplicate (9, as C4.remote_duplicate) | `_c4_remote_duplicate` | yes | — | no |
| campaign_run10.remote_duplicate (10, as C9.remote_duplicate) | `_c9_remote_duplicate` | yes | — | no |
| campaign_run15/17.remote_duplicate (as C10.remote_duplicate) | `_c10_remote_duplicate` / `_C10_DUP` | yes | — | no |
| campaign_run6/7 stagen_argv lambdas (as CR.stagen_argv) | `C7.stagen_argv` → `C6.stagen_argv` → `_stagen_argv` (CR at import) | module functions never reassigned; the last bound | no | no |
| campaign_run4/6/7 untrained lambdas (as CR.untrained) | `untrained` (local) / `C7.untrained_with` (global lookup) | the local yes; C7.untrained_with is replaced by campaign_run17 with a function calling the bound original | only by 17, to its own wrapper | no |
| campaign_run12.set_env (as C9.set_env) | `C11.set_env` | module function, never reassigned | no | no |
| campaign_run9's c2_held (as C2.cmd_run) | `orig["c2_run"]` | yes | — | no |
| the cmd_run chain (Cn.cmd_run → Cn-1.cmd_run) | module functions | never reassigned, except C2.cmd_run by 9 (above) | — | no |
| Instance subclasses (C3–C10) | `super().step` | the class cell, not a module attribute | — | no |

campaign_run16.step is the only place that recurses.

## D5: U and the remote duplicates were not under the guard
- **The finding.** campaign_run5's guard sits in Instance.step. The untrained control (campaign_run7.untrained_with)
  and the remote duplicate (campaign_run4.remote_duplicate) call CR.run_child directly, so no guard ever applied to
  them. campaign_run16's docstring and D3_DECISION.md said "U and the duplicates stay guarded". That was wrong.
- **The fix in campaign_run17.**
  - **U:** below the guard, U does not run. It returns ok null and held_for_disk, is listed in stopped_for_disk, and
    writes nothing, so a later run starts it.
  - **The duplicate:** after its wait and before its N0, below the guard, it is held the same way: not completed,
    held_for_disk.

## The template
TEMPLATE_CAMPAIGN_5.json (fbf0c7cc…) is template 4 plus `driver: campaign_run17.py`:
- campaign_run17 refuses templates 1–4;
- campaign_run16 refuses a plan made from template 5 (the key `driver` is not in template 4).
