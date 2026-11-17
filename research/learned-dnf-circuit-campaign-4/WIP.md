# Campaign 4: the work branch (research/learned-dnf-circuit-campaign-4-wip)

**The frozen implementation is the tree of the commit that wrote this text** (the third refreeze, 2026-11-17, for
amendment 8). Its frozen files are `plan.FROZEN` (`plan.py`), byte for byte; after the freeze, a stage's source
commit may differ from it only as amendment 5 (section 1, item 3) and amendment 6 (section 5) allow, which
`plan.check_after_freeze` checks. It differs from `3156ee4`, the commit the rehearsal's runs used, only in the files
of amendment 8's table (section 2). It supersedes the freezes `c69e21d`, `52e2cc2` and `3156ee4`.

The campaign branch (`research/learned-dnf-circuit-campaign-4`) holds `PREDICTION.md` (commit `1596b36`) and
amendments 1 to 8. Amendments 1 to 5 (commits `c14124f`, `d6a75a9`, `41cf88b`, `a167f3c`, `6c5630f`) are merged into
this branch; amendments 6 to 8 (commits `424f6f9`, `53d50f3`, `d380da6`) are on the campaign branch only, allowed in a
stage's source commit by safeguard ii as later amendments.

## State (2026-11-17)

- **The rehearsal.** Attempt 1 (on `3156ee4`) was interrupted by the director's 2 h task limit, no check evaluated
  (`rehearsal/run-1-interrupted/`). Attempt 2 (on `3156ee4`) ran every stage through the kit and stopped on
  `check.sh`'s audit of M8.lean before writing its record (`rehearsal/run-2/`). Amendment 8: attempt 2 is completed,
  not redone; only its memory stages are rerun, as `MEMD2` and `MEMI2`.
- **Next**, on the owner's return: the completion, once, on this commit; then the rehearsal's report and
  `REHEARSAL.json`. Then, before `BEFORE_M.md`: the procedure for the stages' source commits (built from this commit
  and the allowed files, not from this branch's head, which holds the rehearsal's evidence).
- **Checks before the completion**: `uptime -s`; `grep -qw avx512f /proc/cpuinfo`; the pinned toolchain (ngspice 42 at
  `/usr/bin/ngspice`, SHA-256 `820658…`; Python 3.12.3, `e50d468e…`, with numpy 2.3.5, RECORD `064003bd…`, in
  `/home/user/owner-prep/venv312`; Lean 4.35.0 at `/home/user/lean/bin`; the PDK at `/home/user/campaign/pdk`); a fresh
  clone checked out, detached and clean, at this commit (not this branch's head); attempt 2's work folder at
  `/home/user/rehearsal2` and its meta folder at `/home/user/rehearsal2-meta`, or else
  `restore_attempt.py /home/user/rehearsal2 /home/user/rehearsal2-meta` run from that clone.
- **The completion's start**, from that clone, detached:
  `setsid nohup bash research/learned-dnf-circuit-campaign-4/complete_rehearsal.sh /home/user/rehearsal2 /home/user/rehearsal2-meta WORK_DIR REHEARSAL.json LOG_DIR > /dev/null 2>&1 < /dev/null &`
  (new folders for WORK_DIR and LOG_DIR); then check that it and its uptime recorder are alive outside the
  director's session task.

- `rehearsal/gate-cases-4` and `rehearsal/mirror-mutations-3`: the kernel gate on P0 to P6 and P4' and the mirror
  mutations, under the pinned interpreter and OpenBLAS's SkylakeX kernel; `check.sh` regenerates and compares them.
- `drafts/AMENDMENT_1.md`: the outgoing director's draft, superseded by the pushed `AMENDMENT_1.md`.
