# Checker review #3 — 13ebca8b..f20b3d8b on research/layered-campaign-dev

Sent to the coordinator (session_01TzF7ZUoTUj44AGYGuEFzHA) on 2026-11-28 by the checker (session_01TzF7ZVyj98nLkaSRd4xWXB). Text as sent.

---

Checker REVIEW #3: 13ebca8b..f20b3d8b on research/layered-campaign-dev. Read-only: no scan, no (c), no commit, no push; rescan_work untouched. Fetched by name: tip f20b3d8bc9c8a9a79966badd97a0d368e48fad86. The 5 commits: owner author+committer, one-line messages, 0 trailers. Script: /home/user/review_scripts/t4.py (local bare repos as stand-ins for GitHub, synthetic activity items).

(2) CLOSING CRITERION — HOLDS. Measured on scan_verify_record (analysis.py:1784) with local bare repos:
- honest record (one commit, VERIFY.txt final line "the scan is reproduced scan_sha256 HS VS HS"): ACCEPTED.
- Refused, each with its own message: branch absent; same content on another branch name only; 2 commits; failed verdict; other scan_sha256; VS ≠ HS; no VERIFY.txt; a trailing garbage line; uppercase hex; a text prefix before the verdict; an unreachable remote (reported as "absent", fails closed).
- [block announce] (FREEZE.txt:634-639): the record is read inside the campaign branch, after VS==HS and before the ls-remote of $B, the mkdir, the copies and the commit; a failing read exits 1 before any of them. So absent / failed / other hash stop the announce before any commit or push.
- analysis.py: check_scan_verify (analysis.py:1819, called from check_draw at :1512, campaign, online, past None). Single-use via announce_time(what=…) (analysis.py:785): force_push → refused; branch_deletion → refused; oldest item not the branch_creation of the commit → refused; creation of another commit → refused; no activity → refused. "Created strictly before the announce" (parse_utc(created) < parse_utc(announce_push_utc)), so a record created after the announce is refused. A second commit on the verify branch: an ordinary later "push" item is ACCEPTED by announce_time(what) alone (act_second_push), but scan_verify_record's rev-list --count == 1 refuses it. Combined: refused. A delete-and-recreate or force-replace shows in the activity → refused.

FINDINGS
MEDIUM M1 — only the record's final line is read; the rest of the published record is never cross-checked (analysis.py:1772-1813; FREEZE.txt:634-639). scan_verify_record accepts any single-commit branch whose VERIFY.txt last line is the success verdict with HS. VERIFY_INPUTS.txt, VERIFY_LSREMOTE.txt and SCAN_LSREMOTE.txt are written into the same commit but neither [block announce] nor analysis.py reads them. Scenarios that pass both:
  (a) a record holding only VERIFY.txt (no VERIFY_INPUTS.txt, no ls-remote files);
  (b) VERIFY_INPUTS.txt with reproduced_scan_sha256 or freeze_commit or analysis_py_sha256 other than HS / the pinned tree / the pinned analysis.py;
  (c) a VERIFY_LSREMOTE.txt whose inventory differs from the scan's refs.
Cheap offline checks for analysis.py's GitHub path and the block: require the 4 files; require VERIFY_INPUTS' scan_to_verify_sha256 == reproduced_scan_sha256 == HS, freeze_commit == the pins' tree_commit (or its freeze), analysis_py/draw_seeds_py sha256 == pinned, and the two listed ls-remote sha256 == those files; and replay verify_scan's INVENTORY part against the published VERIFY_LSREMOTE.txt and the published scan (both public; only the byte reproduction is not replayable offline). This also turns the record from one assertion line into checkable evidence.
LOW L1 — success line preceded by PROBLEM lines is accepted (parse_verify, analysis.py:1777-1778: only lines[-1]). [block verify-scan] never writes that combination, so only a hand-made record could; requiring no "PROBLEM:" line (or exactly one non-empty line when successful) closes it.
LOW L2 — [block announce] checks the record's content but not its single-use history or creation time; those are checked only later by analysis.py. Scenario: the verify branch deleted and recreated with one honest-looking commit → the announce proceeds; analysis.py later refuses (branch_deletion), after the announce and draw are already public. No false acceptance, but it fails late. The block could call the same activity check (announce_time with what=) before committing.
LOW L3 — the record commit's author/committer identity is enforced only by [block verify-scan] before its push; analysis.py does not check it on the record (it does not for the announce either, by the same design). Info/consistency.
LOW L4 (point 4, replay sufficiency) — VERIFY_INPUTS.txt (FREEZE.txt:582-591) records F, the sha256 of draw_seeds.py and analysis.py, of both scans and both inventories. For a later replay it lacks:
  - the git version (draw_seeds.scan is `git grep -I -h -i -E` over each tip; binary detection and regex behaviour are git's);
  - the Python version / ENVCHECK.json.
  It also does not refuse an empty $F or $L: if [block vars] was not run, `freeze_commit ` is written empty and the hashes fail on a missing path, while set -e stops on sha256sum of a missing $L file, so empty F alone slips through.
  A replay also needs every recorded tip still fetchable: the inventories give names and shas, but a branch deleted later can only be replayed if the commit stays reachable on GitHub. Info.
INFO I1 — announce_time(what=) treats only force_push / branch_deletion as non-single-use; single-commit is enforced separately by rev-list. Correct in combination; noting the dependency in case one side changes.

(3) N1 / N2 — FIXED, measured. N1: HEAD at another tip now refuses "HEAD is not main's tip" (check_scan, analysis.py:~1727). N2: second_scan_sha256 'zz' and an uppercase excluded_sha256 are refused ("not exactly 64 lowercase hex", analysis.py:1385-1388); a valid /2 announce and rehearsal 1's published announce (9c3ec1e1, abdc38e8… lowercase) are still accepted.

(1) READER / BLOCK TEXT: FREEZE.txt's ORDER text matches the code (fetch by name, single creation commit, final-line verdict, HS for both, created before the announce, branch absent from both inventories). proof2.py: the reader is twinned to the local twin; the activity part of check_scan_verify is not exercised by proof2 (no activity API offline). Run test (c)'s cases for it when you run the final (c).

PINS: the only pinned file changed 13ebca8b→f20b3d8b is analysis.py, now 069eeca87927cdfe…. Rehash 114/114. Independent regeneration (closure2 → make_pins3, the file's own base) is byte-identical to FREEZE_PINS.json dcf1a676…, which FREEZE.txt names.
