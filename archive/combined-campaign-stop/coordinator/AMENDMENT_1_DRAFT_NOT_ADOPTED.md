> **DRAFT, NOT ADOPTED.** This is the coordinator's working draft of amendment 1 to the combined campaign's
> preregistration, as it stood when the owner stopped the campaign on 2026-11-28 before its official draw.
> It was never pushed or published as an amendment and has no force. Its placeholders ([NEW_FREEZE], ...) were
> never filled. It is kept because its procedure rules (commit identity, root publication, push hold during scans,
> criteria for a go) were drawn from rehearsal 1 and may serve a future preregistration.
> Known stale points at the stop: §3 lists four changed pinned files, but the dev candidate 7fa3693e changed more
> (see FICHE.md); it does not cover the /2 announce, the exact union, check_scan, [block verify-scan] or the
> shared record reader (their wording is in SUIVI.md).


# Combined campaign: amendment 1 to the preregistration

**Status:** draft for the owner's review, not pushed.
- It is to be pushed alone, after the new freeze commit `[NEW_FREEZE]` and before rehearsal 2's announcement.
- The campaign draw is deferred until rehearsal 2 meets the criteria of §6.
- It amends `PREDICTION.md` (`321284af`) and preregistration note 1 (`0e15bb14`). Everything they say that this amendment does not change stays in force.

## 1. Why: rehearsal 1
Rehearsal 1 ran under the freeze `5d02acce`. Its records:
- the announcement `9c3ec1e1` and the draw `f74b75fb` (DRAW.json b8aaefd9);
- 12 roots on `evidence/combined-rehearsal-K01…K12`;
- the frozen analysis, twice, byte-identical: `evidence/combined-rehearsal-analysis` `4fd58425`, RESULTS.json `f7ad053a`.

It counts for no claim. It found:
- **A defect in the remote duplicate.** NOT1_18985's duplicate (K09 → K10) recorded the home seal branch's tip at fetch time (`c644f542`). The original had recorded its own seal commit (`e668cd5e`). The traces, the input, the comparison and the log were identical, yet check_duplicate reported `identical: false` on `/seal_log/commit`. In the campaign this would fail almost every duplicate control. The other two duplicates passed: ANDOR3_87182 K08 → K11, and XOR3_27735 K03 → K12.
- **Two XOR refutations at K0, kept as they are.**
  - XOR3_27735: key 1/0/0, predicted `ssFF`, network `sssFF`. It is reproduced identically on a second computer.
  - XOR3_88529: key 1/1/0, the same pattern.
  - In both, the other words, the four outputs (the XOR table), the cell bits and the skew slots agree with the seal.
  - Their study, the dated note `dev/rehearsal1/NOTE_XOR_K0_2026-11-27.md` and the replay `dev/rehearsal1/replay/`, is exploratory. It changes neither the XOR prediction nor its refutation criterion. `ssFF` against `sssFF` stays a full refutation (§7).
- **Procedural defects**, fixed in §4:
  - the seal commits' identity: 8 seal commits under another identity;
  - the publication of large roots;
  - a machine restart that left one instance not completed;
  - a repository that moved during a scan.

## 2. A correction to the verification statement
`PREDICTION.md` (`321284af`) says the independent defect suite (51 cases) was rerun on the frozen code. That was inaccurate.
- The recorded 51/51 is from `8bac22cc` (`dev/equiv/DEFECTS_R_AFTER.json`), before the final exclusion-list scan `340e1c6c`.
- A run on the frozen revision `5d02acce` returned 34/51 (`dev/rehearsal1/suite_at_5d02acce/`, recorded at `a22f6f2e`).
- Of the 17 failures, two failed directly on the old demonstration seeds, which the final scan had added to the exclusion list:
  - `standin_draw_valid`, the control, which expected `not_run` entries for 65418 and 69364;
  - `beacon_canonical`, which expected the draw to give those seeds.
- The other 15 depend on that control, so their verdicts in that run are not established:
  - 14 mutation cases, each refused with its own check's message;
  - `standin_plans_from_command`, which exited 0 and was marked gated.
- The suite now has a stable reference case (fixed inputs, seeds established independently and hard-coded) and an integration case on the pinned list, in which each dependent case must reach its own check.
- It is rerun on the final candidate after the new scan: `[SUITE_RESULT]` at `[SUITE_RECORD]`.

## 3. What the new freeze changes
The new freeze `[NEW_FREEZE]` is a plain push on `research/layered-campaign-freeze`, on top of `5d02acce`, never forced, so the push of `5d02acce` stays readable for rehearsal 1. Its pinned files differ from `5d02acce` in these four only:
- **`campaign.py`: the remote duplicate.**
  - It finds the commit that introduced its instance's SEALS.txt line: the earliest commit of the home branch's first-parent history that holds the exact line.
  - It fetches and verifies the seal folder and its manifest at that commit, before its N0.
  - It records that commit as `seal_log.commit`, and the tip it read apart.
  - If there is no such commit, or the seal does not verify there, it refuses and is not completed.
  - `seal_log.commit` stays in check_duplicate's comparison.
  - A regression test reproduces K09's case: two later seals are pushed before the fetch, and the duplicate must name the first commit and be IDENTICAL.
- **`analysis.py`: the two rehearsals.**
  - Rehearsal 2's announcement and result branches are new and single-use: `evidence/combined-rehearsal2-draw` and `evidence/combined-rehearsal2-draw-result`.
  - Rehearsal 1 is pinned as published (`f74b75fb`, DRAW.json b8aaefd9, list abdc38e8). It is checked against its own freeze `5d02acce` and its own list.
  - Rehearsal mode requires rehearsal 1's 18 seeds and 72 noise seeds in rehearsal 2's list.
  - Campaign mode requires both rehearsals' 36 seeds and 144 noise seeds in the campaign's list, and both announcements earlier than the campaign's.
  - Every other rule is unchanged.
- **`EXCLUDED.json` and `EXCLUDED_PRINT.txt`: rescanned at the new freeze** (`[NEW_LIST_SHA]`, `[NEW_COUNT]` integers).

The freeze criterion of `PREDICTION.md` is amended accordingly: the driver closure is that of `5d02acce` except `campaign.py`, for the reason above.

## 4. Procedures for rehearsal 2 and the campaign
These rules bind rehearsal 2 and the campaign. They are not in the frozen code.
- **Identity.**
  - Every machine sets `GIT_AUTHOR_NAME`, `GIT_AUTHOR_EMAIL`, `GIT_COMMITTER_NAME` and `GIT_COMMITTER_EMAIL` to the owner's identity, taken from `main`, in the shell of every `launch` and every `resume`.
  - It checks them in the driver's environment before waiting.
  - A seal commit under another identity is reported, never rewritten.
- **Machine set-up.**
  - Fetch by branch name only, never a full clone.
  - `research/circuit/pdk` is linked in all three trees.
  - Every output stays outside the git trees.
- **A restart.** The driver is resumed (`campaign.py resume`), never relaunched. A step found running is recorded "interrupted", and its instance is not completed. This is the rule already applied to ANDOR3_66680 in rehearsal 1.
- **Publishing a root.** Each root goes on its own new branch, from a copy; OUTROOT stays untouched until the analysis has run.
  - Remove `.seal_log_work/.git` in the copy, so the seal files stay as plain files.
  - Every file over 50,000,000 bytes is split into `.transport-part-NNN` with a line in `TRANSPORT_SPLIT.txt` (sha256, size, parts, path), with the concatenation checked before removal, IF it is any of these:
    - listed in a `SHA256SUMS*`;
    - the N0 raw of a `keep_raw` instance;
    - the N0 raw of a `DUPX_` folder (check_duplicate reads both).
  - Otherwise it is left out, with a line in `NOT_PUBLISHED.txt`, and kept on the machine.
  - A push is under 1 GB: the first is the creating push, and later plain pushes add parts.
  - Before the analysis, every split file is restored and checked against its sha256 and size.
- **Push hold.** Every branch of the repository is held still during every exclusion-list scan, which refuses if a branch moves.

## 5. Rehearsal 2
- **Size and runs.** 6/6/6 over the 12 machines, under `[NEW_FREEZE]`, with the blocks of its `FREEZE.txt`. Its announcement and result go on the branches of §3. Its roots go on `evidence/combined-rehearsal2-K01…K12`.
- **Its exclusion list.** The new freeze's scan output plus rehearsal 1's 18 seeds and 72 noise seeds, built and checked by the FREEZE.txt blocks. Its sha is written in its announcement.
- **The campaign's list.** The second scan's output plus both rehearsals' seeds and noise seeds, by the same three steps.

## 6. The go for the campaign draw
The owner gives the go for the campaign draw once rehearsal 2 meets every criterion below. None of them depends on how an XOR instance turns out.
1. Its draw is checked in full by the analysis.
2. Every instance is sealed before its network run, with the seal's push time recorded by GitHub.
3. The analysis runs twice with byte-identical output. Every not completed instance and every deviation is listed and explained.
4. The three cross-machine duplicates are verified: `identical: true` and `comparison.equals_original: true`. The late-fetch case is covered by the regression test of §3, and by rehearsal 2 itself wherever a home pushes another seal before its duplicate fetches.
5. Every seal commit carries the owner's identity.
6. Every root is published under §4 and restored byte for byte before the analysis.

## 7. What does not change
- The XOR prediction, every prediction, and the refutation criterion: one differing letter, cell bit or output refutes, even when the final table is right.
- The sizes 60/32/37, the thresholds and the verdict rules of §4 of `PREDICTION.md`.
- §5's rule for fewer than 12 machines and note 1.
- A timing rule drawn from the replay would be a new prediction. It would need a bound on the arrival times known before a run, a measured guarantee over that range, and a prospective test on new development seeds before any freeze.
