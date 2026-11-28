DESIGN NOTE (l): the independent reproduction of the second scan, and where its record is published (FOR THE OWNER)

What it guards against. Level 1 (check_scan) proves the scan file is consistent in itself, but a canonical scan with
3 arbitrary integers added and count/seeds_sha256 recomputed is just as consistent (test verify_scan shows check_scan
accepting it). Only rerunning the scan can tell. So the scan is reproduced on a SECOND machine before the announce,
and the announce refuses unless that reproduction has the same bytes.

The procedure (ORDER 3 step (3b), written into FREEZE.txt):
1. On the second machine: its own clean clone of the freeze and its own pinned Python ([block vars] there), a new
   working folder outside any clone. Only ONE file comes from the first machine: its EXCLUDED_SECOND_SCAN.json, saved
   as SCAN_TO_VERIFY.json. The verifier fetches everything else itself.
2. [block second-scan], verbatim, in that folder: the verifier's own scan, from its own ls-remote and its own fetch of
   every branch by name.
3. [block verify-scan], verbatim, in that folder:
   - it takes its OWN `git ls-remote --heads` NOW (VERIFY_LSREMOTE.txt) and compares it with the refs SCAN_TO_VERIFY.json
     records, by name AND tip (refs/remotes/origin/X against refs/heads/X): a branch missing, extra or at another tip
     refuses; the scan's HEAD must be main's tip;
   - SCAN_TO_VERIFY.json must pass check_scan (level 1);
   - the verifier's reproduction must equal SCAN_TO_VERIFY.json byte for byte;
   - it prints "... scan_sha256 <the scan's> VS <the reproduction's>". VS is KEPT in [block vars-campaign].
   The comparison is analysis.verify_scan (pinned, so the block's logic is frozen with the analysis).
4. Then, and only then, the same block publishes the record: one creating push of one commit to the single-use
   branch evidence/combined-scan-verify, holding VERIFY.txt (the printed result), VERIFY_LSREMOTE.txt (its own
   inventory) and SCAN_LSREMOTE.txt (the inventory of its own scan). Never pushed again, never forced, never deleted,
   owner identity, the same guards as the announce and result branches (refuses if the branch exists, not an orphan,
   inside a clone, identity not main's).
5. The campaign [block announce] refuses, with no commit and no push, unless VS equals HS (VS empty or different: the
   message names both). In rehearsal mode S, HS and VS must be empty.

Why a separate branch, created before the announce:
- The record becomes public BEFORE the announce fixes the round, so the reproduction cannot be arranged after the
  beacon is known. GitHub's push time of evidence/combined-scan-verify (its branch_creation) is earlier than the
  announce's; anyone can check that ordering in the activity API, like the announce's own.
- It does not touch the announce: the announce commit stays exactly DRAW_ANNOUNCE.txt + EXCLUDED_PUBLISHED.json +
  EXCLUDED_SECOND_SCAN.json, one push.
- It changes no list: the scan has already run, so the new branch is not in the scan (and cannot be).

What it does NOT do yet (possible follow-ups, not implemented):
- analysis.py does not read evidence/combined-scan-verify. It could, in campaign mode: VERIFY.txt naming the announced
  second_scan_sha256 as VS, and its branch_creation before the announce's. Today VS is checked by the announce block
  only, and the record is there for anyone to audit.
- The "second machine" is a procedure. Nothing in the files proves it was a different machine; the record shows it
  was an independent run (its own ls-remote and fetch).
- The push hold must hold between the scan and the verification. Any push to any branch in between makes the
  inventory differ, and the verification refuses. That is the intended behaviour, but it costs a rerun of both scans.
- Each scan is about 25 GB (the tips of every evidence branch), so the second machine needs the same disk.

proof2.py runs it: step 08a is a second [block second-scan] in the folder verify/ (a second full scan), and step 08b
is [block verify-scan]. Its push is twinned to the local twin, and its ls-remote calls read GitHub as written. VS is
filled from 08b's printed line. A new negative step 09a (announce with VS = 000…) must refuse with no commit. The
owner-identity step now expects 5 refs on the twin. proof2.py itself has not been run (it needs about 50 GB and drand).
Its twins were dry-checked: each applies exactly once to the current blocks.
