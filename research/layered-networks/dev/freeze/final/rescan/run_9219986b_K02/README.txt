The final rescan of the exclusion list: run record (small outputs only).

Machine K02, Claude Code session session_01TzF7ZUzWF9YA9phr9ZxG8C (runner role), under a push hold on the whole repo.
Start 2026-11-27T20:52:08Z, end 2026-11-27T21:19:28Z, rc=0.

Command line (from ~/runner, with GIT_AUTHOR_*/GIT_COMMITTER_* set from main's author):
  nohup bash kernel-R/research/layered-networks/dev/freeze/final/rescan/rescan.sh ~/runner/kernel-R/research/layered-networks ~/runner/venv/bin/python ~/runner/scan_final > ~/runner/scan_final.log 2>&1; echo "rc=$?" >> ~/runner/scan_final.log
The clone ~/runner/kernel-R was at research/layered-campaign-dev 9219986b09be4c7ec8660c591ddf78f67d77fbeb (CLONE_HEAD.txt),
clean apart from the research/circuit/pdk link (CLONE_STATUS.txt). WORKDIR: ~/runner/scan_final.

Files here: scan_final.log (the complete rescan.sh output), CLONE_HEAD.txt, CLONE_STATUS.txt, ENVCHECK.json,
SCAN_LSREMOTE.txt, SCAN_BRANCHES.txt, SCAN_EXPECTED.txt, SCAN_FETCHED.txt, SCAN_LSREMOTE_AFTER.txt, SCANREPO_REMOVED.txt,
this README.txt, and SHA256SUMS (every file here except itself).
Not published: the SCAN_BATCH_* files (intermediate batch lists, the split of SCAN_BRANCHES.txt in tens), and scanrepo/,
the scan repository (22 GB), which was removed at 2026-11-27T22:11:33Z with the owner's go (SCANREPO_REMOVED.txt).

The scan's outputs are not copied here: they are pinned at e38b4df3 and are byte-equal to these run outputs:
  EXCLUDED_SECOND_SCAN.json  sha256 a3a76e1a8552fa054faf616faee0771669432b19d3aa1722a9988e7029cb8940  (= research/layered-networks/EXCLUDED.json)
  EXCLUDED.json              sha256 a3a76e1a8552fa054faf616faee0771669432b19d3aa1722a9988e7029cb8940  (= research/layered-networks/EXCLUDED.json)
  EXCLUDED_PRINT.txt         sha256 efc8d463affe0f24b6f3b80a57ea7acaac74e0c428c69c15f900434f685cbca1  (= research/layered-networks/EXCLUDED_PRINT.txt)
