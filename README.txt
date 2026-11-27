LOCAL RECORDS OF REHEARSAL 1 AND THE SECOND FREEZE CANDIDATE (copied 2026-11-27 by the stage-D worker)

These files existed only in the stage-D worker's container. They are copied here unchanged, so that they outlive it.
The source folder was the worker's scratchpad:
  S = /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad
Nothing was moved or deleted at the source.

INTEGRITY
- SHA256SUMS covers every original file: 147 files, each by its whole-file sha256. It was made after the copy, and each
  line was checked against the source file.
- Two files are not in SHA256SUMS because they are new: this README.txt and TRANSPORT_SPLIT.txt.
- One file is over 50,000,000 bytes: trace_study/extract_88529_trace.raw (64,525,038 bytes). It is split into
  .transport-part-000 and -001; see TRANSPORT_SPLIT.txt. To rebuild it:
    cat trace_study/extract_88529_trace.raw.transport-part-* > trace_study/extract_88529_trace.raw
  The rebuilt file must match its line in SHA256SUMS: 9538f0ea….
- There are no symlinks and no nested git repositories.
- The six replay folders held a "pdk" symlink to the PDK, at the pinned commit 1232782c. It is left out.

CONTENTS
analysis/OUT1/, analysis/OUT2/
  From S/rehearsal/analysis/OUT1 and OUT2. These are the two full runs of analysis.py on rehearsal 1: RESULTS.json,
  SHA256SUMS, activity/, kernel_build/. The two runs are byte-identical: the same RESULTS.json and the same
  SHA256SUMS. Each folder's own SHA256SUMS checks.
  Backs: the rehearsal-1 analysis published on evidence/combined-rehearsal-analysis (4fd58425).
  Not copied: the roots (R/, about 6.2 GB), which can be fetched again from origin.

replay/r_<instance>_case<k>/ and replay/r_<instance>_case<k>.log
  From S/rehearsal/replay. These are TASK 3, the replay of the third symbol: 2 instances x 3 cases.
  Each folder holds the deck input.spice, blocks.spice, the ngspice session.log, replay.json and the binary
  replay.raw. The six raws' sha256 are the ones in the published runs/RAW_SHA256SUMS.txt.
  Backs: research/layered-campaign-dev 9618a665, dev/rehearsal1/replay/ (REPLAY_REPORT.md, REPLAY_TABLE.*).

trace_study/
  From S/rehearsal/trace_study: extract_88529_trace.raw (split; see above), study.json, study2.json, study2.out,
  NOTES.txt.
  Backs: research/layered-campaign-dev df2bb840, dev/rehearsal1/trace_study/.

equiv_a/at_8b5c9f95/EQUIV_A.json, equiv_a/at_5d02acce/EQUIV_A.json and equiv_a/at_5d02acce/eqa_frz.log
  - From S/eqa/EQUIV_A.json (the (a) run on the second candidate's code, 8b5c9f95).
  - From S/eqa_frz/EQUIV_A.json and S/eqa_frz.log (the same run on the first freeze, 5d02acce).
  The two files say which tree they ran on only through their source folder names, as the worker recorded them. The
  JSON itself does not name the commit.
  Each run holds 24 of 24 cases: K01..K08 x 3 scenarios, all "identical". The two JSON files are byte-identical.
  Backs: the claim "(a) 24/24 at 8b5c9f95, byte-identical to (a) at 5d02acce".

proof2_P8_8b5c9f95/log/
  From S/frz/f3/P8/log only: SUMMARY.json, SELFTEST.json, RUN.out, TWINS.md, blocks_extracted.json, and each step's
  .block.sh and .out. No twin repository and no other part of P8 is copied.
  THIS IS A NOT-GREEN RUN: proof2 exit code 1.
  - Steps 01..04 passed. The four negative steps 04a..04d refused as expected. The runner self-test passed 6 of 6.
  - Step 05 (second-scan) refused at its own guard ("the fetched refs are not the ls-remote's"):
    research/layered-campaign-dev moved from 8b5c9f95 to acf61c3b during the scan.
  - Steps 06..14 were not run.
  Backs: the report that proof2 at 8b5c9f95 ended exit 1 at the scan guard. It backs no pass.

test_c_f46c49e0/TEST_C_f46c49e0.json
  From S/tcfull/WD/TEST_C.json (kept as S/tcfull/TEST_C_f46c49e0.json). This is the full test (c), tests/test_campaign.py,
  run on research/layered-campaign-dev f46c49e0.
  RESULT: 28 of 29 PASS, exit 1. The failing case is analysis_refuses: its expected refusal text was stale, because
  the pins then matched the tree. It was fixed in 0ce2d1af, and that fix was rerun on its own only, not in a full (c).
  No full (c) on the final code exists here.
