# The final freeze proof (dev/freeze/final)

**The freeze candidate:** research/layered-campaign-dev at 0b33340d16cbac3edc00ffae7b6416dddfbdb013. Its pinned
files are those of 340e1c6c, which has the last exclusion scan and the regenerated pins. 0b33340d adds only
FREEZE.txt and a note in dev/freeze/PROOF.md, and neither file is pinned.

- FREEZE_PINS.json: sha256 6baf8a51d4f4aca35d4789b1865da7692affca0106690f163b00d4e68f7e84f1, 114 files.
- EXCLUDED.json: sha256 abdc38e8c3dee532ecb67097951e3c7d4f8c3bb1e22d3a30a91a11dceb5d680c.
  - seeds_sha256 d9975dee4f80fb75ea5fb67d3d0301bbae2274b0857fc7d44dc216f1c67afbc6.
  - 15741 integers and 256 refs, an excluded fraction of 6.86 %.

**How it was made.** `proof.sh WORK 0b33340d… <pinned Python 3.13.18> <this folder>` ran on a clean clone:
- fetched by branch name;
- with the worktrees at kit_commit d599300d and noise_commit 458bc7a6;
- with nothing launched and nothing pushed.

Every command is in log/*.txt with its full output and its exit status. The clone stayed clean: `git status
--porcelain --untracked-files=all` prints 0 after steps 3 and 6.

To rerun it: `bash proof.sh <new folder> 0b33340d16cbac3edc00ffae7b6416dddfbdb013 <python> <this folder>`. It takes
about 30 s and needs network access to GitHub.

**What is real and what stands in:**
- **Real:**
  - the clone's files;
  - the pinned EXCLUDED.json;
  - the last scan's output. That output is the pinned EXCLUDED.json itself, unedited, used as EXCLUDED_SECOND_SCAN.json.
- **Stand-in:**
  - The **rehearsal draw** does not exist yet. Quicknet's round 1000000, as published, stands in for it. inputs/standin.py builds it:
    - the signature verifies against the pinned key;
    - 6/6/6 over the pinned EXCLUDED.json;
    - announce push_utc 600 s before the round;
    - announce commit 0×40.
  - The same round at 60/32/37 serves only to make 12 plans for step 3.

The **second scan** of FREEZE.txt's ORDER step 3 has not happened either. It comes after the rehearsal. Here, the
last scan stands in for its output.

## Owner's criterion 1: the final commands on the real files

1. **The pins regeneration (log/01_pins.txt).**
   - Commands: closure2.py over the nine entries gives 58 files in the closure. make_pins3.py then runs on the clone, with the base string read from its FREEZE_PINS.json.
   - The result is **IDENTICAL**, byte for byte (`cmp`), to the clone's FREEZE_PINS.json.
   - Against the pins of 483f90c5, the commit before:
     - added [], removed [];
     - changed: exactly the four stale code pins (analysis.py, beacon_verify.py, draw_seeds.py, plan_split.py), EXCLUDED.json and EXCLUDED_PRINT.txt;
     - the groups and the tools are the same.
2. **Option (A), the three steps of FREEZE.txt ORDER 3 (log/05_option_A.txt).** proof.sh extracts them verbatim from the clone's FREEZE.txt (inputs/step12.sh, inputs/step3.sh). FREEZE.txt's `python` is the pinned Python.
   - **(1)+(2), real scan output plus the stand-in rehearsal draw:**
     - It prints "18 rehearsal seeds, 72 noise seeds; 15831 integers".
     - seeds_sha256 ae9e2aa4f5d4110bee4df51cc5ea9fe18955b5ff73f319cfe73a2e87801cb03d.
     - Against the scan: 90 integers added, none removed. The only key added is "added". The refs and the rule are kept.
   - **(3) verbatim: refused, exit 1.** The rehearsal's announce cannot be read from GitHub: "couldn't find remote ref refs/heads/evidence/combined-rehearsal-draw".
     - This is the expected refusal: the stand-in has no announce on GitHub, and that branch must not exist before the rehearsal.
   - **(3) offline (inputs/step3_offline.py), the same checks:**
     - check_draw runs with offline=True and the stand-in's announce file;
     - check_rehearsal_seeds runs with strict=False and rehearsal_announce=;
     - the draw record prints with recomputed true and signature_verified true;
     - then "**the list is right** 18 72 fraction 0.0688 sha256 efb15ecb60f469e008932575f7d16901cc87d7126fe069f4df929a0e3c134b0f", exit 0.

     The final list is in inputs/EXCLUDED_SECOND_from_standin.json. It comes from the stand-in and is not a campaign list.
3. **The pre-announce check, DRAW_ANNOUNCE verbatim (log/06_preannounce.txt, inputs/preannounce.sh).**
   - Both branches are absent from GitHub: `git ls-remote` prints 0 lines for evidence/combined-rehearsal-draw and for evidence/combined-draw.
   - **Rehearsal:** X = the pinned EXCLUDED.json at 6/6/6 gives "announce ok". Its DRAW_ANNOUNCE.txt carries excluded_sha256 abdc38e8….
   - **Campaign:** X = EXCLUDED_SECOND.json of step 2 at 60/32/37 gives "announce ok", with excluded_sha256 efb15ecb….
   - No commit, no push.

## Owner's criterion 2: the driver accepts the regenerated pins

- **campaign.py check campaign campaign_template.json PLAN_K01..K12 (log/03_check_campaign.txt):**
  - all 12 exit 0, each with ok true, tree_clean true, mismatched [] and not_pinned [];
  - pinned_files 114, pins_sha256 6baf8a51…, tree_commit 0b33340d;
  - the full JSON of K01 is log/03_check_campaign_K01.json.
- **The plans:** plan_split3.py on the stand-in at 60/32/37 (DRAW_CAMPAIGN_SIZES.json) over the frozen template made PLAN_K01..K12.
- **analysis.py rehearsal, past the pins gate (log/04_analysis_rehearsal.txt).** The root is a TEST root, evidence/devtest-run2-K02's out_K02 at 41f053ff. Both runs use times=github and draw=DRAW_REHEARSAL.json.
  - With controls set to the noise worktree's top folder, it refuses: "rehearsal mode: controls must be the noise tree at 458bc7a6d763 (…/noise/research/layered-networks)".
  - With controls set to that folder, it refuses: "roots not run by this campaign.py on the frozen template in campaign mode: ['root_1']".
    - The root is a TEST root, and the rehearsal's drivers run in campaign mode on the frozen template.
  - Both refusals come after these gates, all passed, in main's order:
    - the -O check;
    - the arguments;
    - the roots and OUTDIR;
    - the pins gate (CP.pins_refusal);
    - the pinned-thresholds gate;
    - times=github;
    - the clean noise worktree at noise_commit.
  - The draw is read after the roots' drivers are checked, so a real rehearsal root is needed to go further.
- **The same TEST root in campaign mode** gives the same refusal, after the same gates.

## Records of the attempt

proof.sh first ran with an extraction bug: it read step (3)'s prose instead of its command, and bash reported a syntax error. The bug was fixed and proof.sh was rerun from a fresh clone. These logs are from that second run. The first run's other logs are the same once its folder name is replaced (diffed).
