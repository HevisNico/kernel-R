The final rescan of the exclusion list, versioned before it runs.

- second-scan.block.sh: FREEZE.txt's [block second-scan], unchanged, byte for byte. It is extracted by proof2.py's
  own rule (extract_block.py). This is THE COMMAND.
- rescan.sh wraps the block. Five parts are added, labelled in the script; none of them edits the block:
  PART 0  a check: this copy of the block is byte-identical to the one in FREEZE.txt;
  PART 0a a check: the environment check exactly as [block vars] does it (envcheck_layered4.py check > ENVCHECK.json
          in WORKDIR, refused unless ok is True, with [block vars]'s refusal text); F, the clone's HEAD, printed;
  PART 0b a check: the clone L is clean. Its HEAD is recorded in CLONE_HEAD.txt and git status in CLONE_STATUS.txt;
          the only line allowed is exactly "?? research/circuit/pdk", the untracked PDK link;
  PART 2  a check: a second ls-remote after the fetch equals the first (origin did not move during the scan);
  PART 3  a step: EXCLUDED.json is a byte copy of the block's EXCLUDED_SECOND_SCAN.json, and EXCLUDED_PRINT.txt is
          draw_seeds.py print of it, as the freeze pins them; a failed byte copy is refused with a message.
- The rescan runs from a clean clone of research/layered-campaign-dev, BEFORE the new freeze exists: its output is
  pinned by that freeze. [block vars] describes L as a clone of research/layered-campaign-freeze; here L is the dev
  clone, and PART 0b checks that it is clean.
- Run only under a push hold on the whole repository; the scan takes about 23 GB and 30 minutes.
