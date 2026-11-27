The final rescan of the exclusion list, versioned before it runs.

- second-scan.block.sh: FREEZE.txt's [block second-scan], unchanged, byte for byte. It is extracted by proof2.py's
  own rule (extract_block.py). This is THE COMMAND.
- rescan.sh wraps the block. Three parts are added, labelled in the script; none of them edits the block:
  PART 0  a check: this copy of the block is byte-identical to the one in FREEZE.txt;
  PART 2  a check: a second ls-remote after the fetch equals the first (origin did not move during the scan);
  PART 3  a step: EXCLUDED.json is a byte copy of the block's EXCLUDED_SECOND_SCAN.json, and EXCLUDED_PRINT.txt is
          draw_seeds.py print of it, as the freeze pins them.
- Run only under a push hold on the whole repository; the scan takes about 23 GB and 30 minutes.
