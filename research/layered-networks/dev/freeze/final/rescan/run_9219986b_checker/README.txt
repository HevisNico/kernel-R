The independent checker's rescan of the exclusion list, at 9219986b (2026-11-27). A second, independent run of
dev/freeze/final/rescan/rescan.sh, made in another container from another clean clone, to compare byte for byte
with the record's rescan.

Who: Claude Code session session_01TzF7ZVyj98nLkaSRd4xWXB (the checker), on the owner's approval relayed by the
coordinator.

Clone: a new clean clone, research/layered-campaign-dev fetched by name, checked out at
9219986b09be4c7ec8660c591ddf78f67d77fbeb, research/circuit/pdk linked to the SKY130 PDK at 1232782c; git status
--porcelain --untracked-files=all was exactly "?? research/circuit/pdk".

Run: start 2026-11-27T21:27:20Z, end 2026-11-27T21:53:21Z (1561 s), rc=0. The command, run from L:
  L=/home/user/rescan_clone/research/layered-networks
  cd "$L" && PATH=$HOME/.elan/bin:$PATH bash "$L/dev/freeze/final/rescan/rescan.sh" "$L" /opt/layered-venv/bin/python /home/user/rescan_work
(/opt/layered-venv/bin/python is the pinned Python 3.13.18 with numpy 2.3.5 and py_ecc 8.0.0; ENVCHECK.json is its
envcheck_layered4 check.) Its stdout and stderr are rescan.log, followed by the rc and the end time and elapsed
seconds that the outer shell appended.
WORKDIR: /home/user/rescan_work.

The failed first launch: rescan_attempt0_no_time_binary.log. At 2026-11-27T21:27:06Z the same command was launched
prefixed by /usr/bin/time -v, which is not installed in this container: bash exited 127 before rescan.sh started, the
WORKDIR was not created, and nothing was scanned. The run above was then launched without that prefix.

Files here: rescan.log; CLONE_HEAD.txt, CLONE_STATUS.txt, ENVCHECK.json (written by rescan.sh PART 0a/0b);
SCAN_LSREMOTE.txt, SCAN_BRANCHES.txt, SCAN_EXPECTED.txt, SCAN_FETCHED.txt (written by [block second-scan]);
SCAN_LSREMOTE_AFTER.txt (rescan.sh PART 2); rescan_attempt0_no_time_binary.log; SHA256SUMS (every file here except
itself). All are copied unchanged from the WORKDIR.

Not published here:
- scanrepo/ (the scan repository, about 22 GB) is not published; it is kept in the checker's container.
- The list files are not copied here; they are the record's pinned files, byte for byte (checked with cmp against
  research/layered-networks/EXCLUDED.json and EXCLUDED_PRINT.txt at e38b4df39ee3dac881951e0dee5bd8b3362c70db):
    EXCLUDED_SECOND_SCAN.json  sha256 a3a76e1a8552fa054faf616faee0771669432b19d3aa1722a9988e7029cb8940
    EXCLUDED.json              sha256 a3a76e1a8552fa054faf616faee0771669432b19d3aa1722a9988e7029cb8940
    EXCLUDED_PRINT.txt         sha256 efc8d463affe0f24b6f3b80a57ea7acaac74e0c428c69c15f900434f685cbca1
  (16333 integers, 286 refs, seeds_sha256 1e8e0456f8668de9a6d43ae1ef62ef7dd45dd1e53c49261d33a1156ef02d25fb)
