DESIGN NOTE (E): the second scan's raw output made public (FOR THE OWNER'S APPROVAL)

Problem. Under (D), analysis.py campaign rebuilds the campaign's list from second_scan= and the two verified draws, so
anyone rerunning the analysis needs EXCLUDED_SECOND_SCAN.json. Today it exists only in the coordinator's working folder.

The change (implemented; the campaign announce only, rehearsal 2's announce is byte for byte as before):
1. The campaign announce commit on evidence/combined-draw carries three files instead of two: DRAW_ANNOUNCE.txt,
   EXCLUDED_PUBLISHED.json (= EXCLUDED_SECOND.json, as now) and EXCLUDED_SECOND_SCAN.json (the raw scan output,
   unedited). It is still one commit and one creating push, so the scan is published at the same moment as the list,
   before the round exists.
2. DRAW_ANNOUNCE.txt gets a fifth line, in campaign mode only:
       format layered-draw-announce/1
       mode campaign
       excluded_sha256 <H>
       second_scan_sha256 <HS>
       sizes NOT1=60 ANDOR3=32 XOR3=37
   analysis.parse_announce now requires that line if and only if mode is campaign (a campaign announce without it,
   or a rehearsal/test announce with it, is refused). The format string stays layered-draw-announce/1: rehearsal 1's
   published announce, rehearsal 2's and every test announce are four lines and still parse. (Alternative: bump to
   /2 for the campaign. I did not, to leave the other announces' format untouched; easy to change if preferred.)
3. HS is KEPT like H: [block check-list] now prints "... sha256 <H> scan_sha256 <HS>", and [block vars-campaign]
   takes S=EXCLUDED_SECOND_SCAN.json and HS=<...>. [block vars-rehearsal] sets S= HS= (empty).
4. [block announce], campaign only: S made absolute before any cd; HS must be 64 characters; the copy of S must have
   sha256 HS (else "REFUSED ... no commit, no push"); the 5-line DRAW_ANNOUNCE.txt; the python check additionally
   requires second_scan_sha256 == HS == the copy's sha256 and the scan a superset of the freeze's EXCLUDED.json;
   git add also adds EXCLUDED_SECOND_SCAN.json. In rehearsal mode a non-empty S or HS refuses; the 4-line file and
   the python check are as before (plus "no second_scan_sha256 line").
5. analysis.py campaign: check_draw records second_scan_sha256 from the announce read on GitHub;
   check_rehearsal_seeds refuses a second_scan= whose sha256 is not that one ("second_scan= has sha256 ..., not the
   second_scan_sha256 ... the campaign announce names"). So the analysis can only be run on the published scan.

What this binds. The announce (on GitHub, before the round) fixes both H and HS; the analysis checks
second_scan= against HS, excluded= against H, and excluded= == campaign_list(second_scan=, the two verified draws)
byte for byte. Anyone can fetch evidence/combined-draw and rerun it; anyone can also rerun the scan itself
(draw_seeds.py scan at the refs and tips the scan file names) and compare its bytes with the published one.

Size: EXCLUDED.json today is 16333 integers (138 KB); the scan output is the same kind of file.

Not changed: the [block draw] step 5 (check_draw only, as before; it reads the 5-line announce fine), the result
branch, rehearsal 2's announce, campaign.py, DRAW.json's format.

Run once (one-off, not a committed test): [block announce] extracted verbatim with its single GitHub push twinned to a
local bare repository: campaign → commit with the 3 files and the 5-line announce; campaign with a wrong HS →
"REFUSED: EXCLUDED_SECOND_SCAN.json has sha256 ..., not the validated 000...: no commit, no push"; rehearsal → the 2
files and the 4-line announce as before; rehearsal with S/HS set → "REFUSED: S and HS are for the campaign only".
