import hashlib, sys
p = sys.argv[1]; pins, exj, seeds, prt = sys.argv[2:6]
t = open(p).read()
I = " " * 36
new_tip = ("  research/layered-campaign-dev     9219986b09be4c7ec8660c591ddf78f67d77fbeb  (the tree the exclusion scan ran over,\n"
           + I + "recorded by rescan.sh as CLONE_HEAD; the pins are made over that tree plus this\n"
           + I + "record's commit, which changes only EXCLUDED.json, EXCLUDED_PRINT.txt,\n"
           + I + "FREEZE_PINS.json and FREEZE.txt)\n")
print("tip block sha256", hashlib.sha256(new_tip.encode()).hexdigest())
old_tip = ("  research/layered-campaign-dev     340e1c6c722213dbb6060d896b5cfc038273e00e  (the tree these pins were made over,\n"
           + I + "after its last dev commit and the exclusion scan; this record is a later commit\n"
           + I + "that changes no pinned file)\n")
assert t.count(old_tip) == 1; t = t.replace(old_tip, new_tip)
def rep(old, new):
    global t
    assert t.count(old) == 1, old; t = t.replace(old, new)
rep("  FREEZE_PINS.json                  sha256 779b35bd53291fba77979156a5c4f66adb59960aaab69fc96db7841564a20b2f  (114 files)\n",
    f"  FREEZE_PINS.json                  sha256 {pins}  (114 files)\n")
rep("  EXCLUDED.json                     sha256 abdc38e8c3dee532ecb67097951e3c7d4f8c3bb1e22d3a30a91a11dceb5d680c\n",
    f"  EXCLUDED.json                     sha256 {exj}\n")
rep("    seeds_sha256                    d9975dee4f80fb75ea5fb67d3d0301bbae2274b0857fc7d44dc216f1c67afbc6  (15741 integers, 256 refs)\n",
    f"    seeds_sha256                    {seeds}  (16333 integers, 286 refs)\n")
rep("  EXCLUDED_PRINT.txt                sha256 a9c808de9a22b998b44a6f3c3ae9be7695aac5589015d1c0e793ee21e5c2736c\n",
    f"  EXCLUDED_PRINT.txt                sha256 {prt}\n")
old_scan = ("    the last scan, 2026-11-27: draw_seeds.py scan over the 255 branches of origin, each fetched by name (depth 1), plus\n"
            "    HEAD = main 3f27bb36; against 381b4ffe (232 refs), 24 new refs (the evidence branches devtest-K07..K12,\n"
            "    devtest-run2/run3/run4-K07..K12), one ref changed (research/layered-campaign-dev, now 483f90c5), none removed,\n"
            "    45 integers added, none removed; excluded fraction 6.86% (draw_seeds.MAX_EXCLUDED_FRACTION 20%)\n")
new_scan = ("    the last scan, 2026-11-27: dev/freeze/final/rescan/rescan.sh, its PART 1 [block second-scan] verbatim: draw_seeds.py\n"
            "    scan over the 285 branches of origin, each fetched by name (depth 1), plus HEAD = main 3f27bb36; against abdc38e8\n"
            "    (256 refs), 30 new refs (the evidence branches combined-rehearsal-K01..K12, combined-seals-K01..K12,\n"
            "    combined-rehearsal-analysis, combined-rehearsal-draw, combined-rehearsal-draw-result,\n"
            "    combined-rehearsal1-local-records; research/layered-campaign-freeze, research/layered-campaign-prediction), two refs\n"
            "    changed (research/layered-campaign-dev, now 9219986b; review/prediction-candidate, now 95a98fc4), none removed,\n"
            "    592 integers added, none removed; excluded fraction 7.16% (draw_seeds.MAX_EXCLUDED_FRACTION 20%)\n")
rep(old_scan, new_scan)
assert not any(l != l.rstrip() for l in (new_tip + new_scan).splitlines())
open(p, "w").write(t)
