"""Fill FREEZE_TEMPLATE.txt: python3 fill_freeze.py TEMPLATE TREE_TOP DEV_TIP SCAN_LINE TESTC_LINE DEFECTS_LINE OUT"""
import hashlib, json, sys
from pathlib import Path
tmpl, top, dev_tip, scan_line, testc, defects, out = sys.argv[1:8]
L = Path(top) / "research/layered-networks"
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
t = Path(tmpl).read_text()
import re
for f in sorted(set(re.findall(r"\{sha:([^}]+)\}", t))):
    t = t.replace("{sha:%s}" % f, sha(L / f))
ex = json.loads((L / "EXCLUDED.json").read_text())
pins = json.loads((L / "FREEZE_PINS.json").read_text())
rep = dict(DEV_TIP=dev_tip, PINS_SHA=sha(L / "FREEZE_PINS.json"), COUNT=str(pins["count"]), EXCL_SHA=sha(L / "EXCLUDED.json"),
           SEEDS_SHA=ex["seeds_sha256"], N_INT=str(ex["count"]), N_REFS=str(len(ex["refs"])),
           PRINT_SHA=sha(L / "EXCLUDED_PRINT.txt"), SCAN_LINE=scan_line, TESTC_LINE=testc, DEFECTS_LINE=defects)
for k, v in rep.items():
    t = t.replace("{%s}" % k, v)
assert "{" not in "".join(x for x in re.findall(r"\{[A-Z_]+\}|\{sha:[^}]+\}", t)), "unfilled"
Path(out).write_text(t)
print("filled")
