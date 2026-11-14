"""Which nets of the cell swing by more than 0.5 V? A simulation of the schematic: no area, no
capacitance, no layout.

  python3 -I swings.py        (from research/sky130-layout/v2; MODELS as in ../checks/run.sh)

The nominal train of the certification campaign (22 periods, no noise, 27 C), with the sub-circuits
expanded by ../phase1/netlist.py so that every net has the name ngspice gives it, and every net
saved. Writes swings.csv: net, lowest and highest voltage over the run, swing. The list of "loud"
nets of PREDICTION.md is the nets of this file whose swing is above 0.5 V.
"""
import csv
import os
import shutil
import subprocess
import sys
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
P1 = HERE.parent / "phase1"
CIRCUIT = HERE.parent.parent / "circuit"
sys.path.insert(0, str(P1))
sys.path.insert(0, str(CIRCUIT / "certification"))
import cert_run
import netlist

MODELS = Path(os.environ.get("MODELS", CIRCUIT / "pdk"))
work = HERE / "build" / "swings"
shutil.rmtree(work, ignore_errors=True)
work.mkdir(parents=True)
shutil.copy(CIRCUIT / "blocks.spice", work / "blocks.spice")
shutil.copy(CIRCUIT / "spiceinit.txt", work / ".spiceinit")
os.symlink(MODELS, work / "pdk")
deck = cert_run.deck(dict(name="swings", mode="train", section="tt", seed=None, noise=False), "raw.txt")
text, _ = netlist.build(deck, (CIRCUIT / "blocks.spice").read_text())
nodes = set()
for line in text.splitlines():
    if line.startswith(".control"):
        break
    tok = line.split()
    if tok and tok[0][0].lower() in "xcr" and not line.startswith("."):
        n = netlist.NODES[tok[0][0].lower()] or len([t for t in tok[1:] if "=" not in t]) - 1
        nodes.update(tok[1:1 + n])
nodes = sorted(nodes - {"0"})
vectors = " ".join(f"v({n})" for n in nodes)
out = []
for line in text.splitlines():
    if line.startswith(".save "):
        line = ".save " + vectors
    elif line.startswith("wrdata "):
        line = "wrdata raw.txt " + vectors
    out.append(line)
(work / "swings.spice").write_text("\n".join(out) + "\n")
subprocess.run(["/usr/bin/ngspice", "-b", "swings.spice"], cwd=work, check=True, capture_output=True,
               env=dict(os.environ, SPICE_SCRIPTS=str(CIRCUIT / "bridge_check" / "runtime")))
d = np.loadtxt(work / "raw.txt")
sel = d[:, 0] >= 3e-6                       # after the preset of the integrators
with open(HERE / "swings.csv", "w", newline="") as fh:
    w = csv.writer(fh, lineterminator="\n")
    w.writerow(["net", "lowest_V", "highest_V", "swing_V"])
    for k, n in enumerate(nodes, 1):
        lo, hi = float(d[sel, k].min()), float(d[sel, k].max())
        w.writerow([n, f"{lo:.4f}", f"{hi:.4f}", f"{hi - lo:.4f}"])
print(len(nodes), "nets;", sum(1 for k in range(1, len(nodes) + 1) if d[sel, k].max() - d[sel, k].min() > 0.5), "swing by more than 0.5 V")
