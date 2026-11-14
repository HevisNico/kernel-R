"""A picture of a block as the generator sees it: placed cells and wires. For the eye only.

  python3 -I view.py BLOCK OUT.png
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Rectangle

import build
import schematic
from floorplan import PLACE, assemble
from route import tr_rect

COLOR = {"m1": "#3b6fb6", "m2": "#c0504d", "m3": "#5a9e4b", "m4": "#8064a2"}


def main(name, out):
    blocks = schematic.load()
    comps = build.all_devices(blocks)
    built = {}
    for n in build.ORDER:
        if n in PLACE:
            built[n] = assemble(blocks[n], comps, built, build.device_key)
        if n == name:
            break
    c = built[name]
    b = c.bbox
    w, h = (b[2] - b[0]) / 200, (b[3] - b[1]) / 200
    fig, ax = plt.subplots(figsize=(min(24, max(8, w / 8)), min(24, max(6, h / 8))))
    for layer, x1, y1, x2, y2, net in c.shapes:
        k = c.net_class.get(net)
        color = "#d62728" if k == "q" else ("#ff9900" if k == "a" else ("#2ca02c" if net == "vss" else "#9aa0a6"))
        ax.add_patch(Rectangle((x1 / 200, y1 / 200), (x2 - x1) / 200, (y2 - y1) / 200, color=color, alpha=0.8 if k == "q" else 0.45, lw=0))
    for cell, inst, mx, tx, ty, box in c.uses:
        r = tr_rect(box, mx, tx, ty)
        ax.add_patch(Rectangle((r[0] / 200, r[1] / 200), (r[2] - r[0]) / 200, (r[3] - r[1]) / 200, fill=False, ec="k", lw=0.6))
        ax.text((r[0] + r[2]) / 400, (r[1] + r[3]) / 400, inst, ha="center", va="center", fontsize=7)
    win = [float(v) for v in sys.argv[3:7]] if len(sys.argv) > 6 else [b[0] / 200 - 2, b[2] / 200 + 2, b[1] / 200 - 2, b[3] / 200 + 2]
    ax.set_xlim(win[0], win[1])
    ax.set_ylim(win[2], win[3])
    ax.set_aspect("equal")
    ax.set_title(f"{name}: {w:.1f} um x {h:.1f} um (critical nets red, loud nets orange, vss green, others grey; all layers)")
    fig.savefig(out, dpi=110, bbox_inches="tight")


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
