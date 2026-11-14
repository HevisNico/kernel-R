"""Coupling between the drawn wires, estimated from the shapes alone. NOT an extraction.

  python3 -I estimate.py [fF]            pairs above that many fF are listed (default 0.01)

Layout 2.1 is extracted once, and nothing is redrawn after. This script is what was looked at while
the blocks were placed. It reads the shapes the generator draws on metal1 to metal4, with their
nets, and applies two rules of Magic's extraction, with the coefficients of the PDK's technology
file (`sidehalo` and `fringeshieldhalo` 8 um, `defaultsidewall`, `defaultsideoverlap`,
`defaultoverlap`) and the formulas of Magic's source (extract/ExtCouple.c):

  side   two shapes on the same layer that face each other with nothing between them, less than
         8 um apart, couple by  C = k * length / (distance + offset);
  fringe an edge couples to a shape of another layer that lies beside it, less than 8 um away, by
         C = k * length * 0.6366 * (atan(m * far) - atan(m * near)),  m = 0.02 * area capacitance.

The layout is cut into squares of 0.17 um; from each square on the edge of a protected net the
script walks up, down, left and right. For the side term it stops at the first square of another
net. For the fringe term it goes on to 8 um and counts the squares of the other layers, with the
coefficients of both directions (the edge of the one to the face of the other, and back).

What it leaves out: the overlap of two layers (the router forbids it between the two classes),
polysilicon and local interconnect, the inside of the PDK's device cells below metal1, the
shielding of a fringe by other shapes, and Magic's own way of cutting shapes. On the second layout
it gives 1.5, 0.9 and 1.2 fF where Magic gave 1.11 (`x`-`sd`), 0.98 (`x`-`si`) and 1.10
(`vgd`-`si`). It says where two nets run side by side; the numbers that count are those of the
extraction, in ../X_REPORT.md.
"""
import collections
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))        # also under python3 -I

import numpy as np

import build
import floorplan
import schematic

STEP = 34                   # 0.17 um
HALO = 1600                 # 8 um
SIDEWALL = {"m1": (44.0, 0.25), "m2": (50.0, 0.3), "m3": (74.0, 0.40), "m4": (94.0, 0.57)}     # aF, um
# between two layers: area capacitance (aF/um2), fringe of the lower one's edge, of the upper one's edge (aF/um)
FRINGE = {("m1", "m2"): (133.86, 48.19, 67.05), ("m1", "m3"): (34.54, 26.68, 54.81), ("m1", "m4"): (15.03, 16.42, 42.56),
          ("m2", "m3"): (86.19, 44.43, 69.85), ("m2", "m4"): (20.33, 22.33, 46.38), ("m3", "m4"): (84.03, 42.64, 70.52)}


def full_name(comp, key, prefix=""):
    """The name of a net of a block as cell.spice has it, from the key its shapes carry."""
    if key in getattr(comp, "inner", {}):
        inst, local = comp.inner[key]
        child = comp.children[inst]
        return full_name(child, local, prefix + inst + ".")
    return prefix + getattr(comp, "net_names", {}).get(key, key)


def cell():
    blocks = schematic.load()
    comps = build.all_devices(blocks)
    built = {}
    for name in build.ORDER:
        built[name] = floorplan.assemble(blocks[name], comps, built, build.device_key)
    return built[schematic.TOP]


def couplings(c):
    keys = sorted({s[5] for s in c.shapes if s[5] is not None})
    num = {k: i + 1 for i, k in enumerate(keys)}
    x0, y0, x1, y1 = c.bbox
    nx, ny = (x1 - x0) // STEP + 2, (y1 - y0) // STEP + 2
    prot = np.zeros(len(keys) + 1, bool)
    for k, v in c.net_class.items():
        if k in num and "q" in v:
            prot[num[k]] = True
    out = collections.Counter()
    reach = HALO // STEP
    size = len(keys) + 1
    grids = {}
    for L in SIDEWALL:
        grids[L] = grid = np.zeros((nx, ny), np.int32)
        for layer, a, b, cc, d, net in c.shapes:
            if layer == L and net is not None:
                grid[(a - x0) // STEP:max((cc - x0 + STEP - 1) // STEP, (a - x0) // STEP + 1),
                     (b - y0) // STEP:max((d - y0 + STEP - 1) // STEP, (b - y0) // STEP + 1)] = num[net]

    def add(a, b, value):
        pairs = np.zeros(size * size)
        np.add.at(pairs, a.astype(np.int64) * size + b, value)
        for code in np.nonzero(pairs)[0]:
            out[divmod(int(code), size)] += pairs[code] / 1000.0      # fF

    for L, (k, off) in SIDEWALL.items():
        grid = grids[L]
        ii, jj = np.nonzero(prot[grid])
        me = grid[ii, jj]
        for di, dj in ((1, 0), (-1, 0), (0, 1), (0, -1)):
            inside = (ii + di >= 0) & (ii + di < nx) & (jj + dj >= 0) & (jj + dj < ny)
            edge = inside.copy()                         # a square inside its own net has no edge on that side
            edge[inside] = grid[ii[inside] + di, jj[inside] + dj] != me[inside]
            alive = edge.copy()
            for n in range(1, reach + 1):
                i2, j2 = ii + di * n, jj + dj * n
                alive &= (i2 >= 0) & (i2 < nx) & (j2 >= 0) & (j2 < ny)
                idx = np.nonzero(alive)[0]
                if not len(idx):
                    break
                hit = grid[i2[idx], j2[idx]]
                found = hit != 0
                other = found & (hit != me[idx])
                dist = (n - 1) * STEP / 200.0            # um of empty squares between the two
                if other.any() and dist > 0:
                    add(me[idx[other]], hit[other], k * (STEP / 200.0) / (dist + off))
                alive[idx[found]] = False
            # fringe to the other layers, beside this edge
            for M in SIDEWALL:
                if M == L:
                    continue
                area, low, high = FRINGE[tuple(sorted((L, M)))]
                m = 0.02 * area
                other_grid = grids[M]
                for n in range(1, reach + 1):
                    i2, j2 = ii + di * n, jj + dj * n
                    good = edge & (i2 >= 0) & (i2 < nx) & (j2 >= 0) & (j2 < ny)
                    idx = np.nonzero(good)[0]
                    hit = other_grid[i2[idx], j2[idx]]
                    sel = (hit != 0) & (hit != me[idx])
                    if sel.any():
                        near = (n - 1) * STEP / 200.0
                        frac = 0.6366 * (np.arctan(m * (near + STEP / 200.0)) - np.arctan(m * near))
                        add(me[idx[sel]], hit[sel], (low + high) * (STEP / 200.0) * frac)
    names = {num[k]: full_name(c, k) for k in keys}
    cls = {num[k]: v for k, v in c.net_class.items() if k in num}
    return {(names[a], names[b]): (v, cls.get(a), cls.get(b)) for (a, b), v in out.items()}


def main(argv):
    floor = float(argv[1]) if len(argv) > 1 else 0.01
    c = cell()
    est = couplings(c)
    b = c.bbox
    print(f"cell {(b[2] - b[0]) / 200:.1f} x {(b[3] - b[1]) / 200:.1f} um = {(b[2] - b[0]) * (b[3] - b[1]) / 4e10:.4f} mm2")
    print("estimated lateral coupling of a protected net, same layer, nothing between (fF). Not an extraction.")
    rows = sorted(est.items(), key=lambda kv: -kv[1][0])
    for (a, bb), (v, ca, cb) in rows:
        if v >= floor and cb is not None and "a" in cb and not (ca != "qs" and cb == "qa"):
            print(f"  {a:12s} {ca:3s} {bb:14s} {cb:3s} {v:7.3f}")
    print("to anything, summed (fF):")
    tot = collections.Counter()
    for (a, bb), (v, ca, cb) in est.items():
        tot[a] += v
    for a, v in sorted(tot.items()):
        print(f"  {a:12s} {v:7.2f}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
