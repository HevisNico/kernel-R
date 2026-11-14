"""From the extraction of the flattened cell to the two tables of stage P.

  python3 -I pex.py build/rcell_pex_c.spice OUT_AREAS.csv OUT_CAPS.csv

Reads the netlist Magic writes for the flattened cell (cell_pex.tcl) and writes, with the names of
the nodes and devices of cell.spice as ngspice flattens it:

  areas   one row per transistor: path, ad, as (um2), pd, ps (um), summed over its fingers;
  caps    one row per pair of nodes: node1, node2, farad. Node 0 is the substrate and vss.

Nothing is simulated. The script stops if a device or a node of the extraction has no counterpart
in cell.spice, if a transistor of cell.spice is missing or has another width or length, or if two
transistors of cell.spice cannot be told apart by their nets.

Two rules, fixed here:

  - a net of the layout carries the name of the highest block it reaches; `schematic.py` gives the
    node of cell.spice for every such name;
  - the resistor of 8 MOhm is drawn as 20 strips in series, and cell.spice has one resistor. The
    capacitance of an inner node is shared between the two ends of the resistor in proportion to
    the resistance between the node and the other end.
"""
import csv
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import schematic

SUFFIX = {"f": 1e-15, "a": 1e-18, "p": 1e-12, "n": 1e-9, "u": 1e-6, "": 1.0}


def canonical(net):
    """Name of a top-level net of the layout as a node of cell.spice."""
    if net == "vss":
        return "0"
    m = re.fullmatch(r"(x\d+)_(\w+)", net)
    return f"{m.group(1)}.{m.group(2)}" if m else net


def aliases(blocks):
    """Every name a net can carry in the flattened layout -> node of cell.spice."""
    out = {}

    def walk(name, prefix, conn):
        sub = blocks[name]
        nets = {n for e in sub.elems for n in e.nodes}
        for n in nets:
            node = conn.get(n) or (canonical(n) if not prefix else prefix + n)
            out[prefix + n if prefix else n] = node
        for e in sub.elems:
            if e.kind == "block":
                child = blocks[e.ref]
                inner = {p: out[prefix + n if prefix else n] for p, n in zip(child.ports, e.nodes)}
                walk(e.ref, prefix + e.name + ".", inner)

    walk(schematic.TOP, "", {})
    return out


def main(src, out_areas, out_caps):
    blocks = schematic.load()
    alias = aliases(blocks)
    devs = schematic.flat(blocks, schematic.TOP)
    # the strips of a resistor in series: inner node k of n -> share of the first end
    inner = {}
    by_key = {}
    for path, kind, model, nets, par in devs:
        nodes = [alias[n.replace("/", ".")] for n in nets]
        dotted = path.replace("/", ".")
        if kind == "mos":
            d, g, s, b = nodes
            assert d != s, path
            key = (model, g, b, frozenset((d, s)), round(par["l"], 4))
            assert key not in by_key, f"{path} and {by_key.get(key, [''])[0]} cannot be told apart"
            by_key[key] = [dotted, d, s, par["w"], 0.0, 0.0, 0.0, 0.0, 0.0]
        elif kind == "res" and par["series"] > 1:
            # strip j carries the labels R2_j at its lower end and R1_j at its upper end; strips j and
            # j + 1 are joined at their upper ends for j even and at their lower ends for j odd.
            # Inner node k lies between strips k - 1 and k.
            n = par["series"]
            for j in range(n):
                up, down = (j + 1, j) if j % 2 == 0 else (j, j + 1)
                for label, k in ((f"R1_{j}", up), (f"R2_{j}", down)):
                    if 0 < k < n:
                        inner[f"{dotted}/d1.{label}"] = (nodes[0], nodes[1], 1 - k / n)

    def node(name):
        if name in alias:
            return [(alias[name], 1.0)]
        if name in inner:
            a, b, share = inner[name]
            return [(a, share), (b, 1 - share)]
        raise SystemExit(f"a net of the extraction is not in cell.spice: {name}")

    caps, seen = {}, 0
    for line in Path(src).read_text().splitlines():
        tok = line.split()
        if not tok:
            continue
        if tok[0][0] == "X" and "fet" in line:
            n1, g, n3, b, model = tok[1:6]
            par = dict(t.split("=") for t in tok[6:])
            key = (model.replace(schematic.MOS, ""), node(g)[0][0], node(b)[0][0],
                   frozenset((node(n1)[0][0], node(n3)[0][0])), round(float(par["l"]), 4))
            assert key in by_key, f"a transistor of the extraction is not in cell.spice: {line}"
            row = by_key[key]
            first_is_drain = node(n1)[0][0] == row[1]
            ad, as_, pd, ps = (float(par[k]) for k in ("ad", "as", "pd", "ps"))
            if not first_is_drain:
                ad, as_, pd, ps = as_, ad, ps, pd
            row[4] += ad
            row[5] += as_
            row[6] += pd
            row[7] += ps
            row[8] += float(par["w"])
            seen += 1
        elif tok[0][0] == "C":
            m = re.fullmatch(r"([-+0-9.e]+)([a-z]?)", tok[3].lower())
            value = float(m.group(1)) * SUFFIX[m.group(2)]
            for a, wa in node(tok[1]):
                for b, wb in node(tok[2]):
                    if a != b:
                        pair = tuple(sorted((a, b), key=lambda x: (x == "0", x)))
                        caps[pair] = caps.get(pair, 0.0) + value * wa * wb
    for key, row in by_key.items():
        assert abs(row[8] - row[3]) < 1e-6, f"{row[0]}: width {row[8]} in the layout, {row[3]} in cell.spice"
    with open(out_areas, "w", newline="") as fh:
        w = csv.writer(fh, lineterminator="\n")
        w.writerow(["path", "ad", "as", "pd", "ps"])
        for row in sorted(by_key.values()):
            w.writerow([row[0]] + [f"{v:.6g}" for v in row[4:8]])
    with open(out_caps, "w", newline="") as fh:
        w = csv.writer(fh, lineterminator="\n")
        w.writerow(["node1", "node2", "farad"])
        for (a, b), v in sorted(caps.items()):
            w.writerow([a, b, f"{v:.6g}"])
    # Between the two plates of each capacitor: what the extraction adds to the ideal value, and
    # what Magic's rule for metal4 over metal3 gives for the metal4 of the plates alone
    # (84.03 aF per um2 and 70.52 aF per um of edge; the metal4 is 0.195 um inside the capacitor layer).
    for path, kind, model, nets, par in devs:
        if kind != "cap":
            continue
        a, b = (alias[n.replace("/", ".")] for n in nets)
        pair = tuple(sorted((a, b), key=lambda x: (x == "0", x)))
        side = par["side"] - 0.39
        rule = par["count"] * (side * side * 84.03e-18 + 4 * side * 70.52e-18)
        print(f"PEX_MIM {path.replace('/', '.')}: ideal {par['value'] * 1e15:.0f} fF, between its plates {caps.get(pair, 0) * 1e15:.1f} fF "
              f"({caps.get(pair, 0) / par['value'] * 100:.2f}%), metal4 over metal3 by Magic's rule {rule * 1e15:.1f} fF")
    total = sum(caps.values())
    ground = sum(v for (a, b), v in caps.items() if b == "0")
    print(f"PEX {len(by_key)} transistors from {seen} extracted fingers; {len(caps)} capacitances, "
          f"{total * 1e12:.3f} pF in all, of which {ground * 1e12:.3f} pF to node 0")
    return caps


if __name__ == "__main__":
    main(*sys.argv[1:4])
