"""The term that the extraction adds between the two plates of each MIM capacitor (finding F4),
measured by a second extraction, and the list of capacitances without it.

  python3 -I plates.py FULL_CAPS.csv OUT_PRIMARY.csv         (after run.sh and run_pex.sh)

The cell is flattened again and the metal4 of every top plate is erased inside its capacitor,
0.195 um inside the capacitor layer, where the generator drew it. Everything else stays: the
exits of the plates, the joints between plates, every wire. A dummy plate, whose two plates are
on one net, is left as it is. The pieces of metal4 that the erasure separates from their net get
a label with the name of that net; Magic names such a piece NET_uqN, and the suffix is removed here,
which puts the piece back on its net.

For each capacitor of cell.spice, between its two nodes:

    plate term = capacitance in the first extraction - capacitance in the second, not below zero.

OUT_PRIMARY is FULL_CAPS with the plate term taken out of that one row for each capacitor. Every
other row is copied unchanged: the second extraction is used for nothing else. Rows are never
dropped, so that both lists hold the same capacitors.
"""
import csv
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import build
import devices
import pex
import schematic
from floorplan import PLACE, assemble
from tech import BUILD

INSET = 39


def top_comp():
    blocks = schematic.load()
    comps = build.all_devices(blocks)
    built = {}
    for name in build.ORDER:
        if name in PLACE:
            built[name] = assemble(blocks[name], comps, built, build.device_key)
            built[name].write()
    cells = dict(built)
    cells.update({c.name: c for c in comps.values()})
    return blocks, built[schematic.TOP], cells


def top_plate_metal(blocks, cells):
    """Every piece of metal4 of a capacitor, in the coordinates of the cell, with the name of its net
    as Magic writes it for the flattened cell."""
    out = []

    def walk(name, prefix, mirror, tx, ty):
        uses = {u[1]: u for u in cells[name].uses}
        by = {e.name: e for e in blocks[name].elems}
        for e in blocks[name].elems:
            if e.kind == "block":
                _, _, mx, ux, uy, _ = uses[e.name]
                walk(e.ref, prefix + e.name + ".", mirror != mx, (-ux if mirror else ux) + tx, uy + ty)
            elif e.kind == "cap" and e.name != "cs":
                array = e.name == "cf"
                cell, _, mx, ux, uy, _ = uses["cfcs" if array else e.name]
                m, ax, ay = mirror != mx, (-ux if mirror else ux) + tx, uy + ty
                local = dict(sum=e.nodes[0], vmem=e.nodes[1], vs=by["cs"].nodes[0]) if array else dict(T=e.nodes[0])
                for layer, x1, y1, x2, y2, net in cells[cell].shapes:
                    if layer == "m4":
                        r = (ax - x2, y1 + ay, ax - x1, y2 + ay) if m else (x1 + ax, y1 + ay, x2 + ax, y2 + ay)
                        out.append(r + (prefix + local[net],))

    walk(schematic.TOP, "", False, 0, 0)
    return out


def main(full_csv, out_csv):
    blocks, top, cells = top_comp()
    by_rect = {s[1:5]: s[5] for s in top.shapes if s[0] == "m4"}
    plates = []
    for layer, x1, y1, x2, y2, bottom, _ in top.keeps:
        rect = (x1 + INSET, y1 + INSET, x2 - INSET, y2 - INSET)
        assert rect in by_rect, f"no top plate at {rect}"
        if by_rect[rect] != bottom:                      # a dummy plate has both plates on one net
            plates.append(rect)
    tcl = ["load rcell", "select top cell", "flatten rcell_np", "load rcell_np"]
    for r in plates:
        tcl += ["box %di %di %di %di" % r, "erase metal4"]
    labels = 0
    for x1, y1, x2, y2, net in top_plate_metal(blocks, cells):
        if (x1, y1, x2, y2) in plates:
            continue
        # what is left of this piece outside the erased plates: label its centre if it lies there
        cx, cy = (x1 + x2) // 2, (y1 + y2) // 2
        if not any(p[0] <= cx <= p[2] and p[1] <= cy <= p[3] for p in plates):
            tcl += [f"box {cx - 2}i {cy - 2}i {cx + 2}i {cy + 2}i", f"label {net} center metal4"]
            labels += 1
    tcl += ["select top cell", "extract all", "ext2spice lvs", "ext2spice cthresh 0", "ext2spice -o rcell_np_c.spice",
            "quit -noprompt"]
    (BUILD / "cell_pex_noplates.tcl").write_text("\n".join(tcl) + "\n")
    devices.run_magic("cell_pex_noplates.tcl", "cell_pex_noplates.log")
    text = (BUILD / "rcell_np_c.spice").read_text()
    (BUILD / "rcell_np_named.spice").write_text(re.sub(r"_uq\d+\b", "", text))
    second = pex.main(BUILD / "rcell_np_named.spice", BUILD / "np_areas.csv", BUILD / "np_caps.csv")
    with open(full_csv) as fh:
        rows = [(r["node1"], r["node2"], float(r["farad"])) for r in csv.DictReader(fh)]
    full = {(a, b): v for a, b, v in rows}
    alias = pex.aliases(blocks)
    term = {}
    for path, kind, model, nets, par in schematic.flat(blocks, schematic.TOP):
        if kind != "cap":
            continue
        a, b = (alias[n.replace("/", ".")] for n in nets)
        pair = tuple(sorted((a, b), key=lambda x: (x == "0", x)))
        assert pair in full and pair not in term, path
        term[pair] = (path.replace("/", "."), par["value"], max(0.0, full[pair] - second.get(pair, 0.0)))
    with open(out_csv, "w", newline="") as fh:
        w = csv.writer(fh, lineterminator="\n")
        w.writerow(["node1", "node2", "farad"])
        for a, b, v in rows:
            w.writerow([a, b, f"{v - term[(a, b)][2] if (a, b) in term else v:.6g}"])
    print(f"PLATES {len(plates)} top plates erased in the second extraction, {labels} labels added")
    for pair, (path, value, t) in sorted(term.items(), key=lambda kv: kv[1][0]):
        print(f"PLATE_TERM {path}: ideal {value * 1e15:.0f} fF; between its nodes {full[pair] * 1e15:.2f} fF extracted, "
              f"plate term {t * 1e15:.2f} fF ({t / value * 100:.2f}%), kept {(full[pair] - t) * 1e15:.2f} fF")
    print(f"PLATE_SUM {sum(t for _, _, t in term.values()) * 1e12:.4f} pF taken out of {sum(full.values()) * 1e12:.4f} pF")


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
