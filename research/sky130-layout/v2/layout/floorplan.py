"""Where each part of a block is put. This file is the floorplan: the only hand-made input.

PLACE[block] is a list of rows, bottom row first, each row from the left. An entry is the name
of an element of the block in cell.spice or blocks.spice.
"""
from route import Block

PLACE = {
    "inv": dict(rows=[["xmn"], ["xmp"]]),
    "nand2": dict(rows=[["xmn2", "xmn1"], ["xmp1", "xmp2"]]),
    "nand3": dict(rows=[["xmn3", "xmn2", "xmn1"], ["xmp1", "xmp2", "xmp3"]]),
    "srlatch": dict(rows=[["x1", "x2"]]),
    # the input that may carry vq, xm1, at the end of its row, away from xm2 and its loud drain
    "comp_wc4_lc1": dict(rows=[["xm3", "xm4", "xm5", "xi1", "xi2"], ["xm1", "xmt", "xmb", "xm2", "xm6"]]),
    "comp_wc16_lc4": dict(rows=[["xm3", "xm4", "xm5", "xi1", "xi2"], ["xm1", "xmt", "xmb", "xm2", "xm6"]]),
    "opamp": dict(rows=[[[["xm3", "xm4", "xm5", "rz"], ["xmb", "xmt", "xm1", "xm2", "xm6"]], "cc"]]),
}
# One port, bottom to top: the sequencing logic; the delay parts, the reference switches, the window
# comparator and the gain mirror; the integrator with the steering switch beside it, the sensor
# devices under the sensor plate, and the admission switches at the edge that faces the shared
# column, where vq leaves the port; the capacitor array. An integer is an empty space, in tracks.
PLACE["rport"] = dict(gap=2, rowgap=3, rows=[
    ["xien", "xicb", "xnsa", "xla", "xia1", "xia2", "xnsc", "xlc", "xid1", "xid2", "xnsb", "xlb", "xnsi", "xisi", "xisd"],
    ["rda", "rdl", "cda", "cdl", [["xmr1n", "xmr2n"], ["xmr1p", "xmr2p"]], 22, "xcmps", "xmin", "xmout"],
    ["xop", 4, "xmsi", 14, [["xmbd", "xmdis"], ["xmsd", "xmpre"]], 30, [["xnad", "xiad"], ["xms2", "xms1"]]],
    ["cfcs"],
])
# The cell: port 1, the shared parts in a column, port 2 mirrored. In the column, bottom to top:
# the protection delay; the protection latch; the FIRE comparator and its reference switches; the
# leak resistor and the main capacitor, whose exits face the comparator. vq runs between the last two.
PLACE["rcell"] = dict(gap=6, rowgap=3, rows=[[
    "x1",
    [["cdp", "rdp"],
     ["xicm", "xnsp", "xnrp", "xlp", "xip1", "xip2"],
     ["xcmpm", "xmm1n", "xmm2n", "xmm1p", "xmm2p"],
     ["rleak", "cq"]],
    ("x2", True),
]])
# the array of the feedback and sensor capacitors: 9 x 9 plates. The sensor plate is in the bottom
# row, away from the three columns whose feedback plates carry the exits of the summing node, with
# dummy plates on its sides and above it.
ARRAY = dict(nx=9, ny=9, sensor=(6, 0), dummies=[(5, 0), (7, 0), (5, 1), (6, 1), (7, 1)], exits=[0, 1, 2])
# Classes of nets (route.py). "q": kept away from loud nets and shielded. "a": loud, the nets of
# ../PREDICTION.md that swing by more than 0.5 V, under the names they have inside each block.
LOGIC = dict(a={"a", "b", "c", "y", "n1", "n2", "sb", "rb", "q", "qb"})
CLASSES = {
    "inv": LOGIC, "nand2": LOGIC, "nand3": LOGIC, "srlatch": LOGIC,
    "comp_wc4_lc1": dict(q={"inn"}, a={"inp", "o1", "o2", "o3", "out"}),
    "comp_wc16_lc4": dict(q={"inn"}, a={"inp", "o1", "o2", "o3", "out"}),
    "opamp": dict(q={"inn"}),
    "rport": dict(q={"sum", "vq"}, a={"a", "ab", "ad", "ad1", "adb", "adm", "admb", "b", "bb", "c", "cbar", "cd1", "cd2", "cdel", "cmpb",
                                       "cmps", "en", "preb", "rst", "sba", "sbb", "sbc0", "sd", "sen", "si", "sib", "vs"}),
    "rcell": dict(q={"vq"}, a={"cmpm", "cmpmb", "p", "pb", "pbdel", "pd1", "pdel", "rbp", "sbp", "vrefm", "vrefmn"}),
}
# transistors drawn with source and drain exchanged, so that a net leaves on the other side:
# the admission switch of a port has vq toward the shared column
SWAP = {("rport", "xms1")}
TERMINALS = {"mos": ["D", "G", "S", "B"], "res": ["R1", "R2", "B"], "cap": ["T", "B"]}


def assemble(sub, comps, built, device_key):
    spec = PLACE[sub.name]
    blk = Block(sub.name)
    blk.exports = list(sub.ports)
    parts, conn = {}, {}
    by_name = {e.name: e for e in sub.elems}
    for e in sub.elems:
        if e.name in ("cf", "cs"):
            if e.name == "cf":
                cf, cs = by_name["cf"], by_name["cs"]
                parts["cfcs"] = comps["cfcs"]
                conn["cfcs"] = dict(sum=cf.nodes[0], vmem=cf.nodes[1], vs=cs.nodes[0], vss=cs.nodes[1])
        elif e.kind == "block":
            parts[e.name] = built[e.ref]
            conn[e.name] = dict(zip(parts[e.name].pins, e.nodes)) if False else dict(zip(_ports(built[e.ref]), e.nodes))
        else:
            parts[e.name] = comps[device_key(e)]
            conn[e.name] = dict(zip(TERMINALS[e.kind], e.nodes))
            if (sub.name, e.name) in SWAP:
                conn[e.name]["D"], conn[e.name]["S"] = conn[e.name]["S"], conn[e.name]["D"]
    def names(rows):
        for row in rows:
            for x in row:
                if isinstance(x, int):
                    continue
                if isinstance(x, list):
                    yield from names(x)
                else:
                    yield x if isinstance(x, str) else x[0]
    placed = set(names(spec["rows"]))
    assert placed == set(parts), (sub.name, sorted(placed ^ set(parts)))
    blk.rows(spec["rows"], parts, conn, gap=spec.get("gap", 2), rowgap=spec.get("rowgap", 2))
    blk.critical = set(CLASSES.get(sub.name, {}).get("q", ()))
    blk.loud = set(CLASSES.get(sub.name, {}).get("a", ()))
    if sub.name == "rport":
        # vq leaves the port by a wire drawn inside it: from the admission switch to the edge
        from route import footprint
        _, comp_, col, row, _ = next(i for i in blk.insts if i[0] == "xms1")
        _, c, r = comp_.pins["D"][0]
        edge = max(i[2] + footprint(i[1])[2] for i in blk.insts if i[0] != "cfcs") + 2
        blk.exits["vq"] = ("m1", edge, r + row)
    comp = blk.build()
    comp.ports = list(sub.ports)
    comp.stats = dict(blk.stats, shield_nodes=blk.shield_nodes)
    return comp


def _ports(comp):
    return comp.ports
