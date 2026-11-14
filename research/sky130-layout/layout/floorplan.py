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
    "comp_wc4_lc1": dict(rows=[["xm3", "xm4", "xm5", "xi1", "xi2"], ["xm1", "xm2", "xmt", "xmb", "xm6"]]),
    "comp_wc16_lc4": dict(rows=[["xm3", "xm4", "xm5", "xi1", "xi2"], ["xm1", "xm2", "xmt", "xmb", "xm6"]]),
    "opamp": dict(rows=[[[["xm3", "xm4", "xm5", "rz"], ["xmb", "xmt", "xm1", "xm2", "xm6"]], "cc"]]),
}
# One port, bottom to top: the sequencing logic; the window comparator with the sensor devices above
# it, the integrator, the gain mirror with the delay parts above it; the capacitor array.
PLACE["rport"] = dict(gap=2, rowgap=3, rows=[
    ["xien", "xicb", "xnsa", "xla", "xia1", "xia2", "xnsc", "xlc", "xid1", "xid2", "xnsb", "xlb", "xnsi", "xisi", "xisd"],
    [[["xcmps"], ["xmbd", "xmdis", "xnad", "xiad"], ["xms1", "xms2", "xmsi", "xmsd", "xmr1n", "xmr2n"], ["xmpre", "xmr1p", "xmr2p"]],
     "xop",
     [["xmin", "xmout"], ["rda", "rdl", "cda", "cdl"]]],
    ["cfcs"],
])
# The cell: port 1, the shared parts in a column, port 2 mirrored.
PLACE["rcell"] = dict(gap=3, rowgap=3, rows=[[
    "x1",
    [["xicm", "xnsp", "xnrp", "xlp", "xip1", "xip2"],
     ["xmm1n", "xmm2n", "xmm1p", "xmm2p", "rdp"],
     ["xcmpm"],
     ["rleak", "cdp"],
     ["cq"]],
    ("x2", True),
]])
# the array of the feedback and sensor capacitors: 9 x 9 plates, the sensor plate in the middle of
# the bottom row with dummy plates on its sides and above it
ARRAY = dict(nx=9, ny=9, sensor=(4, 0), dummies=[(3, 0), (5, 0), (3, 1), (4, 1), (5, 1)])
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
    def names(rows):
        for row in rows:
            for x in row:
                if isinstance(x, list):
                    yield from names(x)
                else:
                    yield x if isinstance(x, str) else x[0]
    placed = set(names(spec["rows"]))
    assert placed == set(parts), (sub.name, sorted(placed ^ set(parts)))
    blk.rows(spec["rows"], parts, conn, gap=spec.get("gap", 2), rowgap=spec.get("rowgap", 2))
    comp = blk.build()
    comp.ports = list(sub.ports)
    comp.stats = blk.stats
    return comp


def _ports(comp):
    return comp.ports
