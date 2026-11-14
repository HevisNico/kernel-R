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
    # layout 2.2, the FIRE comparator: back in the two rows of the second layout, the two input devices
    # xm1 (vq) and xm2 (vrefmn) in one row with two devices between them
    "comp_wc16_lc4": dict(rows=[["xm3", "xm4", "xm5", "xi1", "xi2"], ["xm1", "xmt", "xmb", "xm2", "xm6"]]),
    "opamp": dict(rows=[[[["xm3", "xm4", "xm5", "rz"], ["xmb", "xmt", "xm1", "xm2", "xm6"]], "cc"]]),
}
# One port, bottom to top: the sequencing logic; the delay parts, the reference switches, the window
# comparator and the gain mirror; the integrator with the steering switch beside it, the sensor
# devices under the sensor plate, and the admission switches at the edge that faces the shared
# column, where vq leaves the port; the capacitor array. An integer is an empty space, in tracks.
# Layout 2.1. Every gate exit points up, and the controls of the sensor (si, sd, preb) are loud,
# while the nets of the channels (sum, x, vs) are protected: the plan is made so that no control has
# to cross a protected net, and none runs along `vs`.
#   - the sensor devices are in two rows under the sensor plate, lifted to the array;
#   - the logic that makes si and sd is in the row below, on the left; its two outputs rise between
#     the amplifier and the sensor devices and reach the gates of xmsd and xmsi from the left,
#     above the top row;
#   - sum leaves xmsi on the right, rises, and joins the feedback plates by the exit of column 4;
#   - vs joins xmdis and xmpre in the lower row and rises to the sensor plate (column 6) on the
#     right of sum; it goes down to the sensor comparator, whose input is under it;
#   - preb, a pin of the port, is the gate of xmpre at the right end.
PLACE["rport"] = dict(gap=2, rowgap=3, rows=[
    ["xien", "xicb", "xnsa", "xla", "xia1", "xia2", "xnsc", "xlc", "xid1", "xid2", "xnsb", "xlb"],
    ["rda", "rdl", "cda", "cdl", [["xmr1n", "xmr2n"], ["xmr1p", "xmr2p"]], "xisd", "xisi", "xnsi", 59, "xmin", "xmout"],
    ["xop", 4, [["xcmps"], 5, ["xmbd", "xmdis", "xmpre"], [13, "xmsd", "xmsi"]], 6, "xnad", "xiad", 4, "xms2", "xms1"],
    ["cfcs"],
])
# The cell: port 1, the shared parts in a column, port 2 mirrored. In the column, bottom to top:
# the protection delay; the protection latch; the FIRE comparator and its reference switches; the
# leak resistor and the main capacitor, whose exits face the comparator. vq runs between the last two.
PLACE["rcell"] = dict(gap=6, rowgap=3, rows=[[
    "x1",
    [["cdp", "rdp"],
     ["xicm", "xnsp", "xnrp", "xlp", "xip1", "xip2"],
     # layout 2.2: the comparator in two rows again; thirteen tracks of height above it, where vq
     # passes from one port to the other more than 8.2 um above the device that carries vrefmn
     ["xcmpm", "xmm1n", "xmm2n", "xmm1p", "xmm2p"],
     13,
     ["rleak", "cq"]],
    ("x2", True),
]])
# the array of the feedback and sensor capacitors: 9 x 9 plates. The sensor plate is in the bottom
# row, away from the three columns whose feedback plates carry the exits of the summing node, with
# dummy plates on its sides and above it.
ARRAY = dict(nx=9, ny=9, sensor=(6, 0), dummies=[(5, 0), (7, 0), (5, 1), (6, 1), (7, 1)], exits=[0, 1, 2, 4])
# Classes of nets (route.py). "qs": critical, kept away from loud nets and from `vs`. "q": protected,
# kept away from loud nets. "qa": `vs`. "a": loud, the nets of ../PREDICTION.md of the second layout
# that swing by more than 0.5 V, under the names they have inside each block. "sh": the nets that
# get `vss` wires beside them.
LOGIC = dict(a={"a", "b", "c", "y", "n1", "n2", "sb", "rb", "q", "qb"})
CLASSES = {
    "inv": LOGIC, "nand2": LOGIC, "nand3": LOGIC, "srlatch": LOGIC,
    "comp_wc4_lc1": dict(qs={"inn"}, sh={"inn"}, a={"inp", "o1", "o2", "o3", "out"}),
    "comp_wc16_lc4": dict(qs={"inn"}, sh={"inn"}, a={"inp", "o1", "o2", "o3", "out"}),
    "opamp": dict(qs={"inn"}, sh={"inn"}),
    # layout 2.1: x, vgd, dq and gm protected too, x and vgd shielded; vs kept away from the loud nets
    # and from the critical ones
    "rport": dict(qs={"sum", "vq"}, q={"x", "vgd", "dq", "gm"}, qa={"vs"}, sh={"sum", "vq", "x", "vgd"},
                  a={"a", "ab", "ad", "ad1", "adb", "adm", "admb", "b", "bb", "c", "cbar", "cd1", "cd2", "cdel", "cmpb",
                     "cmps", "en", "preb", "rst", "sba", "sbb", "sbc0", "sd", "sen", "si", "sib"}),
    "rcell": dict(qs={"vq"}, sh={"vq"}, a={"cmpm", "cmpmb", "p", "pb", "pbdel", "pd1", "pdel", "rbp", "sbp", "vrefm", "vrefmn"}),
}
# transistors drawn with source and drain exchanged, so that a net leaves on the other side:
# the admission switch of a port has vq toward the shared column
SWAP = {("rport", "xms1"), ("rport", "xmsi"), ("rport", "xmpre")}
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
            if isinstance(row, int):
                continue
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
    blk.critical = set(CLASSES.get(sub.name, {}).get("qs", ()))
    blk.loud = set(CLASSES.get(sub.name, {}).get("a", ()))
    blk.protected = set(CLASSES.get(sub.name, {}).get("q", ()))
    blk.both = set(CLASSES.get(sub.name, {}).get("qa", ()))
    blk.shield = set(CLASSES.get(sub.name, {}).get("sh", ()))
    if sub.name == "rport":
        # vq leaves the port by a wire drawn inside it: from the admission switch to the edge
        from route import footprint
        _, comp_, col, row, _ = next(i for i in blk.insts if i[0] == "xms1")
        _, c, r = comp_.pins["D"][0]
        edge = max(i[2] + footprint(i[1])[2] for i in blk.insts if i[0] != "cfcs") + 2
        blk.exits["vq"] = ("m1", edge, r + row)
        # Around the two steering switches the wires are told where not to go.
        #   - sum leaves xmsi on its right and rises three tracks from the gate, to six tracks above
        #     the switch. It does not come back over the switch or pass on its left below that: the
        #     gates stay open to the left, where si and sd come from.
        #   - si comes down on the gate of xmsi from above, and sd reaches the gate of xmsd from the
        #     left: neither passes over x, which lies between the two switches.
        _, _, col, row, _ = next(i for i in blk.insts if i[0] == "xmsi")
        _, _, col_d, _, _ = next(i for i in blk.insts if i[0] == "xmsd")
        blk.forbid["sum"] = [(col - 40, row - 8, col, row + 6), (col, row + 1, col + 2, row + 6)]
        blk.forbid["si"] = [(col_d - 1, row - 8, col - 1, row + 2), (col + 1, row - 8, col + 6, row + 6)]
        blk.forbid["sd"] = [(col_d + 1, row - 8, col + 6, row + 6)]
    if sub.name == "rcell":
        # Layout 2.2: no wire of vq less than 8.2 um from the device of the FIRE comparator that
        # carries vrefmn (xm2), on any layer. Magic couples shapes up to 8 um apart; in the second
        # layout a wire of vq passed 4.4 um above that device.
        from route import HALO
        from tech import P
        _, comp_, col, row, mx = next(i for i in blk.insts if i[0] == "xcmpm")
        assert not mx
        _, _, _, tx, ty, box = next(u for u in comp_.uses if u[1] == "xm2")
        x1, y1, x2, y2 = col * P + tx + box[0], row * P + ty + box[1], col * P + tx + box[2], row * P + ty + box[3]
        blk.forbid["vq"] = [((x1 - HALO) // P, (y1 - HALO) // P, -((-(x2 + HALO)) // P), -((-(y2 + HALO)) // P))]
    comp = blk.build()
    comp.ports = list(sub.ports)
    comp.stats = dict(blk.stats, shield_nodes=blk.shield_nodes)
    return comp


def _ports(comp):
    return comp.ports
