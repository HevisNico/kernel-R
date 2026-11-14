"""The devices of the cell: each drawn by the device generator of the PDK, then given its exits.

A transistor or a resistor is drawn by Magic's generator for SKY130, with its guard ring. The
generator leaves the terminals on metal1 where the device puts them. `wrap` adds to each terminal
an exit that ends on a node of the routing grid (tech.P):

  one finger    source to the left, drain to the right, gate upward, guard ring downward, on metal1;
  more fingers  the source columns joined by a metal2 strap, the drain columns by another one,
                the gates joined by the generator, gate upward, guard ring downward;
  resistor      its two ends downward or upward, guard ring to the left.

A MIM capacitor is drawn here, plate by plate (`mim`), because the array of the feedback capacitor
needs its own pitch. Its layers are those the generator draws.

A device with its exits is a `Comp`: a Magic cell, the shapes it puts on the routing layers with
the terminal each belongs to, and the grid nodes where a terminal can be reached.
"""
import subprocess

from tech import BUILD, CUT, MAGICRC, P, UM, WIRE


class Comp:
    """A cell as the router sees it."""

    def __init__(self, name):
        self.name = name
        self.shapes = []        # (layer, x1, y1, x2, y2, net)
        self.cuts = []          # (via layer, x1, y1, x2, y2): contacts that are not on the grid
        self.keeps = []         # (layer, x1, y1, x2, y2, net, distance): other nets stay that far away
        self.pins = {}          # net -> [(layer, column, row)]
        self.nwell = []         # rectangles of n-well
        self.nkeep = []         # rectangles an n-well must keep away from (n devices, taps, resistors)
        self.bbox = None
        self.devices = []       # (path, model, parameters, terminals) below this cell, for the netlist
        self.paint = {}         # magic layer -> rectangles painted in this cell
        self.uses = []          # (cell, instance, mirror, tx, ty, bbox of the cell)
        self.labels = []        # (magic layer, x, y, text, port number or None)

    def grow(self, r):
        b = self.bbox
        self.bbox = tuple(r) if b is None else (min(b[0], r[0]), min(b[1], r[1]), max(b[2], r[2]), max(b[3], r[3]))

    def add(self, layer, rect, net, magic_layer):
        self.paint.setdefault(magic_layer, []).append(tuple(rect))
        self.grow(rect)
        if layer:
            self.shapes.append((layer,) + tuple(rect) + (net,))

    def write(self):
        out = ["magic", "tech sky130A", "magscale 1 2", "timestamp 1"]
        for layer in sorted(self.paint):
            out.append(f"<< {layer} >>")
            out += ["rect %d %d %d %d" % r for r in self.paint[layer]]
        for cell, inst, mx, tx, ty, box in self.uses:
            out.append(f"use {cell} {inst}")
            out.append("timestamp 1")
            out.append(f"transform {-1 if mx else 1} 0 {tx} 0 1 {ty}")
            out.append("box %d %d %d %d" % box)
        if self.labels:
            out.append("<< labels >>")
            for layer, x, y, text, port in self.labels:
                out.append(f"flabel {layer} {x - 6} {y - 6} {x + 6} {y + 6} 0 FreeSans 80 0 0 0 {text}")
                if port is not None:
                    out.append(f"port {port} nsew")
        out.append("<< end >>")
        (BUILD / f"{self.name}.mag").write_text("\n".join(out) + "\n")


def run_magic(script, log):
    (BUILD / script).parent.mkdir(parents=True, exist_ok=True)
    with open(BUILD / log, "w") as fh:
        subprocess.run(["magic", "-dnull", "-noconsole", "-rcfile", str(MAGICRC), script],
                       cwd=BUILD, stdout=fh, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL, check=True)
    return (BUILD / log).read_text()


def read_mag(path):
    layers, layer = {}, None
    for line in path.read_text().splitlines():
        if line.startswith("<< "):
            layer = line[3:-3]
        elif line.startswith("rect ") and layer:
            layers.setdefault(layer, []).append(tuple(int(v) for v in line.split()[1:5]))
    return layers


def touch(a, b):
    return a[0] <= b[2] and b[0] <= a[2] and a[1] <= b[3] and b[1] <= a[3]


def overlap(a, b):
    return a[0] < b[2] and b[0] < a[2] and a[1] < b[3] and b[1] < a[3]


def hull(rects):
    return (min(r[0] for r in rects), min(r[1] for r in rects), max(r[2] for r in rects), max(r[3] for r in rects))


def groups(rects):
    """Connected groups of touching rectangles."""
    parent = list(range(len(rects)))

    def find(i):
        while parent[i] != i:
            parent[i] = parent[parent[i]]
            i = parent[i]
        return i
    for i in range(len(rects)):
        for j in range(i):
            if touch(rects[i], rects[j]):
                parent[find(i)] = find(j)
    out = {}
    for i, r in enumerate(rects):
        out.setdefault(find(i), []).append(r)
    return list(out.values())


def fmt(v):
    return ("%g" % v).replace(".", "p")


def key_of(kind, **par):
    return kind + "_" + "_".join(f"{k}{fmt(v)}" for k, v in sorted(par.items()))


def generate(specs):
    """Draw each device once with the generator of the PDK. specs: key -> (device, parameters).
    Returns key -> (cell of the generator, bounding box, flat layers in the coordinates of that cell)."""
    for pattern in ("gen_*.mag", "flat_*.mag", "sky130_fd_pr__*.mag", "devices.out"):
        for old in BUILD.glob(pattern):
            old.unlink()
    lines = ["set fh [open devices.out w]"]
    for key, (dev, par) in sorted(specs.items()):
        args = " ".join(f"{k} {v}" for k, v in par.items())
        lines += [f"load gen_{key} -force", "box 0 0 0 0",
                  f"magic::gencell sky130::sky130_fd_pr__{dev} d1 {args}",
                  f"set m [cellname list children gen_{key}]",
                  "load $m", "select top cell", "set b [box values]",
                  f"flatten flat_{key}", f"puts $fh \"{key} $m $b\"",
                  f"load flat_{key}", f"save flat_{key}"]
    lines += ["close $fh", "writeall force", "quit -noprompt"]
    (BUILD / "devices.tcl").write_text("\n".join(lines) + "\n")
    run_magic("devices.tcl", "devices.log")
    out = {}
    for line in (BUILD / "devices.out").read_text().splitlines():
        key, master, *box = line.split()
        out[key] = (master, tuple(int(v) for v in box), read_mag(BUILD / f"flat_{key}.mag"))
    assert set(out) == set(specs), sorted(set(specs) - set(out))
    return out


def pad(layer, c, r):
    h = WIRE[layer] // 2
    return (c * P - h, r * P - h, c * P + h, r * P + h)


def floor_div(a, b):
    return a // b


def ceil_div(a, b):
    return -((-a) // b)


def shift(r, dx, dy):
    return (r[0] + dx, r[1] + dy, r[2] + dx, r[3] + dy)


def ring_exit(c, ring, side):
    """Contact on the guard ring and a metal1 exit to a grid node. The ring is 34 units wide, on li."""
    if side == "down":
        y1 = ring[1]
        c.add(None, (-17, y1, 17, y1 + 34), None, "viali")
        r = floor_div(y1, P)
        c.add("m1", (-34, r * P - 34, 34, y1 + 40), "B", "metal1")
        c.pins["B"] = [("m1", 0, r)]
    elif side == "left":
        x1 = ring[0]
        c.add(None, (x1, -17, x1 + 34, 17), None, "viali")
        col = floor_div(x1, P)
        c.add("m1", (col * P - 34, -34, x1 + 40, 34), "B", "metal1")
        c.pins["B"] = [("m1", col, 0)]


def mos(key, gen, model, w, l, nf):
    """A transistor with its exits. w is the width of one finger, in um."""
    master, box, flat = gen
    ntype = model.startswith("nfet")
    cols = sorted(hull(g) for g in groups(flat["metal1"])
                  if any(overlap(hull(g), d) for d in flat["ndiffc" if ntype else "pdiffc"]))
    gates = [g for g in groups(flat["metal1"]) if any(overlap(hull(g), p) for p in flat["polycont"])]
    assert len(cols) == nf + 1 and len(gates) == 1, (key, len(cols), len(gates))
    gate = hull(gates[0])
    ring = hull(flat["psubdiffcont" if ntype else "nsubdiffcont"])
    xr = (gate[0] + gate[2]) // 2
    yr = (cols[0][1] + cols[0][3]) // 2
    c = Comp("dev_" + key)
    c.uses.append((master, "d1", False, -xr, -yr, box))
    c.grow(shift(box, -xr, -yr))
    cols = [shift(r, -xr, -yr) for r in cols]
    gate, ring = shift(gate, -xr, -yr), shift(ring, -xr, -yr)
    for i, r in enumerate(cols):
        c.shapes.append(("m1",) + r + ("S" if i % 2 == 0 else "D",))
    for r in gates[0]:
        c.shapes.append(("m1",) + shift(r, -xr, -yr) + ("G",))
    half = WIRE["m1"] // 2
    if nf == 1:
        s, d = cols
        assert s[3] - s[1] >= WIRE["m1"], key
        cs, cd = floor_div(s[0], P), ceil_div(d[2], P)
        c.add("m1", (cs * P - half, -half, s[2], half), "S", "metal1")
        c.add("m1", (d[0], -half, cd * P + half, half), "D", "metal1")
        c.pins["S"], c.pins["D"] = [("m1", cs, 0)], [("m1", cd, 0)]
    else:
        h2, cut = WIRE["m2"] // 2, CUT["v1"] // 2
        for net, row, sel in (("S", -1, cols[0::2]), ("D", 1, cols[1::2])):
            y = row * P
            assert sel[0][1] + 40 <= y - h2 and y + h2 <= sel[0][3] - 40, key
            xs = [(r[0] + r[2]) // 2 for r in sel]
            for x in xs:
                c.add(None, (x - cut, y - cut, x + cut, y + cut), None, "via1")
                c.cuts.append(("v1", x - cut, y - cut, x + cut, y + cut))
                c.add("m1", (x - half, y - half, x + half, y + half), net, "metal1")
            c1, c2 = floor_div(xs[0], P), ceil_div(xs[-1], P)
            if net == "S":
                c1 -= 1                     # the source leaves on the left, the drain on the right
            else:
                c2 += 1
            c.add("m2", (c1 * P - h2, y - h2, c2 * P + h2, y + h2), net, "metal2")
            c.pins[net] = [("m2", col, row) for col in range(c1, c2 + 1)]
    rg = ceil_div(gate[1] + half, P)
    c.add("m1", (-half, gate[1], half, rg * P + half), "G", "metal1")
    c.pins["G"] = [("m1", 0, rg)]
    ring_exit(c, ring, "down")
    well = flat.get("nwell")
    if well:
        c.nwell.append(shift(hull(well), -xr, -yr))
    else:
        c.nkeep.append((ring[0] - 17, ring[1] - 17, ring[2] + 17, ring[3] + 17))
    c.devices.append(("", "sky130_fd_pr__" + model, dict(w=w * nf, l=l), ["D", "G", "S", "B"]))
    return c


def res(key, gen, model, length, series=1):
    """A poly resistor with its exits. length is the length netgen will read, in um.
    With series > 1 the generator draws that many separate strips and they are joined here in
    series, on metal1, top and bottom in turn: the snake of the generator breaks the width rule
    of the resistor implant at its two ends."""
    master, box, flat = gen
    ends = sorted(hull(g) for g in groups(flat["metal1"]))
    ring = hull(flat["psubdiffcont"])
    xr, yr = (ring[0] + ring[2]) // 2, (ring[1] + ring[3]) // 2
    c = Comp("dev_" + key)
    c.uses.append((master, "d1", False, -xr, -yr, box))
    c.grow(shift(box, -xr, -yr))
    ring = shift(ring, -xr, -yr)
    ends = [shift(e, -xr, -yr) for e in ends]
    half = WIRE["m1"] // 2
    nets = ["R1", "R2"]
    if series > 1:
        assert len(ends) == 2 * series, key
        low, high = ends[0::2], ends[1::2]                  # sorted by x, then y: bottom and top of each strip
        nets = ["R1"] + [f"s{k}" for k in range(1, series)] + ["R2"]
        for k in range(series - 1):
            pair = high[k:k + 2] if k % 2 == 0 else low[k:k + 2]
            c.add("m1", hull(pair), nets[k + 1], "metal1")
        for k in range(series):
            a, b = (nets[k], nets[k + 1]) if k % 2 == 0 else (nets[k + 1], nets[k])
            c.devices.append((f"s{k}", "sky130_fd_pr__" + model, dict(l=length / series), [a, b, "B"]))
        ends = [low[0], low[-1] if series % 2 == 0 else high[-1]]
    else:
        c.devices.append(("", "sky130_fd_pr__" + model, dict(l=length), ["R1", "R2", "B"]))
    assert len(ends) == 2, key
    for net, r in zip(("R1", "R2"), ends):
        c.shapes.append(("m1",) + r + (net,))
        cx = (r[0] + r[2]) // 2
        down = (r[1] + r[3]) // 2 < 0
        row = floor_div(r[1] - half, P) if down else ceil_div(r[3] + half, P)
        col = round(cx / P) if abs(cx) < half else (floor_div(cx, P) if cx < 0 else ceil_div(cx, P))
        x1, x2 = min(r[0], cx - half), max(r[2], cx + half)
        if down:
            c.add("m1", (x1, row * P - half, x2, r[1] + 2), net, "metal1")
        else:
            c.add("m1", (x1, r[3] - 2, x2, row * P + half), net, "metal1")
        c.add("m1", (min(col * P, cx) - half, row * P - half, max(col * P, cx) + half, row * P + half), net, "metal1")
        c.pins[net] = [("m1", col, row)]
    ring_exit(c, ring, "left")
    c.nkeep.append(c.bbox)
    return c


def mim_layers(c, x, y, side, net_t, net_b, bottom=True):
    """One plate of MIM capacitor with its lower-left corner at (x, y). The bottom plate is metal3,
    0.2 um larger than the capacitor layer on every side; the top contact and its metal4 are
    0.2 um smaller."""
    c.add(None, (x, y, x + side, y + side), None, "mimcap")
    c.add(None, (x + 40, y + 40, x + side - 40, y + side - 40), None, "mimcapcontact")
    c.add("m4", (x + 39, y + 39, x + side - 39, y + side - 39), net_t, "metal4")
    if bottom:
        c.add("m3", (x - 40, y - 40, x + side + 40, y + side + 40), net_b, "metal3")
    c.keeps.append(("m3", x, y, x + side, y + side, net_b, 272))     # 1.34 um to metal3 of another net
    for low in ("m1", "m2"):                        # nothing on metal1 or metal2 under a capacitor (capm.10)
        c.shapes.append((low, x, y, x + side, y + side, "!none"))
    c.cuts.append(("v2", x - 20, y - 20, x + side + 20, y + side + 20))       # no via2 under the capacitor
    c.cuts.append(("v3", x - 20, y - 20, x + side + 20, y + side + 20))


def mim(key, side_um, count=1, per_row=None):
    """`count` plates in parallel on one bottom plate, `per_row` in a row. Exits at the bottom edge:
    the top plates on metal4 at column 0 of each plate of the lowest row, the bottom plate on metal3
    at column 3."""
    side = round(side_um * UM)
    per_row = per_row or count
    c = Comp("dev_" + key)
    y0 = 3 * P                                      # the metal3 under the top-plate exit is 1.34 um away
    pitch = ceil_div(side + 80 + 240, P) * P
    nrow = ceil_div(count, per_row)
    for k in range(count):
        i, j = k % per_row, k // per_row
        x0, y = -2 * P + i * pitch, y0 + j * pitch
        mim_layers(c, x0, y, side, "T", "B", bottom=False)
        if j == 0:
            c.add("m4", (x0 + 2 * P - 38, -38, x0 + 2 * P + 38, y0 + 40), "T", "metal4")
            if i:
                c.add("m4", (x0 + 2 * P - pitch - 38, -38, x0 + 2 * P + 38, 38), "T", "metal4")
        else:                                       # a plate above another: joined across the gap
            c.add("m4", (x0 + side // 2 - 200, y - pitch + side - 50, x0 + side // 2 + 200, y + 50), "T", "metal4")
    c.add("m3", (-2 * P - 40, y0 - 40, -2 * P + (per_row - 1) * pitch + side + 40,
                 y0 + (nrow - 1) * pitch + side + 40), "B", "metal3")
    c.add("m3", (3 * P - 38, -38, 3 * P + 38, y0 - 40), "B", "metal3")
    c.pins["T"] = [("m4", i * pitch // P, 0) for i in range(per_row)]
    c.pins["B"] = [("m3", 3, 0)]
    c.devices.append(("", "sky130_fd_pr__cap_mim_m3_1", dict(w=side_um, l=side_um, m=count), ["T", "B"]))
    return c


ARRAY_PITCH = 23 * P        # 15.64 um: the plates of two nets are then 1.34 um from each other's metal3


def cap_array(key, side_um, nx, ny, sensor, dummies):
    """The feedback capacitor and the sensor capacitor of one port: nx x ny plates of one size.

      feedback plates   top plates joined on metal4 (net `sum`), on one metal3 sheet (net `vmem`);
      sensor plate      at `sensor` = (column, row) of the bottom row, on its own bottom plate
                        (net `vss`), top plate `vs`;
      dummy plates      at `dummies`, on the sheet, top plate tied to the sheet: both on `vmem`.

    Exits at the bottom edge, as for `mim`. There is no ring of dummies around the array.
    """
    side = round(side_um * UM)
    c = Comp("dev_" + key)
    y0, pitch = 3 * P, ARRAY_PITCH
    assert side + 328 <= pitch and sensor[1] == 0
    kind = {(i, j): "f" for i in range(nx) for j in range(ny)}
    kind[sensor] = "s"
    for d in dummies:
        kind[d] = "d"

    def corner(i, j):
        return -2 * P + i * pitch, y0 + j * pitch

    # the sheet: every row above the bottom one, and the bottom row on both sides of the sensor plate
    x_end = corner(nx - 1, 0)[0] + side + 40
    c.add("m3", (-2 * P - 40, y0 + pitch - 40, x_end, corner(0, ny - 1)[1] + side + 40), "vmem", "metal3")
    if sensor[0] > 0:
        c.add("m3", (-2 * P - 40, y0 - 40, corner(sensor[0] - 1, 0)[0] + side + 40, y0 + pitch), "vmem", "metal3")
    if sensor[0] < nx - 1:
        c.add("m3", (corner(sensor[0] + 1, 0)[0] - 40, y0 - 40, x_end, y0 + pitch), "vmem", "metal3")
    counts = dict(f=0, s=0, d=0)
    for (i, j), k in sorted(kind.items()):
        x, y = corner(i, j)
        counts[k] += 1
        top, bot = {"f": ("sum", "vmem"), "s": ("vs", "vss"), "d": ("vmem", "vmem")}[k]
        mim_layers(c, x, y, side, top, bot, bottom=(k == "s"))
        if k == "f":
            for di, dj in ((1, 0), (0, 1)):                 # joined to the feedback plate on its right and above
                if kind.get((i + di, j + dj)) == "f":
                    if di:
                        c.add("m4", (x + side - 50, y + side // 2 - 200, x + pitch + 50, y + side // 2 + 200), "sum", "metal4")
                    else:
                        c.add("m4", (x + side // 2 - 200, y + side - 50, x + side // 2 + 200, y + pitch + 50), "sum", "metal4")
        if k == "d":
            # tie to the sheet, in the gap on the side where the sheet continues
            left = kind.get((i - 1, j)) in ("f", "d")
            gx = x - (pitch - side) // 2 if left else x + side + (pitch - side) // 2
            gy = y + side // 2
            c.add(None, (gx - 32, gy - 32, gx + 32, gy + 32), None, "via3")
            c.add("m3", (gx - 38, gy - 38, gx + 38, gy + 38), "vmem", "metal3")
            c.add("m4", (min(gx - 38, x + 39), gy - 38, max(gx + 38, x + side - 39), gy + 38), "vmem", "metal4")
    # exits
    pins = {"sum": [], "vmem": [], "vs": [], "vss": []}
    for i in range(nx):
        x, _ = corner(i, 0)
        k = kind[(i, 0)]
        if k == "d":
            continue
        top, bot = ("sum", "vmem") if k == "f" else ("vs", "vss")
        col = (x + 2 * P) // P
        c.add("m4", (col * P - 38, -38, col * P + 38, y0 + 40), top, "metal4")
        c.add("m3", ((col + 3) * P - 38, -38, (col + 3) * P + 38, y0 - 40), bot, "metal3")
        pins[top].append(("m4", col, 0))
        pins[bot].append(("m3", col + 3, 0))
    c.pins = pins
    c.devices.append(("f", "sky130_fd_pr__cap_mim_m3_1", dict(w=side_um, l=side_um, m=counts["f"]), ["sum", "vmem"]))
    c.devices.append(("s", "sky130_fd_pr__cap_mim_m3_1", dict(w=side_um, l=side_um, m=1), ["vs", "vss"]))
    c.devices.append(("d", "sky130_fd_pr__cap_mim_m3_1", dict(w=side_um, l=side_um, m=counts["d"]), ["vmem", "vmem"]))
    c.counts = counts
    return c
