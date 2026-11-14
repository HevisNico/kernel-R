"""Assembly of a block: placed cells, wires on the routing grid, labels.

A block is a list of placed cells (devices with their exits, or blocks built earlier) and, for each
of their terminals, the net it belongs to. `Block.build` routes every net on the grid of tech.py
and returns the block as a `Comp`, ready to be placed in a larger block.

Rules the router keeps, so that what it draws is clean by construction:

  - a wire is a chain of grid nodes on one layer; a via joins two layers at one node;
  - a node is usable by a net if no shape of another net is nearer to the pad of the node than the
    spacing of the layer (0.28 um or 0.4 um to a shape wider than 3 um), and if the pad either
    overlaps a shape of its own net or stays a full spacing away from it;
  - a via is not placed next to a contact that is not on the grid.

Nets are routed one after the other, shortest first; each net by Dijkstra from what is already
connected to the nearest terminal not yet connected. Nothing is ripped up: a net that finds no
path stops the build.

Classes of nets (second layout, extended in layout 2.1). A block names

    "qs"  its critical nets: `vq` and the summing nodes;
    "q"   its other protected nets (layout 2.1): `x`, `vgd`, `dq`, `gm`;
    "qa"  `vs` (layout 2.1): protected from the loud nets, and itself loud for the critical nets;
    "a"   its loud nets, those that swing by more than 0.5 V.

A net also takes the class of the terminal of a placed block it is connected to.

  - A loud wire and a protected one (and `vs` and a critical one) are never nearer than 1.4 um on
    the same layer or on the layers next to it, and never over or under each other on any layer
    (0.5 um aside). The rule counts every shape of the two classes, wires and exits of devices
    alike. It is waived within three tracks of the exit of a transistor that carries both nets (a
    switch has its control beside its channel) and, in layout 2.1, of the pin of a block that has
    nets of the other class inside.
  - Layout 2.1. Inside that waiver a wire still does not pass on a track next to the exit of a
    terminal of the other class: it does not wrap the gate of a switch. And where a wire may go,
    it is pushed away from the shapes of the other class that are less than 8.2 um away, on any
    layer, by a cost on each step: Magic couples two shapes up to 8 um apart, on one layer when
    nothing lies between them, and from one layer to another by the fringe of their edges. A
    cost, not a rule: a wire still goes there when there is no other way. The waiver holds on
    metal1 and metal2 only, where the exits are.
  - The nets a block asks to shield (the critical nets and, in layout 2.1, `x` and `vgd`) are
    routed first. Each then gets a `vss` wire on the tracks beside it, wherever the track is free;
    those wires are joined to `vss` when `vss` is routed. Magic couples two wires of a layer only
    if nothing lies between them: the shield takes the coupling to `vss`. The other protected nets
    are routed next, then the rest.
  - A block may ask that a net reach a given node (`exits`), so that a critical net leaves the
    block by a wire drawn inside it.
"""
import heapq
import os

import numpy as np

from devices import Comp, ceil_div, floor_div, hull, overlap, pad
from tech import CUT, CUT_SPACE, LAYERS, MAGIC, MIN_AREA, P, SPACE, VIAS, WIDE, WIDE_SPACE, WIRE

KEEP_NEAR = 280                                     # 1.4 um: a loud shape and a critical one, same layer or the next
KEEP_FAR = 100                                      # 0.5 um aside on the other layers: never over or under
BUBBLE = 3                                          # tracks around the exit of a device that carries both nets
HALO = 1640                                         # 8.2 um: Magic couples two shapes of a layer up to 8 um apart
HALO_COST = 20                                      # added to a step that ends that near a shape of the other class
STEP = {"m1": 10, "m2": 10, "m3": 11, "m4": 22}
PREFER = {"m1": 0, "m2": 1, "m3": 0, "m4": 1}       # 0: along x, 1: along y
VIA_COST = 30
MARGIN = 3


def tr_rect(r, mx, tx, ty):
    return (tx - r[2], r[1] + ty, tx - r[0], r[3] + ty) if mx else (r[0] + tx, r[1] + ty, r[2] + tx, r[3] + ty)


def footprint(comp):
    """Columns and rows a cell covers, exits included."""
    b = comp.bbox
    c1, r1, c2, r2 = floor_div(b[0], P), floor_div(b[1], P), ceil_div(b[2], P), ceil_div(b[3], P)
    for nodes in comp.pins.values():
        for _, c, r in nodes:
            c1, r1, c2, r2 = min(c1, c), min(r1, r), max(c2, c), max(r2, r)
    return c1, r1, c2, r2


class Block:
    def __init__(self, name):
        self.name = name
        self.insts = []             # (instance, comp, column, row, mirror)
        self.conn = {}              # (instance, terminal) -> net
        self.exports = []
        self.critical = set()       # "qs": kept away from loud nets and from `vs`
        self.protected = set()      # "q": kept away from loud nets
        self.both = set()           # "qa": `vs`, kept away from loud nets, and loud for the critical nets
        self.loud = set()           # "a": nets that swing by more than 0.5 V
        self.shield = set()         # nets that get vss wires beside them
        self.forbid = {}            # net -> [(column, row, column, row)]: tracks its wires stay out of, on every layer
        self.exits = {}             # net -> (layer, column, row): a node the net must reach

    def place(self, inst, comp, col, row, mirror=False, **conn):
        self.insts.append((inst, comp, col, row, mirror))
        for pin, net in conn.items():
            self.conn[(inst, pin)] = net

    def rows(self, rows, comps, conn, col0=0, row0=0, gap=2, rowgap=2):
        """Place rows of cells, bottom row first, each row from the left. An entry is an instance
        name, (instance name, True) for a cell mirrored left to right, a number of empty tracks,
        or a list of rows: a stack that takes one place in its row. A row that is a number is that
        many empty tracks of height. Returns the width and height taken, in tracks."""
        base, width = row0, 0
        for row in rows:
            if isinstance(row, int):
                base += row
                continue
            cur, top = col0, base
            for entry in row:
                if isinstance(entry, int):              # an empty space of that many tracks
                    cur += entry
                    continue
                if isinstance(entry, list):
                    w, h = self.rows(entry, comps, conn, cur, base, gap, rowgap)
                else:
                    inst, mx = entry if isinstance(entry, tuple) else (entry, False)
                    c1, r1, c2, r2 = footprint(comps[inst])
                    if mx:
                        c1, c2 = -c2, -c1
                    self.place(inst, comps[inst], cur - c1, base - r1, mx, **conn[inst])
                    w, h = c2 - c1 + 1, r2 - r1 + 1
                cur += w + gap
                top = max(top, base + h)
            width = max(width, cur - gap - col0)
            base = top + rowgap
        return width, base - rowgap - row0

    # ---- build

    def build(self, verbose=False):
        out = Comp(self.name)
        nets = sorted(set(self.conn.values()))
        nid = {n: k + 1 for k, n in enumerate(nets)}
        other = {}                                    # nets inside the placed cells

        def owner(inst, comp, local):
            if (inst, local) in self.conn:
                return nid[self.conn[(inst, local)]]
            return other.setdefault((inst, local), len(nets) + 1 + len(other))

        comp_of = {inst: comp for inst, comp, _, _, _ in self.insts}
        cls = {}                                      # net -> "q" or "a"
        for (inst, pin), net in self.conn.items():
            c = comp_of[inst].net_class.get(pin)
            if c in ("q", "qa", "qs") or (c == "a" and net not in cls):
                cls[net] = c
        cls.update({n: "a" for n in self.loud if n in nid})
        cls.update({n: "q" for n in self.protected if n in nid})
        cls.update({n: "qs" for n in self.critical if n in nid})
        cls.update({n: "qa" for n in self.both if n in nid})

        shapes, cuts, keeps, terms, pin_nodes = [], [], [], {}, {}
        for inst, comp, col, row, mx in self.insts:
            tx, ty = col * P, row * P
            out.uses.append((comp.name, inst, mx, tx, ty, comp.bbox))
            out.grow(tr_rect(comp.bbox, mx, tx, ty))
            missing = [p for p in comp.pins if (inst, p) not in self.conn]
            assert not missing, f"{self.name}: {inst} has unconnected terminals {missing}"
            for layer, x1, y1, x2, y2, local in comp.shapes:
                shapes.append((layer, tr_rect((x1, y1, x2, y2), mx, tx, ty), owner(inst, comp, local)))
            for v, x1, y1, x2, y2 in comp.cuts:
                cuts.append((v, tr_rect((x1, y1, x2, y2), mx, tx, ty)))
            for layer, x1, y1, x2, y2, local, dist in comp.keeps:
                keeps.append((layer, tr_rect((x1, y1, x2, y2), mx, tx, ty), owner(inst, comp, local), dist))
            for pin, nodes in comp.pins.items():
                net = self.conn[(inst, pin)]
                terms.setdefault(net, []).append([(L, (-c if mx else c) + col, r + row) for L, c, r in nodes])
                pin_nodes[(inst, pin)] = terms[net][-1]
            out.nwell += [tr_rect(r, mx, tx, ty) for r in comp.nwell]
            out.nkeep += [tr_rect(r, mx, tx, ty) for r in comp.nkeep]
            for path, model, par, tnets in comp.devices:
                mapped = [self.conn.get((inst, t), f"{inst}/{t}") for t in tnets]
                out.devices.append((f"{inst}/{path}" if path else inst, model, par, mapped))

        for net, node in self.exits.items():
            terms.setdefault(net, []).append([node])
            out.grow(pad(node[0], node[1], node[2]))
        ocls = {nid[n]: c for n, c in cls.items()}
        for (inst, local), oid in other.items():
            c = comp_of[inst].net_class.get(local)
            if c:
                ocls[oid] = c

        b = out.bbox
        c0, r0 = floor_div(b[0], P) - MARGIN, floor_div(b[1], P) - MARGIN
        nc, nr = ceil_div(b[2], P) + MARGIN - c0 + 1, ceil_div(b[3], P) + MARGIN - r0 + 1
        occ = {L: np.zeros((nc, nr), np.int32) for L in LAYERS}
        tch = {L: np.zeros((nc, nr), np.int32) for L in LAYERS}
        miss = {L: np.zeros((nc, nr), np.int32) for L in LAYERS}
        vblk = {v: np.zeros((nc, nr), bool) for v in VIAS}

        def span(lo, hi, origin, n, strict):
            """Indices i with lo < origin+i (strict) or lo <= origin+i, in units of P."""
            a = floor_div(lo, P) + 1 if strict else ceil_div(lo, P)
            z = ceil_div(hi, P) - 1 if strict else floor_div(hi, P)
            return max(a - origin, 0), min(z - origin, n - 1) + 1

        def raster(layer, r, oid, keepout=0):
            """Mark the nodes whose pad is nearer to the shape than the spacing. A keep-out is a zone
            around a shape, wider than the spacing of the layer, that other nets stay out of."""
            h = WIRE[layer] // 2
            s = WIDE_SPACE[layer] if min(r[2] - r[0], r[3] - r[1]) > WIDE else SPACE[layer]
            s = max(s, keepout)
            i0, i1 = span(r[0] - h - s, r[2] + h + s, c0, nc, True)
            j0, j1 = span(r[1] - h - s, r[3] + h + s, r0, nr, True)
            if i0 >= i1 or j0 >= j1:
                return
            sub = occ[layer][i0:i1, j0:j1]
            sub[(sub != 0) & (sub != oid)] = -1
            sub[sub == 0] = oid
            near = np.ones((i1 - i0, j1 - j0), bool)
            a0, a1 = span(r[0] - h, r[2] + h, c0, nc, False)
            b0, b1 = span(r[1] - h, r[3] + h, r0, nr, False)
            if a0 < a1 and b0 < b1:
                near[a0 - i0:a1 - i0, b0 - j0:b1 - j0] = False
                sub = tch[layer][a0:a1, b0:b1]
                sub[(sub != 0) & (sub != oid)] = -1
                sub[sub == 0] = oid
            sub = miss[layer][i0:i1, j0:j1]
            sub[near & (sub != 0) & (sub != oid)] = -1
            sub[near & (sub == 0)] = oid

        for layer, r, oid in shapes:
            raster(layer, r, oid)
        for layer, r, oid, dist in keeps:
            raster(layer, r, oid, dist)

        # zones: where a wire of the other class may not go
        # each holds the net whose shape is near, or -2 where shapes of several nets are
        zq = {L: np.zeros((nc, nr), np.int32) for L in LAYERS}      # near a protected shape ("q", "qs", "qa")
        za = {L: np.zeros((nc, nr), np.int32) for L in LAYERS}      # near a loud shape ("a")
        zs = {L: np.zeros((nc, nr), np.int32) for L in LAYERS}      # near a shape of `vs` ("qa")
        zc = {L: np.zeros((nc, nr), np.int32) for L in LAYERS}      # near a critical shape ("qs")
        # the zones a net of each class stays out of
        AVOID = {"a": (zq,), "q": (za,), "qs": (za, zs), "qa": (za, zc)}
        MARKS = {"a": (za,), "q": (zq,), "qs": (zq, zc), "qa": (zq, zs)}
        # the same, 8.2 um wide: where a step costs more
        wide = {id(z): {L: np.zeros((nc, nr), np.int32) for L in LAYERS} for z in (zq, za, zs, zc)}

        def against(mine, other):
            return other in MARKS and any(z is y for z in AVOID[mine] for y in MARKS[other])

        def mark(layer, r, c, oid):
            for L in LAYERS:
                keep = KEEP_NEAR if abs(LAYERS.index(L) - LAYERS.index(layer)) <= 1 else KEEP_FAR
                h = WIRE[L] // 2
                i0, i1 = span(r[0] - h - keep, r[2] + h + keep, c0, nc, True)
                j0, j1 = span(r[1] - h - keep, r[3] + h + keep, r0, nr, True)
                if i0 < i1 and j0 < j1:
                    for zone in MARKS[c]:
                        sub = zone[L][i0:i1, j0:j1]
                        sub[(sub != 0) & (sub != oid)] = -2
                        sub[sub == 0] = oid
            h = WIRE[layer] // 2
            i0, i1 = span(r[0] - h - HALO, r[2] + h + HALO, c0, nc, True)
            j0, j1 = span(r[1] - h - HALO, r[3] + h + HALO, r0, nr, True)
            if i0 < i1 and j0 < j1:
                for zone in MARKS[c]:
                    for L in LAYERS:        # on every layer: a wire above or below is not better than one beside
                        sub = wide[id(zone)][L][i0:i1, j0:j1]
                        sub[(sub != 0) & (sub != oid)] = -2
                        sub[sub == 0] = oid

        for layer, r, oid in shapes:
            if oid in ocls:
                mark(layer, r, ocls[oid], oid)
        for v, r in cuts:
            h, s = CUT[v] // 2, CUT_SPACE[v]
            i0, i1 = span(r[0] - h - s, r[2] + h + s, c0, nc, True)
            j0, j1 = span(r[1] - h - s, r[3] + h + s, r0, nr, True)
            if i0 < i1 and j0 < j1:
                vblk[v][i0:i1, j0:j1] = True

        nl = len(LAYERS)

        def index(L, c, r):
            return (LAYERS.index(L) * nc + (c - c0)) * nr + (r - r0)

        wires = {}                                    # net -> list of (layer, rect)
        vias = {}                                     # net -> list of (via, column, row)
        used = {}                                     # net -> set of indices
        shielded = {n for n in self.shield if n in nid}
        order = sorted(nets, key=lambda n: (0 if n in shielded else (1 if "q" in cls.get(n, "") else 2), len(terms.get(n, [])), n))
        assert all("q" in cls[n] for n in shielded)
        critical = [n for n in order if n in shielded]
        plane = nc * nr
        shield_wires, self.shield_nodes = [], 0

        def shields():
            """vss wires on the free tracks beside the critical wires."""
            if "vss" not in nid or not critical:
                return
            vs = nid["vss"]
            mine = set().union(*(used[n] for n in critical))
            exits_of_others = set()                   # no shield beside the exit of a terminal: it must stay reachable
            for n, groups_ in terms.items():
                if n != "vss":
                    for g in groups_:
                        for node in g:
                            i = index(*node)
                            exits_of_others.update((i, i + 1, i - 1, i + nr, i - nr))
            cand = set()
            for i in mine:
                li, rest = divmod(i, plane)
                ci, ri = divmod(rest, nr)
                for dc, dr in ((1, 0), (-1, 0), (0, 1), (0, -1)):
                    c2, r2 = ci + dc, ri + dr
                    j = (li * nc + c2) * nr + r2
                    if 0 <= c2 < nc and 0 <= r2 < nr and j not in mine and j not in exits_of_others and occ[LAYERS[li]][c2, r2] == 0:
                        cand.add(j)
            while cand:
                group, stack = [], [cand.pop()]
                while stack:
                    j = stack.pop()
                    group.append(j)
                    li, rest = divmod(j, plane)
                    ci, ri = divmod(rest, nr)
                    for k in ((j + nr) if ci < nc - 1 else -1, (j - nr) if ci > 0 else -1, (j + 1) if ri < nr - 1 else -1, (j - 1) if ri > 0 else -1):
                        if k in cand:
                            cand.discard(k)
                            stack.append(k)
                L = LAYERS[group[0] // plane]
                if len(group) < 2 and L in ("m3", "m4"):      # a pad alone there is below the minimum area
                    continue
                members = set(group)
                nodes = []
                for j in group:
                    rest = j % plane
                    ci, ri = divmod(rest, nr)
                    occ[L][ci, ri] = vs
                    tch[L][ci, ri] = vs
                    nodes.append((L, ci + c0, ri + r0))
                    shield_wires.append((L, pad(L, ci + c0, ri + r0)))
                    if j + nr in members:
                        shield_wires.append((L, hull([pad(L, ci + c0, ri + r0), pad(L, ci + c0 + 1, ri + r0)])))
                    if j + 1 in members:
                        shield_wires.append((L, hull([pad(L, ci + c0, ri + r0), pad(L, ci + c0, ri + r0 + 1)])))
                terms.setdefault("vss", []).append(nodes)
                self.shield_nodes += len(group)

        for position, net in enumerate(order):
            if position == len(critical):
                shields()
            me = nid[net]
            # usable: no shape of another net within the spacing, and no shape of this net that the
            # pad would come near without touching
            free = {L: (occ[L] == 0) | ((occ[L] == me) & (miss[L] != me)) for L in LAYERS}
            if net in cls:
                mine = cls[net]
                zone = {L: np.zeros((nc, nr), bool) for L in LAYERS}
                for L in LAYERS:
                    for z in AVOID[mine]:
                        zone[L] |= (z[L] != 0) & (z[L] != me)
                for inst, comp in comp_of.items():
                    # a transistor that carries both nets, or (layout 2.1) a block that has nets of the
                    # other class inside: the exit of the net there cannot be kept away from them
                    here = {pin: self.conn[(inst, pin)] for pin in comp.pins}
                    if comp.name.startswith("dev_"):
                        mixed = any(n != net and against(mine, cls.get(n)) for n in here.values())
                    else:
                        mixed = any(against(mine, c) for pin, c in comp.net_class.items() if here.get(pin) != net)
                    if net in here.values() and mixed:
                        for pin, n in here.items():
                            if n == net:
                                for _, c, r in pin_nodes[(inst, pin)]:
                                    i, j = c - c0, r - r0
                                    for L in LAYERS[:2]:    # layout 2.1: on metal1 and metal2 only, where the exits are
                                        zone[L][max(i - BUBBLE, 0):i + BUBBLE + 1, max(j - BUBBLE, 0):j + BUBBLE + 1] = False
                # not on a track next to the exit of a terminal of the other class, waiver or not
                for (inst, pin), n in self.conn.items():
                    if n != net and against(mine, cls.get(n)):
                        for L, c, r in pin_nodes[(inst, pin)]:
                            i, j = c - c0, r - r0
                            zone[L][max(i - 1, 0):i + 2, max(j - 1, 0):j + 2] = True
                free = {L: free[L] & ~zone[L] for L in LAYERS}
                far = np.concatenate([np.logical_or.reduce([(wide[id(z)][L] != 0) & (wide[id(z)][L] != me) for z in AVOID[mine]]).ravel()
                                      for L in LAYERS])
                pen = bytes(np.where(far, HALO_COST, 0).astype(np.uint8).tobytes())
            else:
                pen = bytes(nl * plane)
            for a1, b1, a2, b2 in self.forbid.get(net, ()):
                for L in LAYERS:
                    free[L][max(a1 - c0, 0):max(a2 - c0 + 1, 0), max(b1 - r0, 0):max(b2 - r0 + 1, 0)] = False
            ok = bytearray(np.concatenate([free[L].ravel() for L in LAYERS]).tobytes())
            vok = [(~vblk[v]).ravel().tobytes() for v in VIAS]
            groups = []
            for nodes in terms.get(net, []):
                # the exit of a terminal was drawn for it: it is usable whatever own shape is near
                good = []
                for L, c, r in nodes:
                    if occ[L][c - c0, r - r0] in (0, me):
                        ok[index(L, c, r)] = 1
                        good.append(index(L, c, r))
                assert good, f"{self.name}: a terminal of net {net} cannot be reached: {nodes[:3]}"
                groups.append(good)
            tree = set(groups[0]) if groups else set()
            todo = {i: k for k, g in enumerate(groups[1:], 1) for i in g}
            left = set(range(1, len(groups)))
            edges = []
            while left:
                dist = {i: 0 for i in tree}
                prev = {}
                heap = [(0, i) for i in tree]
                heapq.heapify(heap)
                found = None
                while heap:
                    d, i = heapq.heappop(heap)
                    if d > dist.get(i, 1 << 60):
                        continue
                    if i in todo and todo[i] in left:
                        found = i
                        break
                    li, rest = divmod(i, plane)
                    ci, ri = divmod(rest, nr)
                    L = LAYERS[li]
                    sx = STEP[L] if PREFER[L] == 0 else STEP[L] * 3 // 2
                    sy = STEP[L] if PREFER[L] == 1 else STEP[L] * 3 // 2
                    cand = []
                    if ci > 0:
                        cand.append((i - nr, sx))
                    if ci < nc - 1:
                        cand.append((i + nr, sx))
                    if ri > 0:
                        cand.append((i - 1, sy))
                    if ri < nr - 1:
                        cand.append((i + 1, sy))
                    if li < nl - 1 and vok[li][rest]:
                        cand.append((i + plane, VIA_COST))
                    if li > 0 and vok[li - 1][rest]:
                        cand.append((i - plane, VIA_COST))
                    for j, w in cand:
                        w += pen[j]
                        if ok[j] and d + w < dist.get(j, 1 << 60):
                            dist[j] = d + w
                            prev[j] = i
                            heapq.heappush(heap, (d + w, j))
                if found is None:
                    def where(i):
                        li, rest = divmod(i, plane)
                        ci, ri = divmod(rest, nr)
                        return (LAYERS[li], ci + c0, ri + r0)
                    stuck = {k: [where(i) for i in groups[k][:3]] for k in sorted(left)}
                    for i in list(groups[0])[:2]:
                        L, c, r = where(i)
                        around = {(dc, dr): (int(occ[L][c - c0 + dc, r - r0 + dr]), int(miss[L][c - c0 + dc, r - r0 + dr]),
                                             int(zq[L][c - c0 + dc, r - r0 + dr]), int(za[L][c - c0 + dc, r - r0 + dr]))
                                  for dc, dr in ((1, 0), (-1, 0), (0, 1), (0, -1))}
                        print(f"  stuck at {L} {c} {r} (net id {me}, class {cls.get(net)}): occ, miss, zq, za around: {around}")
                    if os.environ.get("ROUTE_DEBUG"):       # what the router saw, for the one who places the block
                        names = {v: k for k, v in nid.items()}
                        names.update({oid: f"{inst}/{local}" for (inst, local), oid in other.items()})
                        np.savez(os.environ["ROUTE_DEBUG"], c0=c0, r0=r0, names=np.array(sorted(names.items()), dtype=object),
                                 reached=np.array(sorted(dist)), ok=np.frombuffer(bytes(ok), np.uint8).reshape(len(LAYERS), nc, nr),
                                 **{f"occ_{L}": occ[L] for L in LAYERS}, **{f"zq_{L}": zq[L] for L in LAYERS},
                                 **{f"za_{L}": za[L] for L in LAYERS}, **{f"zs_{L}": zs[L] for L in LAYERS},
                                 **{f"zc_{L}": zc[L] for L in LAYERS})
                    raise AssertionError(f"{self.name}: no path for net {net}: reached {len(dist)} nodes from "
                                         f"{[where(i) for i in list(groups[0])[:3]]}; terminals left {stuck}")
                i = found
                while i not in tree:
                    edges.append((prev[i], i))
                    tree.add(i)
                    i = prev[i]
                k = todo[found]
                left.discard(k)
                tree.update(groups[k])
            used[net] = tree
            wires[net], vias[net] = [], []
            on_layer = {}
            for a, bb in edges:
                la, ra = divmod(a, plane)
                lb, rb = divmod(bb, plane)
                ca, wa = divmod(ra, nr)
                cb, wb = divmod(rb, nr)
                if la == lb:
                    L = LAYERS[la]
                    wires[net].append((L, hull([pad(L, ca + c0, wa + r0), pad(L, cb + c0, wb + r0)])))
                    on_layer.setdefault(L, set()).update((a, bb))
                else:
                    v = VIAS[min(la, lb)]
                    vias[net].append((v, ca + c0, wa + r0))
                    for l2 in (la, lb):
                        wires[net].append((LAYERS[l2], pad(LAYERS[l2], ca + c0, wa + r0)))
            # a pad alone on metal3 or metal4 is below the minimum area: lengthen it by one node
            for a, bb in edges:
                for i in (a, bb):
                    li, rest = divmod(i, plane)
                    L = LAYERS[li]
                    if L not in ("m3", "m4") or i in on_layer.get(L, ()):
                        continue
                    ci, ri = divmod(rest, nr)
                    if tch[L][ci, ri] == me:
                        continue
                    for dc, dr in ((1, 0), (-1, 0), (0, 1), (0, -1)):
                        c2, r2 = ci + dc, ri + dr
                        if 0 <= c2 < nc and 0 <= r2 < nr and ok[(li * nc + c2) * nr + r2]:
                            wires[net].append((L, hull([pad(L, ci + c0, ri + r0), pad(L, c2 + c0, r2 + r0)])))
                            j = (li * nc + c2) * nr + r2
                            on_layer.setdefault(L, set()).update((i, j))
                            tree.add(j)
                            break
                    else:
                        raise AssertionError(f"{self.name}: lone pad of {net} on {L} cannot be lengthened")
            # a ring of wires around one free node leaves a hole below the minimum area: fill it
            for i in list(tree):
                li, rest = divmod(i, plane)
                ci, ri = divmod(rest, nr)
                for dc, dr in ((1, 1), (1, -1), (-1, 1), (-1, -1), (1, 0), (-1, 0), (0, 1), (0, -1)):
                    c2, r2 = ci + dc, ri + dr
                    if not (0 < c2 < nc - 1 and 0 < r2 < nr - 1):
                        continue
                    j = (li * nc + c2) * nr + r2
                    if j in tree:
                        continue
                    ring = [(li * nc + c2 + a) * nr + r2 + b for a in (-1, 0, 1) for b in (-1, 0, 1) if a or b]
                    if all(k in tree for k in ring):
                        L = LAYERS[li]
                        assert ok[j], f"{self.name}: hole of {net} on {L} cannot be filled"
                        wires[net].append((L, hull([pad(L, c2 + c0, r2 + r0), pad(L, c2 + c0 + 1, r2 + r0)])))
                        wires[net].append((L, hull([pad(L, c2 + c0, r2 + r0), pad(L, c2 + c0, r2 + r0 + 1)])))
                        tree.add(j)
            # four nodes in a square leave a hole between their wires: cover it
            for i in tree:
                li, rest = divmod(i, plane)
                ci, ri = divmod(rest, nr)
                if ci < nc - 1 and ri < nr - 1 and i + 1 in tree and i + nr in tree and i + nr + 1 in tree:
                    L = LAYERS[li]
                    wires[net].append((L, hull([pad(L, ci + c0, ri + r0), pad(L, ci + c0 + 1, ri + r0 + 1)])))
            for i in tree:
                li, rest = divmod(i, plane)
                ci, ri = divmod(rest, nr)
                L = LAYERS[li]
                if occ[L][ci, ri] == 0:
                    occ[L][ci, ri] = me
                tch[L][ci, ri] = me
            if net in cls:
                for L, r in wires[net]:
                    mark(L, r, cls[net], me)
            if verbose:
                print(f"  {self.name}: {net}: {len(groups)} terminals, {len(edges)} steps")

        # ---- the block as a cell
        if shield_wires:
            wires["vss"] = wires["vss"] + shield_wires
        port = {n: k + 1 for k, n in enumerate(self.exports)}
        # the names behind the numbers, for estimate.py and for the one who reads a debug dump
        out.net_names = {f"#{nid[n]}": n for n in nets}
        out.inner = {f"#{oid}": key for key, oid in other.items()}
        out.children = dict(comp_of)
        for n, c in cls.items():
            out.net_class[n if n in port else f"#{nid[n]}"] = c
        for oid, c in ocls.items():
            if oid > len(nets):
                out.net_class[f"#{oid}"] = c
        for net in nets:
            for L, r in wires[net]:
                out.paint.setdefault(MAGIC[L], []).append(r)
                out.grow(r)
            for v, c, r in vias[net]:
                h = CUT[v] // 2
                out.paint.setdefault(MAGIC[v], []).append((c * P - h, r * P - h, c * P + h, r * P + h))
            # a label on a wire of the net; a net with no wire gets a pad on its terminal
            if wires[net]:
                L, r = wires[net][0]
                x, y = (r[0] + WIRE[L] // 2, r[1] + WIRE[L] // 2)
            else:
                L, c, r = terms[net][0][0]
                out.paint.setdefault(MAGIC[L], []).append(pad(L, c, r))
                wires[net].append((L, pad(L, c, r)))
                x, y = c * P, r * P
            out.labels.append((MAGIC[L], x, y, net, port.get(net)))
        for layer, r, oid in shapes:
            name = nets[oid - 1] if oid <= len(nets) else None
            out.shapes.append((layer,) + r + (name if name in port else f"#{oid}",))
        for net in nets:
            for L, r in wires[net]:
                out.shapes.append((L,) + r + (net if net in port else f"#{nid[net]}",))
        for v, r in cuts:
            out.cuts.append((v,) + r)
        for layer, r, oid, dist in keeps:
            name = nets[oid - 1] if oid <= len(nets) else None
            out.keeps.append((layer,) + r + (name if name in port else f"#{oid}", dist))
        for net in self.exports:
            nodes = []
            for i in used[net]:
                li, rest = divmod(i, plane)
                ci, ri = divmod(rest, nr)
                nodes.append((LAYERS[li], ci + c0, ri + r0))
            out.pins[net] = sorted(nodes)
        fill_wells(out)
        self.stats = dict(nets=len(nets), wire_um=sum((r[2] - r[0] + r[3] - r[1] - 2 * WIRE[L]) for n in nets for L, r in wires[n]) / 200,
                          vias=sum(len(vias[n]) for n in nets))
        return out


NWELL_SPACE = 254
NWELL_KEEP = 68


def fill_wells(comp):
    """Join n-wells that are nearer to each other than their spacing (1.27 um). The fill spans the
    gap over the full height (or width) of the two wells, so that no narrow neck is left."""
    wells = list(comp.nwell)
    changed = True
    fills = []
    while changed:
        changed = False
        for i in range(len(wells)):
            for j in range(i):
                a, b = wells[i], wells[j]
                gx = max(a[0], b[0]) - min(a[2], b[2])
                gy = max(a[1], b[1]) - min(a[3], b[3])
                if (gx > 0 or gy > 0) and gx < NWELL_SPACE and gy < NWELL_SPACE:
                    f = hull([a, b])
                    if f not in fills:
                        fills.append(f)
                        wells.append(f)
                        changed = True
    for f in fills:
        grown = (f[0] - NWELL_KEEP, f[1] - NWELL_KEEP, f[2] + NWELL_KEEP, f[3] + NWELL_KEEP)
        hit = [k for k in comp.nkeep if overlap(grown, k)]
        assert not hit, f"{comp.name}: an n-well fill {f} would cover an n device at {hit[0]}"
        comp.paint.setdefault("nwell", []).append(f)
    comp.nwell = wells
