"""The cell as the layout must contain it, read from ../../circuit/cell.spice and blocks.spice.

Nothing is typed by hand: the elements are those of role "cell" of ../inventory.py, with the nodes
the netlists give them. The two netlists are read and not changed.

  - Node 0 is called `vss`.
  - A sub-circuit keeps its ports that reach an element of the cell, gets `vss` if it uses node 0,
    and gets as further ports the nets that an element outside the cell reaches (an ideal source,
    a part of the test bench): the layout leaves those as pins.
  - The comparator exists in two sizes; each is a block of its own.
  - Ideal capacitors and resistors become devices of the PDK by the table `PARTS`. Their values in
    the simulations stay the ideal ones (decision D3); the sizes here are what is drawn.
"""
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent.parent))
import inventory  # noqa: E402

MOS = "sky130_fd_pr__"
FINGER_MAX = 10.0           # um: a wider transistor is drawn with several fingers

# name of the element -> (kind, model, what is drawn)
PARTS = {
    "cf": ("cap", "cap_mim_m3_1", dict(side=14.0, count=75, dummies=5)),
    "cs": ("cap", "cap_mim_m3_1", dict(side=14.0, count=1)),
    "cq": ("cap", "cap_mim_m3_1", dict(side=24.84, count=4, per_row=2)),
    "cc": ("cap", "cap_mim_m3_1", dict(side=27.22, count=1)),
    "cdp": ("cap", "cap_mim_m3_1", dict(side=22.2, count=2, per_row=2)),
    "cda": ("cap", "cap_mim_m3_1", dict(side=9.84, count=1)),
    "cdl": ("cap", "cap_mim_m3_1", dict(side=9.84, count=1)),
    "rleak": ("res", "res_xhigh_po_0p35", dict(length=1400.0, series=20)),
    "rz": ("res", "res_xhigh_po_1p41", dict(length=2.66, series=1)),
    "rda": ("res", "res_xhigh_po_0p35", dict(length=17.5, series=1)),
    "rdl": ("res", "res_xhigh_po_0p35", dict(length=17.5, series=1)),
    "rdp": ("res", "res_xhigh_po_0p35", dict(length=17.5, series=1)),
}
TOP = "rcell"


class Elem:
    def __init__(self, name, kind, ref, nodes, par):
        self.name, self.kind, self.ref, self.nodes, self.par = name, kind, ref, nodes, par


class Sub:
    def __init__(self, name):
        self.name, self.ports, self.elems = name, [], []


def gnd(node):
    return "vss" if node == "0" else node


def load():
    """Returns {block name: Sub}, the top block being TOP."""
    top, raw, subckts = inventory.read(inventory.CIRCUIT / "cell.spice")
    _, _, more = inventory.read(inventory.CIRCUIT / "blocks.spice")
    subckts.update(more)
    env = {}
    for k, v in raw.items():
        env[k] = inventory.number(v, env)
    out = {}

    def make(name, ports, lines, scope):
        """Build the block `name` from the lines of a sub-circuit, with the parameters of scope."""
        if name in out:
            return out[name]
        sub = Sub(name)
        inside, outside = set(), set()
        for line in lines:
            tok = line.split()
            el, kind = tok[0], tok[0][0].lower()
            if kind == "x":
                pos = [t for t in tok[1:] if "=" not in t]
                given = dict(t.split("=") for t in tok[1:] if "=" in t)
                ref, nodes = pos[-1], [gnd(n) for n in pos[:-1]]
                if ref.startswith(MOS):
                    w, l = inventory.number(given["w"], scope), inventory.number(given["l"], scope)
                    sub.elems.append(Elem(el, "mos", ref[len(MOS):], nodes, dict(w=w, l=l)))
                else:
                    inner = dict(scope)
                    variant = []
                    child = subckts[ref]
                    for k, v in {**child["defaults"], **given}.items():
                        try:
                            inner[k] = inventory.number(v, scope)
                        except Exception:
                            inner[k] = 0.0
                        if k in ("wc", "lc"):
                            variant.append(f"{k}{inner[k]:g}")
                    cname = ref + ("_" + "_".join(variant) if variant else "")
                    csub = make(cname, child["ports"], child["lines"], inner)
                    conn = dict(zip(child["ports"], nodes))
                    conn["vss"] = conn.get("vss", "vss")
                    cnodes = [conn[p] if p in conn else f"{el}_{p}" for p in csub.ports]
                    outside.update(f"{el}_{p}" for p in csub.ports if p not in conn)     # pins of the block stay pins
                    sub.elems.append(Elem(el, "block", cname, cnodes, {}))
                inside.update(sub.elems[-1].nodes)
            elif inventory.ROLE.get(el) == "cell":
                kind2, model, par = PARTS[el]
                nodes = [gnd(tok[1]), gnd(tok[2])] + (["vss"] if kind2 == "res" else [])
                sub.elems.append(Elem(el, kind2, model, nodes, dict(par, value=inventory.number(tok[3], scope))))
                inside.update(nodes)
            else:
                assert el in inventory.ROLE, el
                outside.update(gnd(t) for t in tok[1:3])
                outside.update(gnd(m) for m in re.findall(r"\bv\(\s*(\w+)\s*\)", line))
        nets = {n for e in sub.elems for n in e.nodes}
        sub.ports = [gnd(p) for p in ports if gnd(p) in nets]
        for extra in ["vss"] + sorted((outside & nets) - {"vss"}):
            if extra in nets and extra not in sub.ports:
                sub.ports.append(extra)
        out[name] = sub
        return sub

    make(TOP, [], top, env)
    return out


def check_inventory(blocks):
    """The devices below the top block are those of role "cell" of ../inventory.py, no more, no fewer."""
    import csv
    inventory.main()
    with open(inventory.HERE / "inventory_devices.csv") as fh:
        want = {r["path"].replace(".", "/"): r for r in csv.DictReader(fh) if r["role"] == "cell"}
    have = {path: (kind, par) for path, kind, model, nets, par in flat(blocks, TOP)}
    assert set(want) == set(have), sorted(set(want) ^ set(have))[:10]
    for path, row in want.items():
        kind, par = have[path]
        assert kind == row["kind"], path
        if kind == "mos":
            assert abs(par["w"] - float(row["w_um"])) < 1e-9 and abs(par["l"] - float(row["l_um"])) < 1e-9, path
        else:
            assert abs(par["value"] / float(row["value"]) - 1) < 1e-6, path
    return len(have)


def finger_count(w):
    return max(1, -int(-w // FINGER_MAX))


def flat(blocks, name, prefix="", conn=None):
    """Primitive devices below a block: (path, kind, model, nets, parameters)."""
    sub = blocks[name]
    conn = conn or {p: p for p in sub.ports}
    rows = []
    for e in sub.elems:
        nets = [conn.get(n, prefix + n) for n in e.nodes]
        if e.kind == "block":
            rows += flat(blocks, e.ref, prefix + e.name + "/", dict(zip(blocks[e.ref].ports, nets)))
        else:
            rows.append((prefix + e.name, e.kind, e.ref, nets, e.par))
    return rows


def spice(blocks, name):
    """The netlist netgen compares the layout of a block with: one sub-circuit, primitives only."""
    sub = blocks[name]
    out = [f"* LVS netlist of {name}, written by schematic.py from cell.spice and blocks.spice",
           f".subckt {name} " + " ".join(sub.ports)]
    for path, kind, model, nets, par in flat(blocks, name):
        x = "X" + path.replace("/", "_")
        nets = [n.replace("/", "_") for n in nets]
        if kind == "mos":
            out.append(f"{x} {' '.join(nets)} {MOS}{model} L={par['l']:g} W={par['w']:g} nf=1 m=1")
        elif kind == "cap":
            out.append(f"{x} {nets[0]} {nets[1]} {MOS}{model} W={par['side']:g} L={par['side']:g} m={par['count']}")
            if par.get("dummies"):      # dummy plates of the array: drawn, not in cell.spice, both plates on one net
                out.append(f"{x}_dummy {nets[1]} {nets[1]} {MOS}{model} W={par['side']:g} L={par['side']:g} m={par['dummies']}")
        elif par["series"] == 1:
            out.append(f"{x} {' '.join(nets)} {MOS}{model} L={par['length']:g} m=1")
        else:
            n = par["series"]
            mid = [nets[0]] + [f"{x[1:]}_s{k}" for k in range(1, n)] + [nets[1]]
            for k in range(n):
                out.append(f"{x}_{k} {mid[k]} {mid[k + 1]} {nets[2]} {MOS}{model} L={par['length'] / n:g} m=1")
    out.append(".ends")
    return "\n".join(out) + "\n"


if __name__ == "__main__":
    blocks = load()
    for name, sub in blocks.items():
        kinds = {}
        for e in sub.elems:
            kinds[e.kind] = kinds.get(e.kind, 0) + 1
        print(f"{name}: ports {' '.join(sub.ports)} | {kinds} | {len(flat(blocks, name))} devices below")
