"""Device inventory of one R cell, read from the netlists of the circuit study.

  python3 -I inventory.py            (from research/sky130-layout)

Reads ../circuit/cell.spice and ../circuit/blocks.spice without changing them, flattens the
hierarchy of one cell (two ports and the shared FIRE path), and writes

  inventory_devices.csv    one row per transistor, capacitor, resistor and source
  inventory_summary.md     the tables quoted in INVENTORY.md

Nothing is simulated. Gate areas are drawn areas W x L, not layout measurements.
"""
import csv
import hashlib
import math
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
CIRCUIT = HERE.parent / "circuit"
MOS = "sky130_fd_pr__"

# Role of every element that is not a transistor. "cell": a physical part of the cell that a
# layout must contain. "ideal": an ideal source that a real chip must replace by a circuit or a
# pad. "bench": part of the test bench only (stimulus shaping, noise injection, imposed leak).
ROLE = {
    "cq": "cell", "rleak": "cell", "cs": "cell", "cf": "cell", "cc": "cell", "rz": "cell",
    "rda": "cell", "cda": "cell", "rdl": "cell", "cdl": "cell", "rdp": "cell", "cdp": "cell",
    "vdd": "ideal", "vr0": "ideal", "vfire": "ideal", "vreopen": "ideal", "vcm": "ideal",
    "vhi": "ideal", "vlo": "ideal", "vpre": "ideal", "vinit": "ideal",
    "ibm": "ideal", "ibs": "ideal", "ibo": "ideal", "idis": "ideal",
    "vksen": "ideal", "vkrst": "ideal", "vkpreb": "ideal", "bip": "ideal",
    "bsen": "ideal", "brst": "ideal", "bpreb": "ideal", "vrsti": "ideal", "bdrv": "ideal",
    "srst": "ideal",
    "rsen": "bench", "csen": "bench", "rrst": "bench", "crst": "bench", "rpreb": "bench",
    "cpreb": "bench", "rrsti": "bench", "crsti": "bench", "rlk": "bench",
    "bvcmn": "bench", "rvcmn": "bench", "cvcmn": "bench", "bvrs": "bench", "rvrs": "bench",
    "cvrs": "bench", "bvrm": "bench", "rvrm": "bench", "cvrm": "bench",
    "vnzc": "bench", "rnzc": "bench", "vnzo": "bench", "rnzo": "bench", "vnzi": "bench",
    "rnzi": "bench", "gnm": "bench", "vnzm": "bench", "rnzm": "bench",
}

SUFFIX = {"f": 1e-15, "p": 1e-12, "n": 1e-9, "u": 1e-6, "m": 1e-3, "k": 1e3, "meg": 1e6, "g": 1e9}


def number(text, env):
    """Value of a SPICE number or of a {expression} of parameters."""
    text = text.strip()
    if text.startswith("{"):
        return float(eval(text[1:-1], {"__builtins__": {}, "log": math.log}, env))
    m = re.fullmatch(r"([-+0-9.e]+?)(meg|[fpnumkg])?", text.lower())
    if not m:
        raise ValueError(text)
    return float(m.group(1)) * SUFFIX.get(m.group(2), 1.0)


def read(path):
    """Top-level lines, parameters and sub-circuits of a netlist."""
    top, params, subckts, current = [], {}, {}, None
    for raw in path.read_text().splitlines()[1:]:          # the first line of a deck is its title
        line = raw.strip()
        if not line or line.startswith("*"):
            continue
        low = line.lower()
        if low.startswith(".subckt"):
            tok = line.split()
            ports = [t for t in tok[2:] if "=" not in t]
            defaults = dict(t.split("=") for t in tok[2:] if "=" in t)
            current = subckts.setdefault(tok[1], dict(ports=ports, defaults=defaults, lines=[]))
        elif low.startswith(".ends"):
            current = None
        elif low.startswith(".param") and current is None:
            for k, v in re.findall(r"(\w+)=(\{[^}]*\}|\S+)", line[6:]):
                params[k] = v
        elif low.startswith("."):
            continue
        elif current is not None:
            current["lines"].append(line)
        else:
            top.append(line)
    return top, params, subckts


def main():
    top, raw_params, subckts = read(CIRCUIT / "cell.spice")
    _, _, block_subckts = read(CIRCUIT / "blocks.spice")
    subckts.update(block_subckts)
    env = {}
    for k, v in raw_params.items():                          # parameters are defined in order
        env[k] = number(v, env)

    rows = []

    def walk(lines, path, scope):
        for line in lines:
            tok = line.split()
            name, kind = tok[0], tok[0][0].lower()
            where = ".".join(path + [name])
            if kind == "x":
                pos = [t for t in tok[1:] if "=" not in t]
                given = dict(t.split("=") for t in tok[1:] if "=" in t)
                ref = pos[-1]
                if ref.startswith(MOS):
                    w, l = number(given["w"], scope), number(given["l"], scope)
                    d, g, s, b = pos[:4]
                    rows.append(dict(path=where, block=".".join(path) or "top", kind="mos",
                                     model=ref[len(MOS):], w_um=w, l_um=l, value="",
                                     nodes=f"d={d} g={g} s={s} b={b}", role="cell"))
                else:
                    sub = subckts[ref]
                    inner = dict(scope)
                    for k, v in {**sub["defaults"], **given}.items():
                        try:
                            inner[k] = number(v, scope)
                        except Exception:
                            inner[k] = 0.0                   # ta, tb, tj: pulse schedule, unused here
                    walk(sub["lines"], path + [name], inner)
            elif kind in "cr":
                value = number(tok[3], scope)
                rows.append(dict(path=where, block=".".join(path) or "top", kind="cap" if kind == "c" else "res",
                                 model="", w_um="", l_um="", value=value, nodes=f"{tok[1]} {tok[2]}",
                                 role=ROLE.get(name, "?")))
            else:
                rows.append(dict(path=where, block=".".join(path) or "top", kind="source:" + kind,
                                 model="", w_um="", l_um="", value="", nodes=f"{tok[1]} {tok[2]}",
                                 role=ROLE.get(name, "?")))

    walk(top, [], env)
    unknown = sorted({r["path"] for r in rows if r["role"] == "?"})
    assert not unknown, f"elements without a role: {unknown}"

    fields = ["path", "block", "kind", "model", "w_um", "l_um", "value", "nodes", "role"]
    with open(HERE / "inventory_devices.csv", "w", newline="") as fh:
        wr = csv.DictWriter(fh, fieldnames=fields, lineterminator="\n")
        wr.writeheader()
        for r in rows:
            wr.writerow({k: (f"{v:.6g}" if isinstance(v, float) else v) for k, v in r.items()})

    mos = [r for r in rows if r["kind"] == "mos"]
    caps = [r for r in rows if r["kind"] == "cap"]
    ress = [r for r in rows if r["kind"] == "res"]
    srcs = [r for r in rows if r["kind"].startswith("source")]

    out = ["# Inventory summary (written by `inventory.py`, do not edit)", ""]
    out += ["Sources: `../circuit/cell.spice` sha256 `%s`, `../circuit/blocks.spice` sha256 `%s`." % (
        hashlib.sha256((CIRCUIT / "cell.spice").read_bytes()).hexdigest(),
        hashlib.sha256((CIRCUIT / "blocks.spice").read_bytes()).hexdigest()), ""]

    out += ["## Transistors by size", "",
            "| Model | W (um) | L (um) | Count in one cell | Gate area each (um2) | Gate area total (um2) |",
            "|---|---|---|---|---|---|"]
    groups = {}
    for r in mos:
        groups.setdefault((r["model"], r["w_um"], r["l_um"]), []).append(r)
    total_area = 0.0
    for (model, w, l), rs in sorted(groups.items(), key=lambda kv: -kv[0][1] * kv[0][2] * len(kv[1])):
        total_area += w * l * len(rs)
        out.append(f"| `{model}` | {w:g} | {l:g} | {len(rs)} | {w * l:.3g} | {w * l * len(rs):.4g} |")
    out += [f"| **total** | | | **{len(mos)}** | | **{total_area:.4g}** |", ""]

    out += ["## Transistors by block", "",
            "| Block | Transistors | Gate area (um2) |", "|---|---|---|"]

    def block_of(r):
        p = r["path"].split(".")
        if p[0] in ("x1", "x2"):
            if len(p) == 2:
                return "port: " + {"xmin": "gain mirror", "xmout": "gain mirror", "xms1": "admission switches",
                                   "xms2": "admission switches", "xmpre": "sensor precharge",
                                   "xmbd": "discharge mirror", "xmdis": "discharge mirror",
                                   "xmsi": "steering switches", "xmsd": "steering switches",
                                   }.get(p[1], "window reference switches")
            return "port: " + {"xop": "integrator op-amp", "xcmps": "window comparator"}.get(p[1], "logic (sequencing, steering, admission)")
        if len(p) == 1:
            return "shared: FIRE reference switches"
        return "shared: " + ("FIRE comparator" if p[0] == "xcmpm" else "protection logic")
    blocks = {}
    for r in mos:
        blocks.setdefault(block_of(r), []).append(r)
    for b, rs in sorted(blocks.items()):
        n = len(rs)
        per = " (both ports)" if b.startswith("port") else ""
        out.append(f"| {b}{per} | {n} | {sum(x['w_um'] * x['l_um'] for x in rs):.4g} |")
    out.append("")

    out += ["## Capacitors and resistors", "",
            "| Element | Value | Count in one cell | Role |", "|---|---|---|---|"]
    seen = {}
    for r in caps + ress:
        key = (r["path"].split(".")[-1], r["value"], r["role"], r["kind"])
        seen[key] = seen.get(key, 0) + 1
    for (name, value, role, kind), n in sorted(seen.items(), key=lambda kv: (kv[0][2], kv[0][3], -kv[0][1])):
        unit = f"{value * 1e12:g} pF" if kind == "cap" else f"{value:g} ohm"
        out.append(f"| `{name}` | {unit} | {n} | {role} |")
    cell_cap = sum(r["value"] for r in caps if r["role"] == "cell")
    out += ["", f"Capacitance that belongs to the cell: **{cell_cap * 1e12:.4g} pF** "
            f"(feedback capacitors alone: {sum(r['value'] for r in caps if r['path'].endswith('.cf')) * 1e12:g} pF).", ""]

    out += ["## Sources", "", "| Element | Count in one cell | Role |", "|---|---|---|"]
    seen = {}
    for r in srcs:
        key = (r["path"].split(".")[-1], r["role"])
        seen[key] = seen.get(key, 0) + 1
    for (name, role), n in sorted(seen.items(), key=lambda kv: (kv[0][1], kv[0][0])):
        out.append(f"| `{name}` | {n} | {role} |")
    out.append("")
    (HERE / "inventory_summary.md").write_text("\n".join(out))
    print(len(mos), "transistors,", len(caps), "capacitors,", len(ress), "resistors,", len(srcs), "sources")
    print("gate area %.1f um2, cell capacitance %.2f pF" % (total_area, cell_cap * 1e12))


if __name__ == "__main__":
    main()
