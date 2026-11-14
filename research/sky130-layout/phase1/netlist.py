"""The netlist of phase 1: the deck of a campaign runner, flattened, with areas and wire capacitances.

  netlist.py IN.spice OUT.spice [--areas AREAS.csv | --zero] [--caps CAPS.csv]

IN is a deck as `../../circuit/run.py` (or a certification runner) writes it: the lines of
`cell.spice`, with `.include blocks.spice`, between the model library and the control section.
`blocks.spice` is read from the current directory, as ngspice reads it.

OUT holds the same devices in the same order, with the same widths and lengths:

  - the sub-circuits of `cell.spice` and `blocks.spice` (rport, opamp, comp, inv, nand2, nand3,
    srlatch) are expanded in place, depth first. A device `xm1` of `xop` of `x1` becomes
    `x1.xop.xm1`, and a node `sum` of `x1` becomes `x1.sum`: the names ngspice gives them, so the
    saved signals of the runners are unchanged;
  - with --areas, each transistor gets the `ad`, `as`, `pd`, `ps` of its row in AREAS.csv
    (columns path, ad, as, pd, ps; areas in um2, perimeters in um);
  - with --zero, each transistor gets `ad=0 as=0 pd=0 ps=0`, and CAPS.csv is read with every value
    replaced by zero: the identity test;
  - with --caps, one capacitor per row of CAPS.csv (columns node1, node2, farad) is added after the
    last device.

Nothing else is changed: parameters, options, sources, the control section.
The script fails on a line it does not know how to expand.
"""
import csv
import re
import sys

MOS = "sky130_fd_pr__"
NODES = {"x": None, "c": 2, "r": 2, "v": 2, "i": 2, "b": 2, "g": 4, "s": 4}


def read_subckts(lines):
    """Split lines into those outside sub-circuit definitions and the definitions."""
    outside, subckts, current = [], {}, None
    for line in lines:
        low = line.strip().lower()
        if low.startswith(".subckt"):
            tok = line.split()
            current = dict(ports=[t for t in tok[2:] if "=" not in t],
                           defaults=dict(t.split("=", 1) for t in tok[2:] if "=" in t), body=[])
            subckts[tok[1]] = current
        elif low.startswith(".ends"):
            current = None
        elif current is not None:
            if low and not low.startswith("*"):
                assert not low.startswith("+") and not low.startswith("."), line
                current["body"].append(line.strip())
        else:
            outside.append(line)
    assert current is None
    return outside, subckts


def unbrace(value):
    return value[1:-1] if value.startswith("{") and value.endswith("}") else value


def substitute(text, params):
    """Replace the local parameters inside every {expression} of text by their values."""
    if not params:
        return text

    def inside(match):
        expr = match.group(1)
        for name, value in params.items():
            expr = re.sub(rf"\b{re.escape(name)}\b", f"({value})", expr)
        return "{" + expr + "}"
    return re.sub(r"\{([^{}]*)\}", inside, text)


def flatten(outside, subckts, glob):
    """Expand every instance of a known sub-circuit. Returns the lines and the flat transistors."""
    out, devices = [], []

    def node(name, prefix, ports):
        if name in ports:
            return ports[name]
        if name == "0" or name in glob:
            return name
        return prefix + name

    def expand(line, prefix, ports, params):
        tok = line.split()
        name, kind = tok[0], tok[0][0].lower()
        if kind not in NODES:
            raise ValueError(f"unknown element: {line}")
        if kind == "x":
            pos = [t for t in tok[1:] if "=" not in t]
            given = [t.split("=", 1) for t in tok[1:] if "=" in t]
            ref, nodes = pos[-1], [node(n, prefix, ports) for n in pos[:-1]]
            given = [(k, substitute(v, params)) for k, v in given]
            if ref in subckts:
                sub = subckts[ref]
                assert len(nodes) == len(sub["ports"]), line
                local = {k: unbrace(v) for k, v in sub["defaults"].items()}
                local.update({k: unbrace(v) for k, v in given})
                assert set(k for k, _ in given) <= set(sub["defaults"]), line
                inner_prefix = prefix + name + "."
                for body in sub["body"]:
                    expand(body, inner_prefix, dict(zip(sub["ports"], nodes)), local)
            else:
                if not ref.startswith(MOS):
                    raise ValueError(f"unknown sub-circuit: {line}")
                flat = prefix + name
                devices.append((flat, len(out)))
                out.append(" ".join([flat] + nodes + [ref] + [f"{k}={v}" for k, v in given]))
            return
        n = NODES[kind]
        nodes = [node(x, prefix, ports) for x in tok[1:1 + n]]
        rest = line.split(None, 1 + n)[1 + n] if len(tok) > 1 + n else ""
        if kind == "b":               # node names inside the expression of a behavioural source
            rest = re.sub(r"\bv\(\s*([^()]*?)\s*\)",
                          lambda m: "v(" + ",".join(node(x.strip(), prefix, ports) for x in m.group(1).split(",")) + ")",
                          rest)
        rest = substitute(rest, params)
        flat = f"{kind}.{prefix}{name}" if prefix else name
        out.append(" ".join([flat] + nodes + [rest]).rstrip())

    control = False
    for line in outside:
        low = line.strip().lower()
        if low.startswith(".control"):
            control = True
        if control or not low or low[0] in "*.":
            out.append(line)
            continue
        tok = line.split()
        if tok[0][0].lower() == "x":
            pos = [t for t in tok[1:] if "=" not in t]
            if pos[-1] in subckts:
                expand(line.strip(), "", {}, {})
                continue
            if pos[-1].startswith(MOS):
                devices.append((tok[0], len(out)))
        out.append(line)
    return out, devices


def build(text, blocks_text, areas=None, zero=False, caps=None):
    lines = text.splitlines()
    assert not any(l.startswith("+") for l in lines), "continuation lines are not handled"
    inc = [i for i, l in enumerate(lines) if l.strip().lower() == ".include blocks.spice"]
    assert len(inc) == 1, "expected one .include blocks.spice"
    block_lines = blocks_text.splitlines()
    assert not any(l.startswith("+") for l in block_lines)
    _, block_subckts = read_subckts(block_lines)
    outside, subckts = read_subckts(lines[:inc[0]] + lines[inc[0] + 1:])
    assert not set(subckts) & set(block_subckts)
    subckts.update(block_subckts)
    glob = set()
    for l in outside:
        if l.strip().lower().startswith(".global"):
            glob.update(l.split()[1:])
    out, devices = flatten(outside, subckts, glob)

    if zero:
        areas = {name: ("0", "0", "0", "0") for name, _ in devices}
    if areas is not None:
        missing = [name for name, _ in devices if name not in areas]
        extra = set(areas) - {name for name, _ in devices}
        assert not missing and not extra, f"areas: missing {missing[:5]}, unknown {sorted(extra)[:5]}"
        for name, index in devices:
            ad, as_, pd, ps = areas[name]
            out[index] += f" ad={ad} as={as_} pd={pd} ps={ps}"

    if caps:
        known = set()
        for l in out:
            low = l.strip().lower()
            if low.startswith(".control"):
                break
            if low and low[0] not in "*.":
                tok = l.split()
                kind = tok[0][0].lower()
                n = NODES[kind] if NODES[kind] else len([t for t in tok[1:] if "=" not in t]) - 1
                known.update(tok[1:1 + n])
        added = []
        for k, (n1, n2, value) in enumerate(caps):
            assert n1 in known and n2 in known, f"capacitor on an unknown node: {n1} {n2}"
            added.append(f"cpar{k} {n1} {n2} {'0' if zero else value}")
        stop = next(i for i, l in enumerate(out) if l.strip().lower().startswith(".control"))
        last = max(i for i, l in enumerate(out[:stop]) if l.strip() and l.strip()[0] not in "*.")
        out[last + 1:last + 1] = ["* extracted wire capacitances"] + added
    return "\n".join(out) + "\n", [name for name, _ in devices]


def read_areas(path):
    with open(path) as fh:
        return {r["path"]: (r["ad"], r["as"], r["pd"], r["ps"]) for r in csv.DictReader(fh)}


def read_caps(path):
    with open(path) as fh:
        return [(r["node1"], r["node2"], r["farad"]) for r in csv.DictReader(fh)]


def main(argv):
    args = argv[1:]
    src, dst = args[0], args[1]
    zero = "--zero" in args
    areas = read_areas(args[args.index("--areas") + 1]) if "--areas" in args else None
    caps = read_caps(args[args.index("--caps") + 1]) if "--caps" in args else None
    text, devices = build(open(src).read(), open("blocks.spice").read(), areas=areas, zero=zero, caps=caps)
    with open(dst, "w") as fh:
        fh.write(text)
    return devices


if __name__ == "__main__":
    main(sys.argv)
