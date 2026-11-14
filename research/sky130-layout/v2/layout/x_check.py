"""The verdicts X1 to X5 of ../PREDICTION.md, from the extraction of the second layout.

  python3 -I x_check.py        (by run_x.sh)      writes ../X_REPORT.md

Committed before the extraction is made. Reads build/p_caps_primary.csv (the primary list),
../swings.csv (the loud nets: swing above 0.5 V in the schematic), build/floor.txt (the device
floor), build/results.json, build/cell_flat.txt and build/klayout.txt (X5).
"""
import csv
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
BUILD = HERE / "build"
FIRST = HERE.parent.parent / "phase1" / "p_caps_primary.csv"
F = 1e-15
HOLDS, FAILS = "holds", "fails"


def caps_of(path):
    out = {}
    with open(path, newline="") as fh:
        for r in csv.DictReader(fh):
            out[frozenset((r["node1"], r["node2"]))] = out.get(frozenset((r["node1"], r["node2"])), 0.0) + float(r["farad"])
    return out


def on(node, caps):
    return {next(iter(k - {node})): v for k, v in caps.items() if node in k and len(k) == 2}


def main():
    caps, first = caps_of(BUILD / "p_caps_primary.csv"), caps_of(FIRST)
    nodes = {n for k in caps for n in k}
    with open(HERE.parent / "swings.csv", newline="") as fh:
        loud = sorted(r["net"] for r in csv.DictReader(fh) if float(r["swing_V"]) > 0.5 and r["net"] in nodes)
    floor = {}
    for line in (BUILD / "floor.txt").read_text().splitlines():
        tok = line.split()
        m = re.fullmatch(r"([-+0-9.e]+)([a-z]?)", tok[3].lower())
        floor[frozenset(t.split(".")[-1] for t in tok[1:3])] = float(m.group(1)) * {"f": 1e-15, "a": 1e-18, "p": 1e-12, "": 1.0}[m.group(2)]
    gd, gs = floor[frozenset("GD")], floor[frozenset("GS")]
    V, lines = [], []

    def verdict(key, text, ok, measured, before):
        V.append((key, text, HOLDS if ok else FAILS, measured, before))

    # X1: vq and the loud nets. The admission switch of each port is drawn with vq on its drain exit.
    def x1(c):
        vq = on("vq", c)
        return {n: max(0.0, vq.get(n, 0.0) - (gd if n in ("x1.adm", "x2.adm") else 0.0)) for n in loud}
    a, b = x1(caps), x1(first)
    worst = max(a, key=a.get)
    verdict("X1", "Between `vq` and each loud net at most 0.03 fF, and at most 0.10 fF in all; device floor subtracted for `adm`",
            max(a.values()) <= 0.03 * F and sum(a.values()) <= 0.10 * F,
            f"largest {a[worst] / F:.4f} fF (`{worst}`); in all {sum(a.values()) / F:.4f} fF over {len(loud)} loud nets",
            f"largest {max(b.values()) / F:.3f} fF (`{max(b, key=b.get)}`); in all {sum(b.values()) / F:.3f} fF")
    lines += ["### X1: the largest capacitances between `vq` and a loud net", "", "| Loud net | Second layout | First layout |", "|---|---|---|"]
    lines += [f"| `{n}` | {a[n] / F:.4f} fF | {b.get(n, 0) / F:.4f} fF |" for n in sorted(a, key=a.get, reverse=True)[:8]]

    # X2: each summing node, its sensor node and the loud nets. The steering switch has the summing node on its source exit.
    def x2(c):
        out = {}
        for q in ("x1", "x2"):
            s = on(f"{q}.sum", c)
            out[q] = (s.get(f"{q}.vs", 0.0), {n: max(0.0, s.get(n, 0.0) - (gs if n == f"{q}.si" else 0.0)) for n in loud if n != f"{q}.vs"})
        return out
    a, b = x2(caps), x2(first)
    ok = all(a[q][0] <= 0.10 * F and max(a[q][1].values()) <= 0.03 * F for q in a)
    verdict("X2", "Between a summing node and `vs` of its port at most 0.10 fF; and each other loud net at most 0.03 fF; device floor subtracted for `si`", ok,
            "; ".join(f"port {q[1]}: `vs` {a[q][0] / F:.4f} fF, largest other {max(a[q][1].values()) / F:.4f} fF (`{max(a[q][1], key=a[q][1].get)}`)" for q in a),
            "; ".join(f"port {q[1]}: `vs` {b[q][0] / F:.3f} fF, largest other {max(b[q][1].values()) / F:.3f} fF (`{max(b[q][1], key=b[q][1].get)}`)" for q in b))
    lines += ["", "### X2: the largest capacitances between a summing node and a loud net", "", "| Port | Loud net | Second layout | First layout |", "|---|---|---|---|"]
    for q in a:
        for n in sorted(a[q][1], key=a[q][1].get, reverse=True)[:4]:
            lines.append(f"| {q[1]} | `{n}` | {a[q][1][n] / F:.4f} fF | {b[q][1].get(n, 0) / F:.4f} fF |")

    # X3
    tot, tot1 = sum(on("vq", caps).values()), sum(on("vq", first).values())
    verdict("X3", "The capacitances with one end on `vq`, summed: at most 45 fF", tot <= 45 * F, f"{tot / F:.2f} fF", f"{tot1 / F:.2f} fF")
    vq = on("vq", caps)
    lines += ["", "### X3: where the capacitance of `vq` goes", "", "| To | Second layout | First layout |", "|---|---|---|"]
    lines += [f"| `{n}` | {vq[n] / F:.2f} fF | {on('vq', first).get(n, 0) / F:.2f} fF |" for n in sorted(vq, key=vq.get, reverse=True)[:8]]

    # X4
    def x4(c):
        vq_ = on("vq", c)
        names = {n[3:] for n in vq_ if n.startswith(("x1.", "x2."))}
        return {n: abs(vq_.get("x1." + n, 0.0) - vq_.get("x2." + n, 0.0)) for n in names}
    a, b = x4(caps), x4(first)
    worst = max(a, key=a.get) if a else None
    verdict("X4", "For every net of a port, its capacitance to `vq` in port 1 and in port 2 differ by at most 0.1 fF",
            not a or a[worst] <= 0.1 * F, f"largest difference {a[worst] / F:.4f} fF (`{worst}`), over {len(a)} nets" if a else "no capacitance",
            f"largest difference {max(b.values()) / F:.2f} fF (`{max(b, key=b.get)}`)")

    # X5
    results = json.loads((BUILD / "results.json").read_text())
    flat = (BUILD / "cell_flat.txt").read_text()
    count = int(re.search(r"FLAT_DRC_COUNT (\d+)", flat).group(1))
    box = [int(v) for v in re.search(r"CELL_BBOX (-?\d+) (-?\d+) (-?\d+) (-?\d+)", flat).groups()]
    area = (box[2] - box[0]) * (box[3] - box[1]) * 25e-12            # units of 5 nm -> mm2
    kl = (BUILD / "klayout.txt").read_text()
    capm = sum(int(l.split()[-1]) for l in kl.splitlines() if l.startswith("KLAYOUT capm.10") or l.startswith("KLAYOUT capm.2b"))
    clean = all(r["clean"] for r in results) and len(results) == 9
    verdict("X5", "Magic DRC 0 and LVS match on each block and on the cell; no wire under a capacitor; at most 0.085 mm²",
            clean and count == 0 and capm == 0 and area <= 0.085,
            f"{sum(r['clean'] for r in results)} of {len(results)} blocks clean; flattened cell: {count} DRC errors; "
            f"`capm.10` and `capm.2b`: {capm} reports; {(box[2] - box[0]) / 200:.1f} µm × {(box[3] - box[1]) / 200:.1f} µm = {area:.4f} mm²",
            "9 of 9; 0; 0; 0.0742 mm²")

    out = ["# Second layout: X1 to X5", "",
           "Written by `layout/x_check.py` under [`PREDICTION.md`](PREDICTION.md). **An extraction, not a simulation.** "
           "The capacitances are those Magic extracts by rules, primary list.", "",
           f"**{sum(v[2] == HOLDS for v in V)} hold, {sum(v[2] == FAILS for v in V)} fail, of {len(V)}.**", "",
           "| | Prediction | Second layout | First layout | Verdict |", "|---|---|---|---|---|"]
    out += [f"| {k} | {t} | {m} | {bf} | {s} |" for k, t, s, m, bf in V]
    out += ["", f"Device floor, the switch of 1 µm by 0.15 µm drawn alone: gate to drain exit {gd / F:.4f} fF, gate to source exit {gs / F:.4f} fF.", ""]
    out += lines
    kl_other = [l for l in kl.splitlines() if l.startswith("KLAYOUT ") and not l.startswith("KLAYOUT_")]
    rules = {}
    for l in kl_other:
        rules[l.split()[1]] = rules.get(l.split()[1], 0) + int(l.split()[-1])
    out += ["", "## Not part of X5", "", "KLayout deck, reports by rule: " + (", ".join(f"`{r}` {n}" for r, n in sorted(rules.items())) or "none") + ".",
            "Antenna check of Magic: " + ((BUILD / "antenna.txt").read_text().strip().replace("\n", "; ") or "no violation") + "."]
    (HERE.parent / "X_REPORT.md").write_text("\n".join(out) + "\n")
    for k, t, s, m, bf in V:
        print(k, s, "|", m)


if __name__ == "__main__":
    main()
