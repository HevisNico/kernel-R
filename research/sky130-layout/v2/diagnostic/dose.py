"""Diagnostic of the dose of the second layout: exploratory, not a campaign. Nominal cell, 27 C.

  python3 -I dose.py groups      capacitances taken out node by node
  python3 -I dose.py singles     capacitances taken out pair by pair, on the nodes that matter
  python3 -I dose.py report      the tables of DOSE_DIAGNOSTIC.md

Each run is the read of the certification campaign (cert_run.py, unchanged, mode "read": three
periods, one pulse on each port of a fresh cell) on the netlist of the second layout, primary
list, with some capacitances taken out of the list. The dose is the step of the silent pulse of
each port. S2 holds on the second layout, so the first silent step is the step of every silent
pulse. Nothing here was preregistered and nothing here decides a prediction.
"""
import csv
import json
import shutil
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

HERE = Path(__file__).resolve().parent
P1 = HERE.parent.parent / "phase1"
sys.path.insert(0, str(P1))
import p_run

BUILD = HERE / "build"
CAPS = HERE.parent / "phase1" / "p_caps_primary.csv"
PORTS = ("x1", "x2")


def caps_list(path=CAPS):
    with open(path, newline="") as fh:
        return [(r["node1"], r["node2"], float(r["farad"])) for r in csv.DictReader(fh)]


def local(node):
    """x1.vs -> ("x1", "vs"); a node of no port -> (None, node)."""
    for q in PORTS:
        if node.startswith(q + "."):
            return q, node[3:]
    return None, node


def touches(pair, names):
    """One end is a node of a port with one of these local names."""
    return any(local(n)[1] in names and local(n)[0] for n in pair)


GROUPS = {
    "base": ("the primary list of the second layout", lambda a, b: False),
    "areas_only": ("no capacitance: the source and drain areas alone", lambda a, b: True),
    "no_vs": ("without every capacitance on a sensor node `vs`", lambda a, b: touches((a, b), {"vs"})),
    "no_x": ("without every capacitance on a node `x`", lambda a, b: touches((a, b), {"x"})),
    "no_sum": ("without every capacitance on a summing node", lambda a, b: touches((a, b), {"sum"})),
    "no_vrefs": ("without every capacitance on `vrefs` or `vrefsn`", lambda a, b: touches((a, b), {"vrefs", "vrefsn"})),
    "no_vgd": ("without every capacitance on `vgd`", lambda a, b: touches((a, b), {"vgd"})),
    "no_vs_x_sum": ("without the three: `vs`, `x` and the summing node", lambda a, b: touches((a, b), {"vs", "x", "sum"})),
}


def pair_variant(node, other):
    """Without the capacitance between `node` and `other` of the same port (other may be 0, vdd, vmem...)."""
    def drop(a, b):
        for q in PORTS:
            first = f"{q}.{node}"
            second = {"vmem": f"vmem{q[1]}"}.get(other, other if other in ("0", "vdd", "vcm", "vpre", "vhi", "vlo") else f"{q}.{other}")
            if {a, b} == {first, second}:
                return True
        return False
    return drop


def run_variants(tag, variants):
    caps = caps_list()
    runs = [dict(name=f"v_{n}", tool="cert", stage="preflight", mode="read", section="tt", seed=None, noise=False) for n in variants]
    root = BUILD / tag
    shutil.rmtree(root, ignore_errors=True)
    p_run.mirror(root, runs)
    results = BUILD / f"{tag}_results"
    shutil.rmtree(results, ignore_errors=True)
    jobs = []
    for run, (name, (text, drop)) in zip(runs, variants.items()):
        path = BUILD / f"caps_{tag}_{name}.csv"
        kept = [(a, b, v) for a, b, v in caps if not drop(a, b)]
        with open(path, "w", newline="") as fh:
            w = csv.writer(fh, lineterminator="\n")
            w.writerow(["node1", "node2", "farad"])
            for a, b, v in kept:
                w.writerow([a, b, f"{v:.6g}"])
        jobs.append((run, path, len(caps) - len(kept), sum(v for a, b, v in caps if drop(a, b))))
    with ThreadPoolExecutor(4) as ex:
        for line in ex.map(lambda j: p_run.run_in(root, j[0], j[0]["name"], "stage", j[1], results), jobs):
            print(line, flush=True)
    out = {}
    for (run, path, n, total), (name, (text, _)) in zip(jobs, variants.items()):
        with open(results / f"{run['name']}.csv", newline="") as fh:
            rows = list(csv.DictReader(fh))
        out[name] = dict(text=text, removed=n, removed_fF=total * 1e15, step1=float(rows[0]["step1_mV"]), step2=float(rows[1]["step2_mV"]),
                         fired=[int(float(r["fired"])) for r in rows])
    (BUILD / f"{tag}.json").write_text(json.dumps(out, indent=1) + "\n")
    for name, r in out.items():
        print(f"DOSE {tag} {name}: {r['removed']} capacitances out ({r['removed_fF']:.2f} fF); step {r['step1']:.3f} and {r['step2']:.3f} mV")
    return out


def groups():
    return run_variants("groups", GROUPS)


def singles():
    """Pair by pair, on the nodes the groups point at: every capacitance of at least 0.05 fF on `vs` or `x` of port 1."""
    caps = caps_list()
    variants = {"base": GROUPS["base"]}
    for node in sys.argv[2:] or ["vs", "x"]:
        on = {}
        for a, b, v in caps:
            if f"x1.{node}" in (a, b):
                other = b if a == f"x1.{node}" else a
                on[other] = v
        for other, v in sorted(on.items(), key=lambda kv: -kv[1]):
            if v < 0.05e-15:
                continue
            name = local(other)[1] if local(other)[0] else {"vmem1": "vmem"}.get(other, other)
            variants[f"{node}__{name}"] = (f"without `{node}`–`{name}` ({v * 1e15:.2f} fF in port 1)", pair_variant(node, name))
    return run_variants("singles", variants)


def report():
    for tag in ("groups", "singles"):
        path = BUILD / f"{tag}.json"
        if not path.exists():
            continue
        data = json.loads(path.read_text())
        base = data["base"]
        for name, r in data.items():
            print(f"REPORT {tag} | {name} | {r['text']} | {r['removed_fF']:.2f} fF | {r['step1']:.3f} | {r['step2']:.3f} | "
                  f"{(r['step1'] - base['step1']) * 1000:+.0f} uV | {(r['step1'] / base['step1'] - 1) * 100:+.2f}%")


if __name__ == "__main__":
    BUILD.mkdir(exist_ok=True)
    cmd = sys.argv[1] if len(sys.argv) > 1 else ""
    if cmd not in ("groups", "singles", "report"):
        sys.exit(__doc__)
    globals()[cmd]()
