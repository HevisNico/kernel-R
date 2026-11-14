"""Diagnostic of C1 on layout 2.2: the rest charge before the first read. Exploratory, not a campaign.

  python3 -I rest.py table      what the committed results already say (no simulation)
  python3 -I rest.py runs       the exploratory simulations (about 35 minutes on four cores)
  python3 -I rest.py report     the tables of REST_DIAGNOSTIC.md, printed

C1 fails on three ports because the rest charge before the first read of the noisy test run is
below 0.1. The rest charge is q = 0.1 + (1.25 V - vq) / 0.5 V, read 1 ps before the pulse
(cert_run.py). Each exploratory run is a noisy test run of the campaign (cert_run.py, unchanged,
mode "train", the noise identifier of the stage: 700000 + the seed) made through the harness of
stage P with something taken out:

  areas       no capacitance at all: the source and drain areas alone
  no_vq       the primary list without every capacitance on vq
  no_cmp      the primary list without the capacitances from vq to a node inside the FIRE comparator
  no_vq_rails the primary list without the capacitances from vq to node 0, vdd, vr0 and vpre
  no_vq_dq    the primary list without the capacitances from vq to the node dq of each port
  no_vq_adm   the primary list without the other capacitances on vq (adm, vmem2, sum, ibm)
  schematic   the deck of the schematic: no areas, no capacitance, the same noise
  only_nzm    the primary list; the three other noise sources divided by a million
  no_nzm      the primary list; the noise of the FIRE reference divided by a million
              (for these two the noise file of the mirror is changed, and the hash of it in the
              manifest of the mirror with it: cert_run.py is unchanged and checks that hash. The
              sources keep their random draws; only their size changes.)

and one run without noise, the read of the nominal cell with the areas alone. Only the first row
of each run is read. Nothing here was preregistered and nothing here decides a prediction.
"""
import csv
import json
import shutil
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

HERE = Path(__file__).resolve().parent
P1 = HERE.parent.parent / "phase1"
CIRCUIT = HERE.parent.parent.parent / "circuit"
sys.path.insert(0, str(P1))
import p_plan
import p_run

BUILD = HERE / "build"
CAPS = HERE.parent / "phase1" / "p_caps_primary.csv"
STAGE = HERE.parent / "phase1" / "results_c"
CELLS = p_plan.LARGE + p_plan.SMALL
REFUSED = [6051, 6082, 6031]
FOUR = REFUSED + [6065]
MOVED = [6082, 6074, 6031, 6051]            # the cells whose first read the capacitances move most
NANO = 1e9                      # the tables are in 1e-9 of a level unit: 0.5 nV on vq


def caps_list():
    with open(CAPS, newline="") as fh:
        return [(r["node1"], r["node2"], float(r["farad"])) for r in csv.DictReader(fh)]


CAP_VARIANTS = {
    "base": lambda a, b: False,
    "areas": lambda a, b: True,
    "no_vq": lambda a, b: "vq" in (a, b),
    "no_cmp": lambda a, b: "vq" in (a, b) and any(n.startswith("xcmpm.") for n in (a, b)),
    "no_vq_rails": lambda a, b: "vq" in (a, b) and any(n in ("0", "vdd", "vr0", "vpre") for n in (a, b)),
    "no_vq_dq": lambda a, b: "vq" in (a, b) and any(n.endswith(".dq") for n in (a, b)),
    "no_vq_adm": lambda a, b: "vq" in (a, b) and not any(n in ("0", "vdd", "vr0", "vpre") or n.endswith(".dq") or n.startswith("xcmpm.") for n in (a, b)),
}
#          name        capacitances  harness mode  noise sources kept        cells
VARIANTS = [("areas", "areas", "stage", "all", CELLS),
            ("schematic", "base", "schematic", "all", CELLS),
            ("no_vq", "no_vq", "stage", "all", FOUR),
            ("no_cmp", "no_cmp", "stage", "all", FOUR),
            ("no_vq_rails", "no_vq_rails", "stage", "all", MOVED),
            ("no_vq_dq", "no_vq_dq", "stage", "all", MOVED),
            ("no_vq_adm", "no_vq_adm", "stage", "all", MOVED),
            ("only_nzm", "base", "stage", "nzm", FOUR),
            ("no_nzm", "base", "stage", "others", FOUR)]


def write_caps(key):
    BUILD.mkdir(exist_ok=True)
    path = BUILD / f"caps_{key}.csv"
    rows = [(a, b, v) for a, b, v in caps_list() if not CAP_VARIANTS[key](a, b)]
    with open(path, "w", newline="") as fh:
        w = csv.writer(fh, lineterminator="\n")
        w.writerow(["node1", "node2", "farad"])
        w.writerows((a, b, f"{v:.6g}") for a, b, v in rows)
    return path, sum(v for _, _, v in caps_list()) - sum(v for _, _, v in rows)


def mirror(noise):
    """One mirror of research/circuit for each set of noise sources: the noise file is read there."""
    root = BUILD / f"mirror_{noise}"
    runs = [p_plan.cert(f"t{s}_train", "test", "train", s, noise=True) for s in CELLS] + [p_plan.cert("nom_read", "preflight", "read")]
    if not (root / "certification" / "manifest.json").exists():
        p_run.mirror(root, runs)
        if noise != "all":
            z = json.loads((CIRCUIT / "noise.json").read_text())
            small = ("vnmw", "vnmf") if noise == "others" else ("vncw", "vncf", "vnow", "vnof", "inmw")
            for k in small:
                z["params"][k] *= 1e-6
            (root / "noise.json").write_text(json.dumps(z, indent=1) + "\n")
            for folder in ("certification", "certification-unconditional"):
                m = root / folder / "manifest.json"
                if m.exists():
                    doc = json.loads(m.read_text())
                    if "noise.json" in doc.get("source_sha256", {}):
                        doc["source_sha256"]["noise.json"] = p_run.digest(root / "noise.json")
                        m.write_text(json.dumps(doc, indent=1) + "\n")
    return root, {r["name"]: r for r in runs}


def one(job):
    variant, caps, mode, noise, name = job
    out = BUILD / "results" / variant
    if (out / f"{name}.csv").exists() or (out / f"{name}.failed").exists():
        return f"{variant} {name} already there"
    root, runs = mirror(noise)
    # runs of one mirror share its folders: each variant gets its own copy of the mirror's tree by name
    work = BUILD / f"work_{variant}"
    with p_run.LOCK:
        if not work.exists():
            shutil.copytree(root, work, symlinks=True)
    return variant + " " + p_run.run_in(work, runs[name], name, mode, write_caps(caps)[0], out)


def runs():
    for noise in ("all", "nzm", "others"):
        mirror(noise)
    jobs = [("noiseless", "areas", "stage", "all", "nom_read")]
    for variant, caps, mode, noise, cells in VARIANTS:
        jobs += [(variant, caps, mode, noise, f"t{s}_train") for s in cells]
    with ThreadPoolExecutor(4) as ex:
        for line in ex.map(one, jobs):
            print(line, flush=True)


def first(path):
    """Rest charge before the first read of a run, minus 0.1, and the port of that read."""
    if not Path(path).exists():
        return None
    with open(path, newline="") as fh:
        r = next(csv.DictReader(fh))
    return float(r["c_pre"]) - 0.1


def later(path):
    with open(path, newline="") as fh:
        rows = list(csv.DictReader(fh))
    c = [float(r["c_pre"]) - 0.1 for r in rows[1:] if r["port"] in ("1", "2")]
    k = next(i for i, r in enumerate(rows) if r["port"] == "2")
    return min(c), max(c), float(rows[k]["c_pre"]) - 0.1, k


def table():
    f = lambda x: "   none" if x is None else f"{x * NANO:+8.1f}"
    print("Rest charge before the first read, minus 0.1, in 1e-9 level unit (0.5 nV on vq). Negative: refused.")
    print("cell   | noisy test run: layout 2.2, first layout, schematic | without noise: layout 2.2, first layout, schematic")
    sch, unc = CIRCUIT / "certification" / "results", CIRCUIT / "certification-unconditional" / "results"
    for s in CELLS:
        print(f"t{s} | {f(first(STAGE / f't{s}_train.csv'))} {f(first(P1 / 'results_p' / f't{s}_train.csv'))} {f(first(sch / 'test' / f't{s}_train.csv'))}"
              f" | {f(first(STAGE / f'u{s}_train.csv'))} {f(first(P1 / 'results_p' / f'u{s}_train.csv'))} {f(first(unc / 'gain' / f'u{s}_train.csv'))}")
    for s in p_plan.CALIBRATION["A"] + p_plan.CALIBRATION["B"]:
        print(f"c{s} |                            | {f(first(STAGE / f'c{s}_train.csv'))} {f(first(P1 / 'results_p' / f'c{s}_train.csv'))} "
              f"{f(first(sch / 'calibration' / f'c{s}_train.csv'))}")
    print("every later read of the noisy test runs of layout 2.2 (min, max), and the first read of port 2 (its row):")
    for s in CELLS:
        lo, hi, p2, k = later(STAGE / f"t{s}_train.csv")
        print(f"t{s} | {lo * NANO:+9.1f} {hi * NANO:+9.1f} | {p2 * NANO:+9.1f} (row {k})")
    below = total = 0
    for p in sorted((sch / "test").glob("t*_train.csv")):
        total += 1
        below += first(p) < 0
    print(f"schematic campaign: {below} of {total} noisy test runs have the first rest charge below 0.1")


def report():
    f = lambda x: "    none" if x is None else f"{x * NANO:+8.1f}"
    table()
    print()
    print("capacitance taken out of the list (fF):", {k: round(write_caps(k)[1] * 1e15, 2) for k in CAP_VARIANTS})
    print("without noise, nominal cell, areas alone:", f(first(BUILD / "results" / "noiseless" / "nom_read.csv")))
    names = [v[0] for v in VARIANTS]
    print("cell   | stage C | " + " | ".join(f"{n:>9s}" for n in names))
    for s in CELLS:
        print(f"t{s} | {f(first(STAGE / f't{s}_train.csv'))} | " + " | ".join(f"{f(first(BUILD / 'results' / n / f't{s}_train.csv')):>9s}" for n in names))


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else ""
    if cmd == "table":
        table()
    elif cmd == "runs":
        runs()
    elif cmd == "report":
        report()
    else:
        sys.exit(__doc__)
