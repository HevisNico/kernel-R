"""Source and drain areas of every transistor of the cell, for stage J of ../PREDICTION.md.

  python3 -I build_areas.py           (from research/sky130-layout/phase1)

For each size of transistor in the inventory, the device is drawn alone by the device generator
of the PDK, with one finger per 10 um of width at most (the finger choice of
../footprints/footprints.tcl), and extracted by Magic. The ad, as, pd, ps that Magic writes are
summed over the fingers and given to every transistor of that size.

Writes areas.csv: path, model, w, l, fingers, ad, as, pd, ps (um2 and um).
These are the areas of devices drawn alone, not of a layout of the cell.
"""
import csv
import os
import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
PDK_ROOT = os.environ.get("PDK_ROOT", "/usr/local/share/pdk")
MAGICRC = f"{PDK_ROOT}/sky130A/libs.tech/magic/sky130A.magicrc"


def fingers(w):
    return 1 if w <= 10 else (2 if w <= 20 else 4)


def main():
    import inventory                                   # ../inventory.py: the flat list of devices
    inventory.main()
    rows = [r for r in csv.DictReader(open(HERE.parent / "inventory_devices.csv")) if r["kind"] == "mos"]
    sizes = sorted({(r["model"], float(r["w_um"]), float(r["l_um"])) for r in rows})
    build = HERE / "build" / "areas"
    build.mkdir(parents=True, exist_ok=True)
    tcl = []
    for k, (model, w, l) in enumerate(sizes):
        nf = fingers(w)
        tcl += [f"load a{k} -force", "box 0 0 0 0",
                f"magic::gencell sky130::sky130_fd_pr__{model} d1 w {w / nf:g} l {l:g} nf {nf}",
                "select top cell", "extract all", "ext2spice lvs", f"ext2spice -o a{k}.spice"]
    tcl.append("quit -noprompt")
    (build / "areas.tcl").write_text("\n".join(tcl) + "\n")
    subprocess.run(["magic", "-dnull", "-noconsole", "-rcfile", MAGICRC, "areas.tcl"], cwd=build,
                   capture_output=True, text=True, check=True)
    table = {}
    for k, (model, w, l) in enumerate(sizes):
        nf = fingers(w)
        tot = dict(ad=0.0, pd=0.0, ps=0.0, w=0.0)
        tot["as"] = 0.0
        n = 0
        for line in (build / f"a{k}.spice").read_text().splitlines():
            if line.startswith("X") and f"sky130_fd_pr__{model} " in line + " ":
                p = dict(re.findall(r"(\w+)=([-+0-9.e]+)", line))
                if "ad" not in p:
                    continue
                mult = float(p.get("m", 1)) * float(p.get("nf", 1))
                assert abs(float(p["l"]) - l) < 1e-9, line
                for key in ("ad", "as", "pd", "ps", "w"):
                    tot[key] += float(p[key]) * (mult if key != "w" else float(p.get("m", 1)))
                n += 1
        assert n >= 1 and abs(tot["w"] - w) < 1e-6, f"{model} {w} {l}: extracted width {tot['w']} in {n} devices"
        table[(model, w, l)] = (nf, n, tot)
    with open(HERE / "areas.csv", "w", newline="") as fh:
        wr = csv.writer(fh, lineterminator="\n")
        wr.writerow(["path", "model", "w", "l", "fingers", "ad", "as", "pd", "ps"])
        for r in rows:
            key = (r["model"], float(r["w_um"]), float(r["l_um"]))
            nf, n, t = table[key]
            wr.writerow([r["path"], r["model"], r["w_um"], r["l_um"], nf] + [f"{t[k]:.6g}" for k in ("ad", "as", "pd", "ps")])
    print("size,fingers,devices extracted,ad,as,pd,ps")
    for (model, w, l), (nf, n, t) in sorted(table.items()):
        print(f"{model} {w:g}/{l:g},{nf},{n},{t['ad']:.4g},{t['as']:.4g},{t['pd']:.4g},{t['ps']:.4g}")


if __name__ == "__main__":
    main()
