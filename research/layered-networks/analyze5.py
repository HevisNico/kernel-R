"""analyze4.py with per-group thresholds from thresholds.json (the owner's decision, 2026-11-24). Development only.

  analyze5.py OUTDIR ROOT [ROOT ...] [times=github|lsremote:<LOG>|bare] [thresholds=thresholds.json]

analyze4's analysis, unchanged, then every group's verdict at each level is recomputed with that group's own
threshold (thresholds.json: K0 30 for NOT1 and 20 for ANDOR3 and XOR3; K3 5 for all). The family is recomputed
the same way. The file's sha256 is in RESULTS.json.
"""
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import analyze as A  # noqa: E402
import analyze4 as A4  # noqa: E402

FORMAT = "layered-campaign-results/5"


def word(k, refuted, threshold):
    if refuted:
        return "refuted"
    if k >= threshold:
        return "established"
    if k >= 2:
        return f"held on {k} instances, not established"
    return "held on one instance" if k == 1 else "not established"


def main(outdir, *args):
    args = [str(a) for a in args]
    tf = next((a.split("=", 1)[1] for a in args if a.startswith("thresholds=")), str(HERE / "thresholds.json"))
    rest = [a for a in args if not a.startswith("thresholds=")]
    A4.main(outdir, *rest)
    out = Path(outdir)
    res = json.loads((out / "RESULTS.json").read_text())
    th = json.loads(Path(tf).read_text())
    for g, v in res["groups"].items():
        for level in ("K0", "K3"):
            t = th[level][g]
            v[level].update(threshold=t, verdict=word(v[level]["counted"], bool(v[level]["refuted_instances"]), t))
    for level in ("K0", "K3"):
        vs = [res["groups"][g][level]["verdict"] for g in res["groups"]]
        res["family"][level] = "refuted" if "refuted" in vs else "established" if vs and all(x == "established" for x in vs) else "worded per group"
    res.update(format=FORMAT, analyze5_sha256=A.sha(__file__), thresholds=dict(file=Path(tf).name, sha256=A.sha(tf),
                                                                              K0=th["K0"], K3=th["K3"]))
    (out / "RESULTS.json").write_bytes(A.canon(res))
    (out / "SHA256SUMS").write_text(f"{A.sha(out / 'RESULTS.json')}  RESULTS.json\n")
    print(json.dumps(dict(results_sha256=A.sha(out / "RESULTS.json"), groups={g: (v["K0"]["verdict"], v["K3"]["verdict"])
                                                                              for g, v in res["groups"].items()}), indent=1))
    return True


if __name__ == "__main__":
    sys.exit(0 if main(*sys.argv[1:]) else 1)
