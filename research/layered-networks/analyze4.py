"""analyze3.py plus the stage-N seal-log check of addition C (2026-11-24). Development only.

  analyze4.py OUTDIR ROOT [ROOT ...] [times=github|bare]

analyze3.py's analysis, then, for every instance still counted at a level, every one of its stage-N folders of that
level (N0 for K0; N1..N3 for K3) must hold SEAL_LOG.json naming the commit that logged its seal (analyze3's
`seal.log.commit`). Otherwise the instance is not counted at that level and is listed under `seal_defects` with
`stage_n_seal_log`. The groups and the family are then recomputed as analyze3 computes them.
"""
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import analyze as A  # noqa: E402
import analyze3 as A3  # noqa: E402

FORMAT = "layered-campaign-results/4"


def main(outdir, *args):
    A3.main(outdir, *args)
    out = Path(outdir)
    res = json.loads((out / "RESULTS.json").read_text())
    roots = [Path(a) for a in map(str, args) if "=" not in a]
    for r in res["instances"]:
        root = roots[int(r["machine"].split("_")[1]) - 1]
        commit = ((r.get("seal") or {}).get("log") or {}).get("commit")
        for level, ns in (("K0", [0]), ("K3", [1, 2, 3])):
            if not (r.get(level) or {}).get("counted"):
                continue
            bad = []
            for n in ns:
                f = root / r["instance"] / f"N{n}" / "SEAL_LOG.json"
                got = json.loads(f.read_text()).get("commit") if f.exists() else None
                if got is None or got != commit:
                    bad.append(f"N{n}: SEAL_LOG.json {'missing' if got is None else got[:12]} vs log {str(commit)[:12]}")
            if bad:
                r[level] = dict(counted=False, not_sealed=True)
                res["seal_defects"].append(dict(machine=r["machine"], instance=r["instance"], stage_n_seal_log=bad))
    for g, out_g in res["groups"].items():
        rs = [r for r in res["instances"] if r["group"] == g]
        for level in ("K0", "K3"):
            counted = [r for r in rs if (r.get(level) or {}).get("counted")]
            ref = sorted(r["instance"] for r in counted if r[level]["refuted"])
            out_g[level].update(counted=len(counted), refuted_instances=ref, verdict=A.word(len(counted), bool(ref), level),
                                not_sealed=sorted(r["instance"] for r in rs if (r.get(level) or {}).get("not_sealed")))
    for level in ("K0", "K3"):
        vs = [res["groups"][g][level]["verdict"] for g in res["groups"]]
        res["family"][level] = "refuted" if "refuted" in vs else "established" if vs and all(v == "established" for v in vs) else "worded per group"
    res.update(format=FORMAT, analyze4_sha256=A.sha(__file__))
    (out / "RESULTS.json").write_bytes(A.canon(res))
    (out / "SHA256SUMS").write_text(f"{A.sha(out / 'RESULTS.json')}  RESULTS.json\n")
    print(json.dumps(dict(results_sha256=A.sha(out / "RESULTS.json"), seal_defects=len(res["seal_defects"])), indent=1))
    return True


if __name__ == "__main__":
    sys.exit(0 if main(*sys.argv[1:]) else 1)
