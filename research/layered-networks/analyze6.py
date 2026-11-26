"""analyze5.py plus the in-record seal-log check of the controls' sealed stage N (controls3.py). Development only.

  analyze6.py OUTDIR ROOT [ROOT ...] [times=...] [thresholds=thresholds.json]

analyze5's analysis, then, for every instance still counted at a level, every stage-N record of that level
(N0/noisy_record.json for K0; N1..N3 for K3) must carry `seal_log` = {commit, branch} equal to the commit that logged
the instance's seal (analyze3's seal.log.commit) and to the machine's seal branch (PLAN seal_push.branch).
Otherwise the instance is not counted at that level (seal_defects: `record_seal_log`).
The U records' seal_log is reported. Groups and family recomputed with analyze5's per-group thresholds.
"""
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import analyze as A  # noqa: E402
import analyze5 as A5  # noqa: E402

FORMAT = "layered-campaign-results/6"


def main(outdir, *args):
    args = [str(a) for a in args]
    A5.main(outdir, *args)
    out = Path(outdir)
    res = json.loads((out / "RESULTS.json").read_text())
    roots = [Path(a) for a in args if "=" not in a]
    for r in res["instances"]:
        root = roots[int(r["machine"].split("_")[1]) - 1]
        plan = json.loads((root / "PLAN.json").read_text())
        branch = (plan.get("seal_push") or {}).get("branch")
        commit = ((r.get("seal") or {}).get("log") or {}).get("commit")
        for level, ns in (("K0", [0]), ("K3", [1, 2, 3])):
            if not (r.get(level) or {}).get("counted"):
                continue
            bad = []
            for n in ns:
                f = root / r["instance"] / f"N{n}" / "noisy_record.json"
                sl = json.loads(f.read_text()).get("seal_log") if f.exists() else None
                if not sl or sl.get("commit") != commit or sl.get("branch") != branch:
                    bad.append(f"N{n}: record seal_log {sl} vs log {str(commit)[:12]} on {branch}")
            if bad:
                r[level] = dict(counted=False, not_sealed=True)
                res["seal_defects"].append(dict(machine=r["machine"], instance=r["instance"], record_seal_log=bad))
    th = res["thresholds"]
    for g, v in res["groups"].items():
        rs = [r for r in res["instances"] if r["group"] == g]
        for level in ("K0", "K3"):
            counted = [r for r in rs if (r.get(level) or {}).get("counted")]
            ref = sorted(r["instance"] for r in counted if r[level]["refuted"])
            t = th[level][g]
            v[level].update(counted=len(counted), refuted_instances=ref, verdict=A5.word(len(counted), bool(ref), t),
                            not_sealed=sorted(r["instance"] for r in rs if (r.get(level) or {}).get("not_sealed")))
    for level in ("K0", "K3"):
        vs = [res["groups"][g][level]["verdict"] for g in res["groups"]]
        res["family"][level] = "refuted" if "refuted" in vs else "established" if vs and all(x == "established" for x in vs) else "worded per group"
    useal = []
    for k, root in enumerate(roots, start=1):
        for f in sorted(root.glob("U_*/U/untrained_record.json")):
            useal.append(dict(machine=f"machine_{k}", instance=f.parent.parent.name[2:], seal_log=json.loads(f.read_text()).get("seal_log")))
    res["controls"]["U_seal_log"] = useal
    res.update(format=FORMAT, analyze6_sha256=A.sha(__file__))
    (out / "RESULTS.json").write_bytes(A.canon(res))
    (out / "SHA256SUMS").write_text(f"{A.sha(out / 'RESULTS.json')}  RESULTS.json\n")
    print(json.dumps(dict(results_sha256=A.sha(out / "RESULTS.json"), groups={g: (v["K0"]["verdict"], v["K3"]["verdict"])
                                                                              for g, v in res["groups"].items()},
                          seal_defects=len(res["seal_defects"])), indent=1))
    return True


if __name__ == "__main__":
    sys.exit(0 if main(*sys.argv[1:]) else 1)
