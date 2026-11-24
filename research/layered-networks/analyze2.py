"""analyze.py with the environment's provenance (coordinator, 2026-11-24). Development only.

  analyze2.py OUTROOT [OUTDIR]        OUTDIR/RESULTS.json and SHA256SUMS (default OUTROOT/analysis2)

analyze.py is pushed and kept as it is; its analysis is reused unchanged and an `env` section is added:
- OUTROOT/ENV.json (envcheck_layered.py env, written by campaign_run3.py): its sha256, its static_sha256, the
  resumes' uptimes (ENV_RESUMES.json);
- every instance's status.json `env_sha256` and its sealed prediction's `env_sha256` (stage_d5.py).
**Mixed environments are refused**: if any instance's status or prediction names another ENV.json, or a resume had
another static_sha256, the analysis stops with the list and writes nothing. An OUTROOT without ENV.json is refused too.
Deterministic, as analyze.py.
"""
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import analyze as A  # noqa: E402

FORMAT = "layered-campaign-results/2"


def env_section(root):
    root = Path(root)
    f = root / "ENV.json"
    if not f.exists():
        raise SystemExit(f"refused: {root} has no ENV.json")
    env = json.loads(f.read_text())
    sha = A.sha(f)
    bad = []
    resumes = json.loads((root / "ENV_RESUMES.json").read_text()) if (root / "ENV_RESUMES.json").exists() else []
    bad += [f"resume at {r['uptime_s']}: static {r['static_sha256'][:12]}" for r in resumes if r["static_sha256"] != env["static_sha256"]]
    per = {}
    for st in sorted(root.glob("*/status.json")):
        name = st.parent.name
        s = json.loads(st.read_text()).get("env_sha256")
        pf = st.parent / "D" / "prediction.json"
        p = json.loads(pf.read_text()).get("env_sha256") if pf.exists() else "no prediction"
        per[name] = dict(status=s, prediction=p)
        if s != sha:
            bad.append(f"{name}: status env {s}")
        if pf.exists() and p != sha:
            bad.append(f"{name}: prediction env {p}")
    if bad:
        raise SystemExit("refused: mixed environments in one OUTROOT: " + "; ".join(bad))
    return dict(env_json_sha256=sha, static_sha256=env["static_sha256"], static=env["static"],
                uptime_s=env["uptime_s"], resumes=[r["uptime_s"] for r in resumes], instances=per)


def main(root, outdir=None):
    root = Path(root)
    outdir = Path(outdir) if outdir else root / "analysis2"
    env = env_section(root)
    res = A.analyze(root)
    res.update(format=FORMAT, analyze2_sha256=A.sha(__file__), env=env)
    outdir.mkdir(parents=True, exist_ok=True)
    (outdir / "RESULTS.json").write_bytes(A.canon(res))
    (outdir / "SHA256SUMS").write_text(f"{A.sha(outdir / 'RESULTS.json')}  RESULTS.json\n")
    print(json.dumps(dict(env=env["static_sha256"][:16], groups={g: (v["K0"]["verdict"], v["K3"]["verdict"])
                                                               for g, v in res["groups"].items()}), indent=1))
    return True


if __name__ == "__main__":
    sys.exit(0 if main(*sys.argv[1:]) else 1)
