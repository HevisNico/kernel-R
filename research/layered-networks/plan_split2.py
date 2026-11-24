"""plan_split.py with the entries of campaign_run5.py (owner's additions B and C, 2026-11-24). Development only.

  plan_split2.py DRAW.json TEMPLATE.json OUTDIR [m=12]

plan_split.py's split, unchanged, plus per machine:
- `keep_raw`: the instances of this machine that another machine duplicates (their N0 trace.raw is kept);
- `disk_guard_gb`: 20, unless the template sets it;
- `allow_dry_seal`: false, unless the template sets it (campaign: false).
"""
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import plan_split as PS  # noqa: E402
import spec as specmod  # noqa: E402


def split(draw, template, m=12):
    plans, summary = PS.split(draw, template, m)
    tag = {g: specmod.load(HERE / PS.SPECS[g])["tag"] for g in PS.SPECS}
    for p in plans:
        p.setdefault("disk_guard_gb", template.get("disk_guard_gb", 20))
        p.setdefault("allow_dry_seal", bool(template.get("allow_dry_seal", False)))
        p["keep_raw"] = []
    for p in plans:
        for x in p["remote_duplicates"]:
            home = next(q for q in plans if x["seed"] in q["groups"].get(x["group"], {}).get("seeds", []))
            home["keep_raw"].append(f"{tag[x['group']]}_{x['seed']}")
    for p in plans:
        p["keep_raw"].sort()
    return plans, summary


def main(draw_path, template_path, outdir, *rest):
    m = int(dict(a.split("=") for a in rest).get("m", 12))
    plans, summary = split(json.loads(Path(draw_path).read_text()), json.loads(Path(template_path).read_text()), m)
    import hashlib
    summary["draw_sha256"] = hashlib.sha256(Path(draw_path).read_bytes()).hexdigest()
    out = Path(outdir)
    out.mkdir(parents=True, exist_ok=True)
    for k, p in enumerate(plans, start=1):
        (out / f"PLAN_K{k:02d}.json").write_bytes(PS.canon(p))
    (out / "SPLIT.json").write_bytes(PS.canon(summary))
    print(json.dumps(dict(machines=m, keep_raw={f"K{k + 1:02d}": p["keep_raw"] for k, p in enumerate(plans) if p["keep_raw"]})))
    return True


if __name__ == "__main__":
    sys.exit(0 if main(*sys.argv[1:]) else 1)
