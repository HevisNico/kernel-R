"""plan_split2.py with each remote duplicate's home named (defect D2 of the final dry run, the owner's decision,
2026-11-26). Development only. plan_split2.py is kept as it is.

  plan_split3.py DRAW.json TEMPLATE.json OUTDIR [m=12]

plan_split2's split, unchanged. Each `remote_duplicates` entry also gets:
- `home_machine`: K<nn>, the machine that holds the instance;
- `home_branch`: that machine's seal-log branch, its seal_push.branch (evidence/combined-seals-K<nn>);
- `home_instance`: <TAG>_<seed>.

campaign_run15 refuses a duplicate without home_branch. It waits for the home's SEALS.txt line on that branch, so no
plan is edited by hand.
"""
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import plan_split as PS  # noqa: E402
import plan_split2 as PS2  # noqa: E402
import spec as specmod  # noqa: E402


def split(draw, template, m=12):
    plans, summary = PS2.split(draw, template, m)
    tag = {g: specmod.load(HERE / PS.SPECS[g])["tag"] for g in PS.SPECS}
    for p in plans:
        for x in p["remote_duplicates"]:
            k = next(i for i, q in enumerate(plans) if x["seed"] in q["groups"].get(x["group"], {}).get("seeds", []))
            x.update(home_machine=f"K{k + 1:02d}", home_branch=plans[k]["seal_push"]["branch"],
                     home_instance=f"{tag[x['group']]}_{x['seed']}")
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
    print(json.dumps(dict(machines=m, duplicates={f"K{k + 1:02d}": [(x["home_instance"], x["home_branch"]) for x in p["remote_duplicates"]]
                                                  for k, p in enumerate(plans) if p["remote_duplicates"]})))
    return True


if __name__ == "__main__":
    sys.exit(0 if main(*sys.argv[1:]) else 1)
