"""fit.py's instance fit on a record loaded with records2.py (repeat rule v2). Development only.

  fit2.py SPEC OUT     writes OUT/fit_v2.json (fit.py's fit.json, where it exists, is left as it is)
"""
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import fit as fitmod  # noqa: E402
import records2  # noqa: E402
import spec as specmod  # noqa: E402


def main(spec_path, outdir):
    s = specmod.load(spec_path)
    rec = records2.load(outdir)
    r = fitmod.instance_fit(s, rec)
    r["repeat_rule_v2"] = rec["repeat_rule_v2"]
    (Path(outdir) / "fit_v2.json").write_text(json.dumps(fitmod.js(r), indent=1) + "\n")
    return r


if __name__ == "__main__":
    r = main(sys.argv[1], sys.argv[2])
    print("repeat rule v2 changed:", json.dumps(r["repeat_rule_v2"]))
    for c in r["cells"]:
        if not c["measured"]:
            print(c["cell"], c["gate"], "NOT MEASURED:", c["why_not_measured"])
            continue
        b = c["budgets"]
        print(c["cell"], c["gate"], "K0", c["verdicts"]["K0"]["ok"], "K3", c["verdicts"]["K3"]["ok"],
              "train/test K0", b["K0"]["trainError"], b["K0"]["testError"], "K3", b["K3"]["trainError"], b["K3"]["testError"])
    print("eligible K0", r["eligible_K0"], "room K3", r["room_K3"])
