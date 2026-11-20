"""Development only, arithmetic for a design note: where the crossings of campaign 6's development batch would fall at
twice the dose, if each moved with the dose as the nominal cell's did. No simulation and no new data: it reads
c7/C7_SHARE.json (c7_share.py's output, from the batch's own evidence). An estimate, not a measure.

  c7_rescale.py C7_SHARE.json OUT.json

For each crossing of the 7 predicted instances (the pairs of a and b, the two lines of c):
  s1     = need - above, its place at the unchanged dose, in stages
  s2     = s1 / R, with R = 2.0065, the dose ratio measured on the nominal cell (DOSE_REPORT.md, section 3)
  need2  = ceil(s2);  below2 = s2 - (need2 - 1);  above2 = need2 - s2
  tr2    = the instance's own K = 3 budget of that crossing in stages, divided by R
  in its window at twice the dose, under the one-port rule:  below2 > tr2 and above2 >= tr2
An instance has room for c when both lines are in their windows, and for all three cells when the four crossings are.
"""
import json
import math
from pathlib import Path
import sys

R = 2.0065

if __name__ == "__main__":
    d = json.loads(Path(sys.argv[1]).read_text())
    rows, n_in, n_all = [], 0, 0
    for r in d["instances"]:
        if "frozen" not in r:
            continue
        bs, out = r["budgets_stages"], {}
        for k in ("a", "b", "c1", "c2"):
            s1 = r["needs"][k] - r["margins_stages"][k]["above"]
            tr1 = bs["a"] if k == "a" else bs["b"] if k == "b" else bs["c_training"]
            s2, tr2 = s1 / R, tr1 / R
            need2 = math.ceil(s2)
            below2, above2 = s2 - (need2 - 1), need2 - s2
            ok1 = r["margins_stages"][k]["below"] > tr1 and r["margins_stages"][k]["above"] >= tr1
            ok2 = below2 > tr2 and above2 >= tr2
            out[k] = dict(s1=s1, in_its_window_1x=ok1, s2=s2, need2=need2, below2=below2, above2=above2, budget2=tr2, in_its_window_2x=ok2)
            n_in += ok2
            n_all += 1
        rows.append(dict(seed=r["seed"], crossings=out, needs_2x=[out[k]["need2"] for k in ("a", "b", "c1", "c2")],
                         c_room_1x=out["c1"]["in_its_window_1x"] and out["c2"]["in_its_window_1x"], all_three_1x=all(v["in_its_window_1x"] for v in out.values()),
                         c_room_2x=out["c1"]["in_its_window_2x"] and out["c2"]["in_its_window_2x"], all_three_2x=all(v["in_its_window_2x"] for v in out.values())))
        # the 1x windows must be the rooms c7_share.py found with the frozen functions
        assert out["a"]["in_its_window_1x"] == r["frozen"]["room_at_K3"]["a"] and out["b"]["in_its_window_1x"] == r["frozen"]["room_at_K3"]["b"], r["seed"]
        assert rows[-1]["c_room_1x"] == r["one_port"]["room_at_K3"]["c"], r["seed"]
    res = dict(what="an estimate by rescaling, not a measure", dose_ratio=R, instances_in_the_batch=len(d["instances"]), predicted_instances=len(rows),
               crossings=n_all, crossings_in_their_window_2x=n_in,
               c_room_2x=[x["seed"] for x in rows if x["c_room_2x"]], all_three_2x=[x["seed"] for x in rows if x["all_three_2x"]],
               c_room_1x=[x["seed"] for x in rows if x["c_room_1x"]], all_three_1x=[x["seed"] for x in rows if x["all_three_1x"]], rows=rows)
    Path(sys.argv[2]).write_text(json.dumps(res, indent=1) + "\n")
    print(json.dumps({k: v for k, v in res.items() if k != "rows"}))
    for x in rows:
        print(x["seed"], x["needs_2x"], ["in" if x["crossings"][k]["in_its_window_2x"] else "out" for k in ("a", "b", "c1", "c2")])
