"""disk_peak.py under the owner's rule on D3 (2026-11-26): 40 GB free at launch, the 20 GB guard during the run, and
the comparisons C<n> exempt from it (campaign_run16). Development only. disk_peak.py is kept as it is.

  disk_peak2.py OUT.json

The assignment, the measured sizes and the peak model are disk_peak.py's, with TEMPLATE_CAMPAIGN_4.json, for m = 12
and m = 8. The margin checked is 40 − 20 = 20 GB. A machine whose peak stays within it never meets the guard. With
the comparisons exempt, a machine that does meet it can still delete its finished rounds' raws, so it does not stop.
"""
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import disk_peak as DP  # noqa: E402
import plan_split3 as PS3  # noqa: E402

LAUNCH = 40.0


def main(out):
    t = json.loads((HERE / "TEMPLATE_CAMPAIGN_4.json").read_text())
    assert t["disk_launch_gb"] == LAUNCH and t["disk_guard_gb"] == DP.GUARD
    res = dict(format="layered-disk-peak/2", launch_gb=LAUNCH, guard_gb=DP.GUARD, margin_gb=LAUNCH - DP.GUARD,
               comparisons_exempt=True, jobs=DP.JOBS, raw_gb=DP.RAW, extract_gb=DP.EXT)
    for m in (12, 8):
        draw = dict(format="layered-draw/1", groups={g: [100000 * (i + 1) + k for k in range(n)]
                                                     for i, (g, n) in enumerate([("NOT1", 60), ("ANDOR3", 32), ("XOR3", 37)])})
        plans, _ = PS3.split(draw, t, m)
        per = {}
        for k, p in enumerate(plans):
            v = DP.peak(p)
            v.pop("within_10_gb_worst")
            v.update(margin_left_worst_gb=round(LAUNCH - DP.GUARD - v["peak_worst_gb"], 2),
                     within_margin_worst=v["peak_worst_gb"] <= LAUNCH - DP.GUARD)
            per[f"K{k + 1:02d}"] = v
        res[f"m={m}"] = dict(machines=per, max_peak_worst_gb=max(v["peak_worst_gb"] for v in per.values()),
                             max_peak_expected_gb=max(v["peak_expected_gb"] for v in per.values()),
                             min_margin_left_worst_gb=min(v["margin_left_worst_gb"] for v in per.values()),
                             all_within_margin_worst=all(v["within_margin_worst"] for v in per.values()))
    Path(out).write_text(json.dumps(res, indent=1, sort_keys=True) + "\n")
    print(json.dumps({k: {x: v[x] for x in ("max_peak_worst_gb", "max_peak_expected_gb", "min_margin_left_worst_gb",
                                            "all_within_margin_worst")} for k, v in res.items() if k.startswith("m=")}))
    return True


if __name__ == "__main__":
    sys.exit(0 if main(*sys.argv[1:]) else 1)
