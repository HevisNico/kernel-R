"""The per-machine disk peak of the campaign (defect D3 of the final dry run, 2026-11-26). Development only.

  disk_peak.py OUT.json [m=12]

The assignment is plan_split3's (plan_split2's split) for the campaign sizes NOT1 60, ANDOR3 32, XOR3 37. The
assignment depends only on the group sizes and the draw order, so placeholder seeds are used.

The sizes are measured. Final dry run, 2026-11-26:
- the raws: XOR3 N0 1.849 GB and noisy 2.702 GB; ANDOR3 N0 1.009 GB; NOT1 N0 0.019 GB;
- the extracts: XOR3 70 / 100 MB; ANDOR3 N0 43 MB; NOT1 3.0 / 4.9 MB (N0 / noisy);
- the instance folder without extract and raws: XOR3 19 MB, ANDOR3 2 MB, NOT1 9 MB;
- the kernel library: 6 MB.

The G2 run (evidence/prefreeze-g2, ANDOR3 6104) gives the noisy ANDOR3 raw: 1.387 GB. The noisy ANDOR3 extract is
taken as 43 MB × 1.387 / 1.009 = 59 MB, and the noisy NOT1 raw as 0.035 GB.

Per machine:
- **Kept at the end:**
  - every instance's folder;
  - its extracts: N0, plus 3 noisy rounds, with probability p_room (expected) or on every instance (worst);
  - the N0 raws of its keep_raw instances;
  - the N0 raws of the remote duplicates it runs;
  - the kernel library.
- **Transient:** at most `jobs` = 4 raws being written or awaiting their comparison at once (one core each). At the
  worst, these are the 4 largest raws the machine can hold at once: its groups' noisy raws, or N0 raws when it has no
  room.
- **The peak** = kept + transient. "Worst" assumes room on every instance, with the 4 largest raws at once.
  "Expected" weights the noisy rounds by p_room and takes the transient as the largest single raw times
  min(4, the number of concurrent jobs the machine can have).

The rule checked: peak ≤ 30 − 20 = 10 GB. A machine launched with 30 GB free must keep the 20 GB guard.
"""
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import plan_split as PS  # noqa: E402
import plan_split3 as PS3  # noqa: E402

GB = 1e9
RAW = dict(XOR3=dict(N0=1.849, noisy=2.702), ANDOR3=dict(N0=1.009, noisy=1.387), NOT1=dict(N0=0.019, noisy=0.035))
EXT = dict(XOR3=dict(N0=0.070, noisy=0.100), ANDOR3=dict(N0=0.043, noisy=0.059), NOT1=dict(N0=0.003, noisy=0.0049))
FOLDER = dict(XOR3=0.019, ANDOR3=0.002, NOT1=0.009)
KERNEL = 0.006
SIZES = dict(NOT1=60, ANDOR3=32, XOR3=37)
LAUNCH, GUARD, JOBS = 30.0, 20.0, 4


def peak(plan):
    tag = {"NOT1": "NOT1", "ANDOR3": "ANDOR3", "XOR3": "XOR3"}
    keep = set(plan["keep_raw"])
    inst = [(g, s) for g, v in plan["groups"].items() for s in v["seeds"]]
    kept_w = kept_e = KERNEL
    for g, s in inst:
        p = PS.COST[g]["p_room"]
        kept_w += FOLDER[g] + EXT[g]["N0"] + 3 * EXT[g]["noisy"]
        kept_e += FOLDER[g] + EXT[g]["N0"] + p * 3 * EXT[g]["noisy"]
        if f"{tag[g]}_{s}" in keep:
            kept_w += RAW[g]["N0"]
            kept_e += RAW[g]["N0"]
    for x in plan["remote_duplicates"]:
        kept_w += RAW[x["group"]]["N0"]
        kept_e += RAW[x["group"]]["N0"]
    raws = sorted([RAW[g]["noisy"] for g, _ in inst for _ in range(3)] + [RAW[g]["N0"] for g, _ in inst]
                  + [RAW[x["group"]]["N0"] for x in plan["remote_duplicates"]], reverse=True)
    trans_w = sum(raws[:JOBS])
    big = max(raws, default=0.0)
    trans_e = big * min(JOBS, len(raws))
    return dict(instances={g: sum(1 for h, _ in inst if h == g) for g in SIZES if any(h == g for h, _ in inst)},
                keep_raw=sorted(keep), remote_duplicates=[x["home_instance"] for x in plan["remote_duplicates"]],
                kept_worst_gb=round(kept_w, 2), transient_worst_gb=round(trans_w, 2), peak_worst_gb=round(kept_w + trans_w, 2),
                kept_expected_gb=round(kept_e, 2), peak_expected_gb=round(kept_e + trans_e, 2),
                within_10_gb_worst=kept_w + trans_w <= LAUNCH - GUARD)


def main(out, *rest):
    res = {}
    for m in [int(dict(a.split("=") for a in rest).get("m", 12))] + ([8] if not rest else []):
        draw = dict(format="layered-draw/1", groups={g: [100000 * (i + 1) + k for k in range(n)]
                                                     for i, (g, n) in enumerate([("NOT1", 60), ("ANDOR3", 32), ("XOR3", 37)])})
        plans, _ = PS3.split(draw, json.loads((HERE / "TEMPLATE_CAMPAIGN_3.json").read_text()), m)
        per = {f"K{k + 1:02d}": peak(p) for k, p in enumerate(plans)}
        res[f"m={m}"] = dict(machines=per, max_peak_worst_gb=max(v["peak_worst_gb"] for v in per.values()),
                             max_peak_expected_gb=max(v["peak_expected_gb"] for v in per.values()),
                             all_within_10_gb_worst=all(v["within_10_gb_worst"] for v in per.values()))
    res.update(format="layered-disk-peak/1", launch_gb=LAUNCH, guard_gb=GUARD, jobs=JOBS,
               raw_gb=RAW, extract_gb=EXT, folder_gb=FOLDER, kernel_gb=KERNEL)
    Path(out).write_text(json.dumps(res, indent=1, sort_keys=True) + "\n")
    print(json.dumps({k: {x: v[x] for x in ("max_peak_worst_gb", "max_peak_expected_gb", "all_within_10_gb_worst")}
                      for k, v in res.items() if k.startswith("m=")}))
    return True


if __name__ == "__main__":
    sys.exit(0 if main(*sys.argv[1:]) else 1)
