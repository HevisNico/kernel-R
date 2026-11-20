"""Development only: step B of the dose experiment, the 2x measures on the nominal cell, through dosedev2.many.
Wave 1: the guard-off deck, the four scans, the both-lines check. Then the one-sided bounds from the two pair scans
(dosedev2.bound, S_MAX 4 and 8). Wave 2: the four one-sided sets. No noise, no seed.   step_b.py REPO RUNS_DIR"""
from fractions import Fraction as F
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import dosedev2

REPO, RUNS = Path(sys.argv[1]).resolve(), Path(sys.argv[2]).resolve()
PY, NG, PDK = "/home/user/owner-prep/venv312/bin/python", "/usr/bin/ngspice", "/home/user/campaign/pdk"
WINDOW = ["vhi=0.7"]
D = json.loads((HERE / "runs" / "none-2x-cal-on" / "DOSES.json").read_text())["D_V"]       # the doses of the 2x smoke
LIMIT = dict(caloff=1300, pair=990, line=940, bothfire=80, onesided=440)                  # twice the batch's means


def scan(rid, cell, kind, args, limit):
    return dict(id=rid, limit_s=limit, argv=[PY, "-B", str(HERE / "dosedev2.py"), "scan", str(REPO), str(RUNS / rid), cell, kind, *args, *D[cell], NG, PDK, "--", *WINDOW])


wave1 = [dict(id="none-2x-cal-off", limit_s=LIMIT["caloff"], argv=[PY, "-B", str(HERE / "dosedev2.py"), "caloff", str(REPO), str(RUNS / "none-2x-cal-off"), NG, PDK, *WINDOW]),
         scan("none-2x-scan-a-pair", "a", "pair", ["1/2"], LIMIT["pair"]), scan("none-2x-scan-b-pair", "b", "pair", ["1/2"], LIMIT["pair"]),
         scan("none-2x-scan-c-line1", "c", "line1", ["1/2"], LIMIT["line"]), scan("none-2x-scan-c-line2", "c", "line2", ["1/2"], LIMIT["line"]),
         scan("none-2x-bothfire-c", "c", "bothfire", [], LIMIT["bothfire"])]
RUNS.mkdir(parents=True, exist_ok=True)
(RUNS / "JOBS_B1.json").write_text(json.dumps(dict(folder=str(RUNS / "B1"), waves=[wave1]), indent=1) + "\n")
for j in wave1:                                              # the runs' folders are under RUNS, the scheduler's state under RUNS/B1
    pass
dosedev2.many(RUNS / "JOBS_B1.json")

S, h, why = {}, {}, None
for x in ("a", "b"):
    rec = RUNS / f"none-2x-scan-{x}-pair" / "record.json"
    if not rec.exists():
        why = f"the pair scan of {x} did not complete"
        break
    r = json.loads(rec.read_text())["result"]
    if not r.get("consistent"):
        why = f"the pair scan of {x} has no consistent bracket"
        break
    S[x], h[x] = F(r["s_star"]), F(r["half_bracket"])
if why:
    (RUNS / "BOUNDS.json").write_text(json.dumps(dict(not_started=why), indent=1) + "\n")
    raise SystemExit("one-sided sets not started: " + why)
bounds = {str(s_max): {x: str(v) for x, v in dosedev2.bound(F(s_max), S, h).items()} for s_max in (4, 8)}
(RUNS / "BOUNDS.json").write_text(json.dumps(dict(s_star={x: str(v) for x, v in S.items()}, half_bracket={x: str(v) for x, v in h.items()}, bounds=bounds), indent=1) + "\n")
wave2 = [scan(f"none-2x-onesided-{x}-s{s_max}", x, "onesided", [bounds[str(s_max)][x]] * 2, LIMIT["onesided"]) for s_max in (4, 8) for x in ("a", "b")]
(RUNS / "JOBS_B2.json").write_text(json.dumps(dict(folder=str(RUNS / "B2"), waves=[wave2]), indent=1) + "\n")
dosedev2.many(RUNS / "JOBS_B2.json")
