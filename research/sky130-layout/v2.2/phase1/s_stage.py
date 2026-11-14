"""The nominal stage of layout 2.2: S1 to S5 of ../PREDICTION.md, as declared in ../S_STAGE.md.

  python3 -I s_stage.py plan
  python3 -I s_stage.py launch --go      the eight runs, four at a time, on one machine
  python3 -I s_stage.py report           once, after the last run: writes ../S_REPORT.md

The runs are made by the runners of the campaigns, unchanged, through the harness of stage P
(../../phase1/p_run.py), with the capacitances of layout 2.2 (p_caps_primary.csv). The
launcher is that of ../../phase1/execute.py: attempt marker pushed before the first run, the name
of each run pushed as started before it begins, a started run never made again.

A copy of ../../v2.1/phase1/s_stage.py with two changes: the column of comparison (layout 2.1,
from its committed results) and the words of the report. The rules and the ranges are the same.
"""
import csv
import json
import os
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
P1 = HERE.parent.parent / "phase1"
sys.path.insert(0, str(P1))

import execute
import j_stage
import p_analyze
import p_execute
import p_plan
import p_run

RESULTS = HERE / "results_s"
BUILD = HERE / "build" / "s"
RUNS = [p_plan.circuit("nom_cell", "cell", "rel=1"), p_plan.cert("nom_ramp", "preflight", "ramp"),
        p_plan.cert("nom_read", "preflight", "read"), p_plan.cert("nom_leak", "preflight", "leak"),
        p_plan.circuit("nom_refresh", "refresh", "100", "rlk=1e11", "rel=1"), p_plan.circuit("nom_cell125", "cell", "temp=125", "rel=1"),
        p_plan.circuit("nom_refresh125", "refresh", "60", "temp=125", "rel=1"), p_plan.cert("nom_train", "preflight", "train")]
NAMES = [r["name"] for r in RUNS]
PINNED = ["PREDICTION.md", "S_STAGE.md", "phase1/s_stage.py", "phase1/p_caps_primary.csv", "phase1/p_areas.csv",
          "phase1/constants_stage_p.json"]
HOLDS, FAILS, NA = p_analyze.HOLDS, p_analyze.FAILS, p_analyze.NA
S5_RANGE = (1.350, 1.385)           # ../PREDICTION.md
S5_SECOND = (1.340, 1.365)          # the range of the second layout, given beside it
SECOND = HERE.parent.parent / "v2.1" / "phase1" / "results_s"         # the layout of comparison: 2.1


def run_one(name):
    if (RESULTS / f"{name}.csv").exists() or (RESULTS / f"{name}.failed").exists():
        return f"{name} already there"
    with p_run.LOCK:
        if not (BUILD / "certification" / "manifest.json").exists():
            p_run.mirror(BUILD, RUNS)
    try:
        return p_run.run_in(BUILD, next(r for r in RUNS if r["name"] == name), name, "stage", HERE / "p_caps_primary.csv", RESULTS)
    except Exception as e:                                    # a run that cannot be made is a failed run
        (RESULTS / f"{name}.failed").write_text(f"{type(e).__name__}: {e}\n")
        return f"{name} FAILED {type(e).__name__}"


def check_inputs():
    """The areas of the two layouts are the same file, which is the one the harness gives to the shim."""
    assert (HERE / "p_areas.csv").read_bytes() == (P1 / "p_areas.csv").read_bytes(), "the areas of layout 2.2 differ from those the harness uses"
    assert execute.digest(p_run.NGSPICE) == json.loads((P1 / "j_manifest.json").read_text())["ngspice_sha256"], "simulator changed"
    assert p_run.pdk_commit() == json.loads((P1 / "j_manifest.json").read_text())["pdk_commit"], "device models changed"


def launch(go):
    execute.STAGE, execute.SPLIT, execute.PINNED = "S", {"A": NAMES}, PINNED
    execute.launch("A", root=HERE.parent, run_one=run_one, preflight=p_execute.preflight, verify=check_inputs, go=go)


# ---- the verdicts

def verdicts(data, train_rows, constants, reference, names=NAMES):
    """data: the runs of run.py and the ramps and reads (p_analyze.Data). train_rows: the rows of the
    nominal train of cert_run.py, or None. constants: d0, kappa, mu. reference: schematic values."""
    V = []
    R = p_analyze.single_run_readings(data, [n for n in names if data.ok(n)])
    missing = [n for n in names if not data.ok(n)]

    def add(key, text, status, measured):
        V.append((key, text, status, measured))

    if train_rows is None:
        add("S1", "The rest charge before every pulse of the nominal train is between 0.1 and 0.1001", NA, "nom_train: no result")
    else:
        c = [float(r["c_pre"]) for r in train_rows]
        add("S1", "The rest charge before every pulse of the nominal train is between 0.1 and 0.1001",
            HOLDS if all(0.1 <= x <= 0.1001 for x in c) else FAILS, f"{len(c)} pulses, from {min(c):.6f} to {max(c):.6f}")

    rows = data.rows("nom_cell")
    if rows is None:
        add("S2", "No step of a port at rest or of a firing pulse above 0.005 mV; first silent step within 0.003 mV of the later ones", NA, "nom_cell: no result")
        add("S5", f"Every silent step of the nominal cell is between {S5_RANGE[0]:.3f} and {S5_RANGE[1]:.3f} mV", NA, "nom_cell: no result")
    else:
        rest = [abs(x["step"][q]) for x in rows for q in (1, 2) if x["port"] not in (q, 0)]
        firing = [abs(x["step"][q]) for x in rows for q in (1, 2) if x["fired"] and x["port"] in (q, 0)]
        first = []
        for q in (1, 2):
            s = [x["step"][q] for x in j_stage.series(rows, q) if not x["fired"]]
            first.append(max((abs(s[0] - v) for v in s[1:]), default=0.0) if s else None)
        ok = max(rest + firing) <= 0.005 and all(f is not None and f <= 0.003 for f in first)
        add("S2", "No step of a port at rest or of a firing pulse above 0.005 mV; first silent step within 0.003 mV of the later ones",
            HOLDS if ok else FAILS,
            f"largest step of a port at rest {max(rest):.3f} mV, of a firing pulse {max(firing):.3f} mV; first silent step against the later ones: "
            + " and ".join("no silent pulse" if f is None else f"{f:.3f} mV" for f in first))
        silent = R["silent_steps"]
        add("S5", f"Every silent step of the nominal cell is between {S5_RANGE[0]:.3f} and {S5_RANGE[1]:.3f} mV",
            HOLDS if silent and all(S5_RANGE[0] <= v <= S5_RANGE[1] for v in silent) else FAILS,
            f"{len(silent)} silent steps from {min(silent):.3f} to {max(silent):.3f} mV" if silent else "no silent pulse")

    shift = None
    if data.ok("nom_ramp") and data.ok("nom_read"):
        post = p_analyze.nominal_gap(p_analyze.floats(p_analyze.read_csv(data.path("nom_read"))), data.static_level("nom_ramp"), constants)
        if None not in post.values():
            shift = {q: post[q] - reference["nominal_gap"][q] for q in (1, 2)}
    if shift is None:
        add("S3", "The gap of the nominal cell moves by −0.002 to +0.010, the two ports within 0.0005 of each other", NA, "nominal ramp or read without a result")
    else:
        ok = all(-0.002 <= s <= 0.010 for s in shift.values()) and abs(shift[1] - shift[2]) <= 0.0005
        add("S3", "The gap of the nominal cell moves by −0.002 to +0.010, the two ports within 0.0005 of each other", HOLDS if ok else FAILS,
            f"{shift[1]:+.5f} (port 1) and {shift[2]:+.5f} (port 2); between the ports {abs(shift[1] - shift[2]):.5f}")

    L = []
    if rows is None:
        L += [("L1", NA, "nom_cell: no result"), ("L2", NA, "nom_cell: no result"), ("L3", NA, "nom_cell: no result")]
    else:
        L.append(("L1", HOLDS if R["stops"] else FAILS, f"first FIRE after {R['counts'][0]} and {R['counts'][1]} silent pulses; "
                  + ("no silent pulse after it" if R["stops"] else "a silent pulse after a first FIRE, or no FIRE")))
        L.append(("L2", HOLDS if R["counts"][0] == R["counts"][1] and R["counts"][0] in (3, 4, 5) else FAILS, f"{R['counts'][0]} and {R['counts'][1]}"))
        s = R["silent_steps"]
        L.append(("L3", HOLDS if s and all(1.33 <= v <= 1.42 for v in s) else FAILS, f"{min(s):.3f} to {max(s):.3f} mV" if s else "no silent pulse"))
    L.append(("L5", NA if missing else (FAILS if R["events"] else HOLDS), ("; ".join(R["events"]) if R["events"] else "nothing")
              + (f"; {len(missing)} runs without a result" if missing else "")))
    for key, run, lo, hi in (("L6", "nom_refresh", 20, 25), ("L13", "nom_refresh125", 4, 15)):
        if not data.ok(run):
            L.append((key, NA, f"{run}: no result"))
        else:
            L.append((key,) + p_analyze.every(R["refresh" if key == "L6" else "refresh125"], lo, hi))
    if data.ok("nom_ramp"):
        move = data.static_level("nom_ramp") - reference["static"]["nominal"]
        L.append(("L7", HOLDS if abs(move) < 0.002 else FAILS, f"static level moves by {move:+.5f}"))
    else:
        L.append(("L7", NA, "nom_ramp: no result"))
    L.sort(key=lambda x: int(x[0][1:]))
    status = NA if any(x[1] == NA for x in L) else (HOLDS if all(x[1] == HOLDS for x in L) else FAILS)
    add("S4", "L1, L2, L3, L5, L6, L7 and L13 hold on the nominal runs", status, "; ".join(f"{k} {s}" for k, s, _ in L))
    V.sort(key=lambda v: v[0])
    return V, dict(readings=R, L=L, shift=shift, missing=missing)


def report(results=RESULTS, out_path=None, second=SECOND):
    """Writes the report. The arguments are for the trial before the runs, on the results of layout 2.1."""
    data = p_analyze.Data(results)
    constants = json.loads((HERE / "constants_stage_p.json").read_text())
    ref = p_analyze.schematic_reference()
    train = p_analyze.read_csv(data.path("nom_train")) if data.ok("nom_train") else None
    V, X = verdicts(data, train, constants, ref)
    two = p_analyze.Data(second)
    V2, X2 = verdicts(two, p_analyze.read_csv(two.path("nom_train")) if two.ok("nom_train") else None, constants, ref)
    before = {k: (s, m) for k, t, s, m in V2}
    out = ["# Layout 2.2: the nominal stage, S1 to S5", "",
           "Written by `phase1/s_stage.py report` under [`PREDICTION.md`](PREDICTION.md) and [`S_STAGE.md`](S_STAGE.md). "
           "**Simulations** of the nominal cell with the source and drain areas and the extracted capacitances of layout 2.2, "
           "capacitance only, primary list; typical corner; no noise, no mismatch. No chip is built.", "",
           f"**{sum(v[2] == HOLDS for v in V)} hold, {sum(v[2] == FAILS for v in V)} fail, {sum(v[2] == NA for v in V)} not evaluable, of {len(V)}.**", "",
           "X1 to X7 of the extraction hold ([`X_REPORT.md`](X_REPORT.md)). The stage on the 8 cells starts only on the owner's word.", ""]
    if X["missing"]:
        out += ["**Runs without a result:** " + ", ".join(f"`{n}` ({data.why(n)})" for n in X["missing"]) + ".", ""]
    out += ["| | Prediction | Layout 2.2 | Layout 2.1, read the same way | Verdict |", "|---|---|---|---|---|"]
    out += [f"| {k} | {t} | {m} | {before[k][1]} ({before[k][0]}) | {s} |" for k, t, s, m in V]
    silent = X["readings"].get("silent_steps") if data.rows("nom_cell") is not None else None
    if silent:
        old = all(S5_SECOND[0] <= v <= S5_SECOND[1] for v in silent)
        out += ["", f"S5 is that of layout 2.1, not that of the second layout. **By the range of the second layout, {S5_SECOND[0]:.3f} to {S5_SECOND[1]:.3f} mV, "
                f"the silent step of layout 2.2 {'holds' if old else 'fails'}** ({min(silent):.3f} to {max(silent):.3f} mV)."]
    out += ["", "## S4, prediction by prediction", "", "| | Layout 2.2 | Verdict | Layout 2.1 |", "|---|---|---|---|"]
    b4 = {k: (s, m) for k, s, m in X2["L"]}
    out += [f"| {k} | {m} | {s} | {b4[k][1]} ({b4[k][0]}) |" for k, s, m in X["L"]]
    R = X["readings"]
    out += ["", "## Other readings", ""]
    if "counts125" in R:
        out.append(f"- At 125 °C: {R['counts125'][0]} and {R['counts125'][1]} silent pulses before the first FIRE; the joint pulse "
                   f"{'fires' if R['joint125'] else 'is silent'}.")
    if train:
        c = [float(r["c_pre"]) for r in train]
        out.append(f"- Rest charge of the nominal train: {c[1]:.6f} after a period of port 1, {c[11]:.6f} after a period of port 2.")
    sup = data.path("nom_cell", "supply.json")
    rows = data.rows("nom_cell")
    if sup.exists() and rows:
        z = json.loads(sup.read_text())["mean_A"]
        out.append(f"- Supply current of the nominal cell, reported and not predicted: {z[0] * 1e6:.2f} µA at rest, "
                   f"{sum(z[x['pulse'] + 1] for x in rows if not x['fired']) / max(1, sum(not x['fired'] for x in rows)) * 1e6:.2f} µA in a period with a silent pulse.")
    out += ["", "## Runs", "", "| Run | Result | Wall time |", "|---|---|---|"]
    for n in NAMES:
        meta = json.loads(data.path(n, "json").read_text()) if data.path(n, "json").exists() else {}
        wall = f"{meta['finished_unix'] - meta['started_unix']:.0f} s" if "finished_unix" in meta else "—"
        out.append(f"| `{n}` | {'result' if data.ok(n) else data.why(n)} | {wall} |")
    (out_path or HERE.parent / "S_REPORT.md").write_text("\n".join(out) + "\n")
    for k, t, s, m in V:
        print(k, s, "|", m)
    return V


if __name__ == "__main__":
    args = sys.argv[1:]
    if not args or args[0] == "plan":
        print("one machine:", " ".join(NAMES))
    elif args[0] == "launch":
        launch("--go" in args)
    elif args[0] == "report":
        report()
    else:
        sys.exit(__doc__)
