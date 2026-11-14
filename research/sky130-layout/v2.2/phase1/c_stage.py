"""The stage on the 8 cells of layout 2.2: C1 to C3 of ../../v2/PREDICTION.md, as declared in ../C_STAGE.md.

  python3 -I c_stage.py plan
  python3 -I c_stage.py launch --go      the 65 runs, four at a time, on one machine
  python3 -I c_stage.py report           once, after the last run: writes ../C_REPORT.md

The cells, the runs and the calibration are those of stage P (../../phase1/p_plan.py, primary
analysis), unchanged, in one queue. The runs are made by the runners of the campaigns, unchanged,
through the harness of stage P (../../phase1/p_run.py), with the capacitances of layout 2.2
(p_caps_primary.csv). The launcher is that of ../../phase1/execute.py. The analysis is that of
stage P (../../phase1/p_analyze.py: the scripts of the campaigns in a mirror, and rule A1); this
file adds the three verdicts and the words of the report.
"""
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
P1 = HERE.parent.parent / "phase1"
sys.path.insert(0, str(P1))

import execute
import p_analyze
import p_execute
import p_plan
import p_run

RESULTS = HERE / "results_c"
BUILD = HERE / "build" / "c"
STAGE_S = HERE / "results_s"
HOLDS, FAILS, NA = p_analyze.HOLDS, p_analyze.FAILS, p_analyze.NA
NO_PREDICTION = "no prediction"
S3_GATE = 0.004                 # C3 predicts only if the nominal shift of S3 is below this on both ports


def queue():
    """One queue for one machine: the seven nominal runs, then calibration and cells in turn, the
    units of the two queues of stage P taken alternately. Any prefix holds whole cells of both
    kinds with part of the calibration."""
    q = p_plan.queues()
    by = {r["name"]: r for m in q for r in q[m] if r["analysis"] == "primary"}
    out = [by[r["name"]] for m in ("A", "B") for r in p_plan.NOMINAL[m]]
    for k in range(4):
        for m in ("A", "B"):
            out += [by[r["name"]] for r in p_plan.calibration_unit(p_plan.CALIBRATION[m][k]) + p_plan.cell_unit(p_plan.CELLS[m][k])]
    assert len(out) == len(by) == len({r["name"] for r in out})
    return out


RUNS = queue()
NAMES = [r["name"] for r in RUNS]
NOMINAL = [r["name"] for m in ("A", "B") for r in p_plan.NOMINAL[m]]
PINNED = ["PREDICTION.md", "C_STAGE.md", "phase1/c_stage.py", "phase1/p_caps_primary.csv", "phase1/p_areas.csv"]


def run_one(name):
    if (RESULTS / f"{name}.csv").exists() or (RESULTS / f"{name}.failed").exists() or (RESULTS / f"{name}.json").exists():
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
    """The areas are the file the harness gives to the shim; the simulator and the models are those of stage J."""
    assert (HERE / "p_areas.csv").read_bytes() == (P1 / "p_areas.csv").read_bytes(), "the areas of layout 2.2 differ from those the harness uses"
    assert execute.digest(p_run.NGSPICE) == json.loads((P1 / "j_manifest.json").read_text())["ngspice_sha256"], "simulator changed"
    assert p_run.pdk_commit() == json.loads((P1 / "j_manifest.json").read_text())["pdk_commit"], "device models changed"
    assert (HERE.parent / "S_REPORT.md").exists(), "no report of the nominal stage"


def launch(go):
    execute.STAGE, execute.SPLIT, execute.PINNED = "C", {"A": NAMES}, PINNED
    execute.launch("A", root=HERE.parent, run_one=run_one, preflight=p_execute.preflight, verify=check_inputs, go=go)


# ---- the verdicts

def certified_ports(P, ports):
    """As L11 of stage P reads it: certified at status 3 or eligible by rule A1; and those contradicted."""
    certified, wrong = [], []
    for c, q in ports:
        s3 = P["amended"].get((c, q), {}).get("status3", "")
        by3, by1 = s3.startswith("certified"), P["a1"].get((c, q), {}).get("eligible", False)
        if by3 or by1:
            certified.append((c, q, by3, by1))
            if s3 == "certified, count contradicted" or P["a1"].get((c, q), {}).get("contradicted", False):
                wrong.append(f"{c} port {q}")
    return certified, wrong


def enough_certified(n):
    """How many certified ports C2 asks for with n evaluable ports: 2 of the 16; ../C_STAGE.md for fewer."""
    return 2 if n >= 14 else (1 if n >= 6 else None)


def verdicts(P, X, s3_shift):
    """P: the tables of p_analyze.pipeline. X: what p_analyze.verdicts found (evaluable cells and ports).
    s3_shift: {1: shift, 2: shift} of the nominal stage, or None."""
    V = []
    ports = X["ports"]
    a1 = P["a1"]
    seen = [p for p in ports if p in a1 and not a1[p]["reasons"].startswith("not evaluable")]
    refused = [p for p in seen if "rest charge" in a1[p]["reasons"].split("; ")]
    text = "No port is refused for its rest state"
    if not seen:
        V.append(("C1", text, NA, f"no port on which rule A1 can be read, of {len(ports)} evaluable ports"))
    else:
        V.append(("C1", text, FAILS if refused else HOLDS,
                  f"{len(refused)} of {len(seen)} ports refused for their rest state"
                  + (": " + ", ".join(f"{c} port {q}" for c, q in refused) if refused else "")
                  + (f"; rule A1 not readable on {len(ports) - len(seen)} more" if len(seen) < len(ports) else "")))

    certified, wrong = certified_ports(P, ports)
    n, need = len(ports), enough_certified(len(ports))
    text = "No certified port has a count different from its need, and at least 2 of the 16 ports are certified, at status 3 or by rule A1"
    measured = (f"{len(certified)} certified ports of {n} ({sum(b for _, _, b, _ in certified)} at status 3, "
                f"{sum(b for _, _, _, b in certified)} by rule A1); contradicted: {', '.join(wrong) if wrong else 'none'}")
    if n == 0:
        V.append(("C2", text, NA, "no evaluable port"))
    elif wrong:
        V.append(("C2", text, FAILS, measured))
    elif need is None:
        V.append(("C2", text, NA, measured + f"; with {n} evaluable ports the number asked for is not defined"))
    else:
        V.append(("C2", text, HOLDS if len(certified) >= need else FAILS, measured + (f"; {need} asked for with {n} evaluable ports" if n != 16 else "")))

    large = [(c, q) for c, q in p_analyze.LARGE if c in X["cells"]]
    again = [f"{c} port {q}" for c, q in large if P["amended"].get((c, q), {}).get("status3", "").startswith("certified")]
    reading = f"{len(again)} of {len(large)} evaluable ports of L12 certified again at status 3" + (": " + ", ".join(again) if again else "")
    text = f"No prediction on the four ports of L12 unless S3 gives a shift below {S3_GATE} on both ports; if it does, at least 2 of the 4 are certified again at status 3"
    if s3_shift is None:
        V.append(("C3", text, NA, "no shift of the nominal stage; " + reading))
    elif not all(abs(s) < S3_GATE for s in s3_shift.values()):
        V.append(("C3", text, NO_PREDICTION, f"S3 gave {s3_shift[1]:+.5f} and {s3_shift[2]:+.5f}; " + reading))
    elif len(large) < 4:
        V.append(("C3", text, NA, f"S3 gave {s3_shift[1]:+.5f} and {s3_shift[2]:+.5f}; " + reading))
    else:
        V.append(("C3", text, HOLDS if len(again) >= 2 else FAILS, f"S3 gave {s3_shift[1]:+.5f} and {s3_shift[2]:+.5f}; " + reading))
    return V


def nominal_shift():
    """The shift of S3, computed again from the committed results of the nominal stage, as s_stage.py does."""
    data = p_analyze.Data(STAGE_S)
    if not (data.ok("nom_ramp") and data.ok("nom_read")):
        return None
    constants = json.loads((HERE / "constants_stage_p.json").read_text())
    post = p_analyze.nominal_gap(p_analyze.floats(p_analyze.read_csv(data.path("nom_read"))), data.static_level("nom_ramp"), constants)
    ref = p_analyze.schematic_reference()
    return None if None in post.values() else {q: post[q] - ref["nominal_gap"][q] for q in (1, 2)}


def analysis(results, work):
    data = p_analyze.Data(results)
    ref = p_analyze.schematic_reference()
    P = p_analyze.pipeline(data, work, "stage")
    L, X = p_analyze.verdicts(data, P, ref)
    return data, ref, P, L, X


def report(results=RESULTS, out_path=None, first=P1 / "results_p", shift=None):
    """Writes the report. The arguments are for the trial before the runs, on the results of the first layout."""
    fm = p_analyze.fm
    data, ref, P, L, X = analysis(results, HERE / "build" / "c_analysis" / "stage")
    shift = shift if shift is not None else nominal_shift()
    V = verdicts(P, X, shift)
    data1, _, P1_, L1, X1 = analysis(first, HERE / "build" / "c_analysis" / "first")
    # the first layout had no nominal stage of this kind: its C3 is given as a reading only
    V1 = {k: (s if k != "C3" else "a reading, not a verdict", m.replace("no shift of the nominal stage; ", ""))
          for k, t, s, m in verdicts(P1_, X1, None)}
    cal = P["calibration"]
    R = X["readings"]
    out = ["# Layout 2.2: the stage on the 8 cells, C1 to C3", "",
           "Written by `phase1/c_stage.py report` under [`PREDICTION.md`](PREDICTION.md) and [`C_STAGE.md`](C_STAGE.md). "
           "**Simulations** of the cell of `cell.spice` with the source and drain areas and the extracted capacitances of layout 2.2, "
           "capacitance only, primary list; typical corner; 8 cells with mismatch, each with one noisy test run; "
           "8 calibration cells. No chip is built.", "",
           "**Confirmatory**: X1 to X7 and S1 to S5 hold on layout 2.2 ([`X_REPORT.md`](X_REPORT.md), [`S_REPORT.md`](S_REPORT.md)), "
           "and the declaration was pushed before the first run.", "",
           f"**{sum(v[2] == HOLDS for v in V)} hold, {sum(v[2] == FAILS for v in V)} fail, {sum(v[2] == NA for v in V)} not evaluable, "
           f"{sum(v[2] == NO_PREDICTION for v in V)} without a prediction, of {len(V)}.**", ""]
    if X["missing"]:
        out += [f"**The campaign is truncated: {len(X['missing'])} runs of its scope have no result:** "
                + ", ".join(f"`{n}` ({data.why(n)})" for n in X["missing"]) + ".", ""]
    out += ["| | Prediction | Layout 2.2 | First layout, read the same way | Verdict |", "|---|---|---|---|---|"]
    out += [f"| {k} | {t} | {m} | {V1[k][1]} ({V1[k][0]}) | {s} |" for k, t, s, m in V]
    out += ["", "## What the verdicts rest on", "",
            f"- Constants: {P['note']}. `d0` = {fm(cal.get('d0'), '.6f')}, `kappa` = {fm(cal.get('kappa'), '.6f')}, "
            f"`mu` = {fm(cal.get('mu'), '+.6f')}, `h_mu` = {fm(cal.get('h_mu'), '.6f')}; "
            f"in the campaign on the schematic {ref['calibration']['d0']:.6f}, {ref['calibration']['kappa']:.6f}, {ref['calibration']['mu']:+.6f}, {ref['calibration']['h_mu']:.6f}.",
            f"- Evaluable cells: {len(X['cells'])} of 8 ({', '.join(X['cells'])}); evaluable ports: {len(X['ports'])}.",
            "- C2 can fail on one port and cannot establish a rate: with no contradiction among n certified ports the 95% upper "
            "bound on the rate is 1 − 0.05^(1/n) (53% for 4, 31% for 8, 17% for 16).",
            "- One layout, one extraction by Magic's rules, capacitance only; 8 cells drawn by the mismatch models of the PDK, one noise "
            "draw each. Nothing about silicon."]
    same = [n for n in NOMINAL if data.ok(n) and (STAGE_S / f"{n}.csv").exists() and data.path(n).read_bytes() == (STAGE_S / f"{n}.csv").read_bytes()]
    both = [n for n in NOMINAL if data.ok(n) and (STAGE_S / f"{n}.csv").exists()]
    if both:
        out.append(f"- The seven nominal runs were made again in this stage: {len(same)} of {len(both)} give the rows of the nominal stage, byte for byte"
                   + ("." if len(same) == len(both) else "; not the same: " + ", ".join(f"`{n}`" for n in both if n not in same) + "."))
    out += ["", "## Ports", "",
            "Schematic: the committed values of the same cell and port. Layout 2.2: this stage, constants of this stage.", "",
            "| Cell | Port | Static level, move | Gap, schematic | Gap, layout 2.2 | Need, schematic | Need, layout 2.2 | Count | Status 3, schematic | Status 3, layout 2.2 | Room at status 3 | Rule A1 | Rooms of rule A1, silence and FIRE |",
            "|---|---|---|---|---|---|---|---|---|---|---|---|---|"]
    lev = dict(X["levels"])
    for c in p_analyze.CELLS:
        for q in (1, 2):
            p, o, a, s = P["predictions"].get((c, q), {}), P["ports"].get((c, q), {}), P["amended"].get((c, q), {}), ref["predictions"][(c, q)]
            r1 = P["a1"].get((c, q), {})
            a1 = "eligible" + (", contradicted" if r1.get("contradicted") else "") if r1.get("eligible") else ("not eligible: " + r1.get("reasons", "") if r1 else "—")
            rooms = f"{r1['silence_room']:+.5f} and {r1['fire_room']:+.5f}" if "silence_room" in r1 else "—"
            out.append(f"| `{c}` | {q} | {fm(lev.get(c))} | {fm(s['gap'])} | {fm(p.get('gap'))} | {s['m']} | {p.get('m', '') or '—'} | "
                       f"{o.get('count', '') or '—'} | {ref['amended'][(c, q)]['status3']} | {a.get('status3', '') or '—'} | {fm(a.get('room3'))} | {a1} | {rooms} |")
    out += ["", "## The predictions of stage P, read on layout 2.2", "",
            "**Not predictions of this stage, and no verdict of it.** L1 to L13 were made for the first layout "
            "([`../PREDICTION.md`](../PREDICTION.md)); they are read here by the script of stage P, unchanged, so that the two layouts can be compared.", "",
            "| | Prediction of stage P | Layout 2.2 | Would be | First layout | Was |", "|---|---|---|---|---|---|"]
    b = {k: (s, m) for k, t, s, m in L1}
    out += [f"| {k} | {t} | {m} | {s} | {b[k][1]} | {b[k][0]} |" for k, t, s, m in L]
    out += ["", "## Readings outside any verdict", ""]
    if "counts125" in R:
        a, b = R["counts125"]
        line = (f"- **At 125 °C the two ports of the nominal cell fire after {a} and {b} silent pulses"
                + (", not after the same number" if a != b else "") + ".** No prediction covers it: a reading outside any verdict. "
                f"The joint pulse {'fires' if R['joint125'] else 'is silent'}.")
        rows = p_analyze.Data(STAGE_S).rows("nom_cell125")
        if rows is not None:
            s = [p_analyze.j_stage.series(rows, q) for q in (1, 2)]
            k = [len(x) if p_analyze.j_stage.first_fire(x) is None else p_analyze.j_stage.first_fire(x) for x in s]
            line += f" In the nominal stage of layout 2.2: {k[0]} and {k[1]}."
        out.append(line)
    if "counts" in R:
        out.append(f"- At 27 °C: {R['counts'][0]} and {R['counts'][1]} silent pulses before the first FIRE; silent steps "
                   f"{min(R['silent_steps']):.3f} to {max(R['silent_steps']):.3f} mV.")
    if shift:
        out.append(f"- Shift of the gap of the nominal cell: {shift[1]:+.5f} and {shift[2]:+.5f} with the constants of stage P (S3)"
                   + (f"; {X['shift'][1]:+.5f} and {X['shift'][2]:+.5f} with the constants of this stage." if X["shift"] else "."))
    sup = data.path("nom_cell", "supply.json")
    rows = data.rows("nom_cell")
    if sup.exists() and rows:
        z = json.loads(sup.read_text())["mean_A"]
        out.append(f"- Supply current of the nominal cell, reported and not predicted: {z[0] * 1e6:.2f} µA at rest, "
                   f"{sum(z[x['pulse'] + 1] for x in rows if not x['fired']) / max(1, sum(not x['fired'] for x in rows)) * 1e6:.2f} µA in a period with a silent pulse.")
    out += ["", "## Runs", "", "In the order of the queue, four at a time.", "", "| Group | Run | Result | Wall time |", "|---|---|---|---|"]
    for k, n in enumerate(NAMES):
        meta = json.loads(data.path(n, "json").read_text()) if data.path(n, "json").exists() else {}
        wall = f"{meta['finished_unix'] - meta['started_unix']:.0f} s" if "finished_unix" in meta else "—"
        out.append(f"| {k // 4 + 1} | `{n}` | {'result' if data.ok(n) else data.why(n)} | {wall} |")
    bad = [f"{k}: status {v[0]}" for k, v in P["log"].items() if v[0] != 0]
    if bad:
        out += ["", "Scripts of the campaigns that ended with an error: " + "; ".join(bad) + "."]
    (out_path or HERE.parent / "C_REPORT.md").write_text("\n".join(out) + "\n")
    for k, t, s, m in V:
        print(k, s, "|", m)
    return V


if __name__ == "__main__":
    args = sys.argv[1:]
    if not args or args[0] == "plan":
        for k in range(0, len(NAMES), 4):
            print(f"group {k // 4 + 1:2d}:", " ".join(NAMES[k:k + 4]))
        print(len(NAMES), "runs")
    elif args[0] == "launch":
        launch("--go" in args)
    elif args[0] == "report":
        report()
    else:
        sys.exit(__doc__)
