"""Analysis of stage P: the verdicts of L1 to L13 of ../PREDICTION.md. No simulation is run.

  python3 -I p_analyze.py report      once, after the last run of both machines: writes P_REPORT.md

The rules of the certification campaigns are applied by their own scripts, unchanged. The results
of stage P are copied into a mirror of research/circuit (p_run.mirror) and there run, in order:

  certification/cert_analyze.py calibrate, predict, certify       constants, need m, budget
  certification-unconditional/uncond_analyze.py report            conditions 1 and 2
  certification-unconditional/uncond_amend1.py report             status 3 of amendment 1

Rule A1 of ../../reusable-controller/physical/ASYMMETRIC_PROTOCOL.md is computed here with the
functions of asymmetric_check.py (directional_bounds, padded, reported, room_gates).

Two sets of constants (decision D6): those calibrated on the post-layout cell, which decide the
predictions, and those of ../../circuit/certification/calibration.json, reported apart.

The rules for a campaign with runs missing are those of ../AMENDMENT_2.md; the secondary analysis
is that of ../AMENDMENT_3.md; the definitions fixed before the runs are in ../AMENDMENT_4.md.
"""
import csv
import json
import math
import shutil
import subprocess
import sys
from fractions import Fraction as Q
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import j_stage
import p_plan
import p_run

CIRCUIT = HERE.parent.parent / "circuit"
PHYSICAL = HERE.parent.parent / "reusable-controller" / "physical"
RESULTS = HERE / "results_p"
REF = HERE / "ref_p"
HOLDS, FAILS, NA = "holds", "fails", "not evaluable"
SENTENCE = "The earlier 125 °C result, a stop with no relapse after it, was an artifact of netlists without junction areas."
LARGE = [("t6065", 1), ("t6002", 1), ("t6074", 1), ("t6051", 2)]
CELLS = [f"t{s}" for s in p_plan.LARGE + p_plan.SMALL]


def read_csv(path):
    with open(path, newline="") as fh:
        return list(csv.DictReader(fh))


class Data:
    """The results of a campaign, in a folder of files NAME.csv, NAME.json, NAME.failed."""

    def __init__(self, folder, prefix=""):
        self.folder, self.prefix = Path(folder), prefix
        sys.path.insert(0, str(CIRCUIT))
        import analyze
        self.analyze = analyze

    def path(self, name, ext="csv"):
        return self.folder / f"{self.prefix}{name}.{ext}"

    def ok(self, name):
        return self.path(name).exists() and not self.path(name, "failed").exists()

    def why(self, name):
        if self.path(name, "failed").exists():
            return "run failed"
        if self.path(name, "lost").exists():
            return "run lost"
        return None if self.path(name).exists() else "no result"

    def rows(self, name):
        """Rows of a run of run.py, or None."""
        if not self.ok(name):
            return None
        return self.analyze.read_run(self.path(name))[0]

    def static_level(self, name):
        return float(read_csv(self.path(name))[0]["static_level"]) if self.ok(name) else None


def cell_runs(cell):
    seed = cell[1:]
    return [f"t{seed}_ramp", f"t{seed}_read", f"u{seed}_leak", f"u{seed}_train", f"t{seed}_train"]


def pipeline(data, root, constants):
    """Run the scripts of the campaigns on the results of `data`, in the mirror `root`.
    constants: "stage" (calibrated here) or "campaign" (the committed calibration.json).
    Returns the tables the scripts write, and what was used for the constants."""
    plan = [r for q in p_plan.queues().values() for r in q if r["analysis"] == "primary" and r["tool"] != "circuit"]
    units = [s for s in p_plan.CALIBRATION["A"] + p_plan.CALIBRATION["B"] if data.ok(f"c{s}_train") and data.ok(f"c{s}_ramp")]
    leaks = [s for s in p_plan.LEAK_CALIBRATION if s in units and data.ok(f"c{s}_leak")]
    nominal = data.ok("nom_leak") and data.ok("nom_ramp")
    enough = len(units) >= 4 and len(leaks) >= 1 and nominal
    note = (f"calibrated on {len(units)} cells and {len(leaks) + 1} leak scans" if enough else
            f"only {len(units)} calibration units, {len(leaks)} calibration leak scans, nominal leak scan "
            f"{'present' if nominal else 'absent'}: the constants of the campaign are used")
    if constants == "campaign":
        note = "constants of ../../circuit/certification/calibration.json"
    keep = []
    for r in plan:
        if r["stage"] == "calibration":
            seed = r["seed"]
            if seed not in units or (r["mode"] == "leak" and seed not in leaks):
                continue
        keep.append(r)
    shutil.rmtree(root, ignore_errors=True)
    p_run.mirror(root, keep)
    for r in keep:
        folder = root / ("certification" if r["tool"] == "cert" else "certification-unconditional") / "results" / r["stage"]
        folder.mkdir(parents=True, exist_ok=True)
        name = r["name"]
        if data.path(name, "failed").exists() or data.path(name, "lost").exists() or not data.path(name).exists():
            if data.path(name, "failed").exists():
                shutil.copy(data.path(name, "failed"), folder / f"{name}.failed")
            continue
        for ext in ("json", "charge.csv", "early.csv") + (() if r["mode"] == "ramp" else ("csv",)):
            if data.path(name, ext).exists():
                shutil.copy(data.path(name, ext), folder / f"{name}.{ext}")

    def script(folder, *args):
        p = subprocess.run([sys.executable, "-B"] + list(args), cwd=root / folder, capture_output=True, text=True)
        return p.returncode, (p.stdout + p.stderr)[-1500:]
    log = {}
    cert = root / "certification"
    if constants == "stage" and enough:
        log["calibrate"] = script("certification", "cert_analyze.py", "calibrate")
    else:
        shutil.copy(CIRCUIT / "certification" / "calibration.json", cert / "calibration.json")
    for step in ("predict", "certify"):
        log[step] = script("certification", "cert_analyze.py", step)
    log["uncond"] = script("certification-unconditional", "uncond_analyze.py", "report")
    log["amend1"] = script("certification-unconditional", "uncond_amend1.py", "report")
    out = dict(note=note, log=log, calibrated=constants == "stage" and enough, root=root)
    out["calibration"] = json.loads((cert / "calibration.json").read_text()) if (cert / "calibration.json").exists() else {}
    for key, path in (("predictions", cert / "predictions.csv"), ("ports", cert / "ports.csv"),
                      ("amended", root / "certification-unconditional" / "ports_amendment1.csv")):
        out[key] = {(r["cell"], int(r["port"])): r for r in read_csv(path)} if path.exists() else {}
    out["a1"] = rule_a1(data, out)
    return out


def rule_a1(data, P):
    """Rule A1 for each port: eligible, contradicted, the two rooms, the reasons. With the functions
    of asymmetric_check.py and the quantities its `analyse` uses."""
    sys.path.insert(0, str(PHYSICAL))
    import asymmetric_check as A
    S = A.source
    cal = P["calibration"]
    if "kappa" not in cal or cal.get("d0") is None:
        return {}
    exact = json.loads((P["root"] / "certification" / "calibration.json").read_text(), parse_float=Q)
    trains = {c: read_csv(data.path(f"{c}_train")) for c in CELLS if data.ok(f"{c}_train")}
    silent = [abs(S.gain(r) - S.gain(r, True) - cal["kappa"]) for rows in trains.values() for r in rows
              if r["port"] in ("1", "2") and r["fired"] == "0"]
    if not silent:
        return {}
    eps_kappa = max(silent)
    out = {}
    for (cell, port), pred in P["predictions"].items():
        old, am = P["ports"].get((cell, port), {}), P["amended"].get((cell, port), {})
        res = dict(eligible=False, contradicted=False, reasons="", eps_kappa=eps_kappa)
        out[(cell, port)] = res
        try:
            S.require(cell in trains, "noisy test run missing")
            S.require(pred.get("m", "") != "" and old.get("a", "") != "" and am.get("eps3", "") != "" and am.get("h3", "") != ""
                      and old.get("count", "") != "", "a quantity of the earlier statuses is not evaluable")
            m = int(pred["m"])
            prefix = [r for r in trains[cell] if int(r["port"]) == port][:m + 1]
            S.require(len(prefix) == m + 1, "missing target read")
            y = [A.reported(r, cal["kappa"]) for r in prefix]
            bs, bf = A.directional_bounds(y, [r["fired"] == "1" for r in prefix], eps_kappa, cal["d0"])
            ell = Q(am["h3"]) + max(Q(r["noise_sup_V"]) * 2 for r in prefix) + Q(1, 5000)
            v = dict(level=Q(pred["level0"]), dose=exact["d0"], a=Q(old["a"]) + A.PAD, eps=Q(am["eps3"]) + A.PAD,
                     bs=A.padded(bs), bf=A.padded(bf), ell=A.padded(ell))
            silence = v["dose"] / 2 - (v["a"] + v["eps"]) - (v["bs"] + 2 * v["eps"]) - Q(20, 17) * v["ell"] - Q(1, 8000)
            fire = v["dose"] / 2 - (v["a"] + v["eps"]) - (v["bf"] + 2 * v["eps"]) - Q(20, 17) * v["ell"]
            reasons = []
            if any(not .1 <= float(r["c_pre"]) <= .1001 for r in prefix):
                reasons.append("rest charge")
            if any(float(r["latch_rises"]) > 1 for r in prefix):
                reasons.append("multiple latch rises")
            if any(float(r[f"steer_rises{port}"]) != (0 if r["fired"] == "1" else 1) or float(r[f"steer_rises{3 - port}"]) != 0
                   for r in prefix):
                reasons.append("steering")
            if v["level"] - v["ell"] < Q(19, 20):
                reasons.append("threshold floor")
            if not A.room_gates(silence, fire):
                reasons += (["silence room"] if silence <= 0 else []) + (["FIRE room"] if fire < 0 else [])
            res.update(silence_room=float(silence), fire_room=float(fire), eligible=not reasons,
                       contradicted=not reasons and int(old["count"]) != m, reasons="; ".join(reasons))
        except (S.CampaignError, ValueError, OverflowError, KeyError) as error:
            res["reasons"] = "not evaluable: " + str(error)
    return out


def nominal_gap(read_rows, static_level, cal):
    """Gap of each port of a nominal cell from its read and its ramp, by the formula of cert_analyze.predict."""
    sys.path.insert(0, str(CIRCUIT / "certification"))
    import cert_analyze as C
    out = {}
    for port in (1, 2):
        r = C.reads_of(read_rows, port)[0]
        g = C.gain(r, cal["kappa"])
        out[port] = None if g is None else math.log(static_level + cal["mu"] - 0.1) - g
    return out


def floats(rows):
    return [{k: float(v) for k, v in r.items()} for r in rows]


def single_run_readings(data, guard_runs):
    """What is read on the nominal runs: used for the verdicts and for the secondary analysis."""
    R = {}
    rows = data.rows("nom_cell")
    if rows is not None:
        s = [j_stage.series(rows, q) for q in (1, 2)]
        k = [j_stage.first_fire(x) for x in s]
        stops = all(ki is not None and all(x["fired"] for x in si[ki:]) for ki, si in zip(k, s))
        silent = [x["step"][q] for q in (1, 2) for x in j_stage.series(rows, q) if not x["fired"]]
        firing = [x["step"][q] for x in rows for q in (1, 2) if x["fired"] and x["port"] in (q, 0)]
        R.update(counts=[len(si) if ki is None else ki for ki, si in zip(k, s)], stops=stops, silent_steps=silent,
                 firing_steps=firing, joint=rows[-1]["fired"])
    for key, name in (("refresh", "nom_refresh"), ("refresh125", "nom_refresh125")):
        rows = data.rows(name)
        if rows is not None:
            R[key] = j_stage.silent_after_stop(rows)
    rows = data.rows("nom_cell125")
    if rows is not None:
        s = [j_stage.series(rows, q) for q in (1, 2)]
        R["counts125"] = [len(si) if j_stage.first_fire(si) is None else j_stage.first_fire(si) for si in s]
        R["joint125"] = rows[-1]["fired"]
    events = []
    for name in guard_runs:
        rows, why = data.analyze.read_run(data.path(name)) if data.ok(name) and name.split("_")[-1] != "ramp" else (None, None)
        if data.path(name, "restfire").exists():
            events.append(f"{name}: protection in the period at rest")
        if data.ok(name) and data.path(name, "json").exists() and json.loads(data.path(name, "json").read_text()).get("rest_fire"):
            events.append(f"{name}: protection in the period at rest")
        for x in rows or []:
            e = data.analyze.not_a_fire(x) or data.analyze.against(x)
            if e:
                events.append(f"{name} pulse {x['pulse']}: {e}")
    R["events"] = events
    return R


def every(silent, lo, hi):
    if silent is None:
        return FAILS, "no FIRE"
    gaps = [b - a for a, b in zip(silent, silent[1:])]
    return (HOLDS if len(silent) >= 2 and all(lo <= g <= hi for g in gaps) else FAILS), f"silent after the stop at pulses {silent}; intervals {gaps}"


def verdicts(data, P, reference):
    """The thirteen verdicts. reference: schematic values (static levels, predictions, nominal gaps)."""
    primary = [r["name"] for q in p_plan.queues().values() for r in q if r["analysis"] == "primary"]
    missing = [n for n in primary if not data.ok(n)]
    R = single_run_readings(data, [n for n in primary if data.ok(n)])
    V = []

    def add(key, text, status, measured):
        V.append((key, text, status, measured))

    def on(run, key, text, fn):
        if not data.ok(run):
            add(key, text, NA, f"{run}: {data.why(run)}")
        else:
            add(key, text, *fn())

    on("nom_cell", "L1", "The nominal cell stops by itself: silent pulses, then a FIRE on every later pulse of each series",
       lambda: (HOLDS if R["stops"] else FAILS, f"first FIRE after {R['counts'][0]} and {R['counts'][1]} silent pulses; "
                + ("no silent pulse after it" if R["stops"] else "a series has no FIRE or a silent pulse after its first FIRE")))
    on("nom_cell", "L2", "The nominal count of silent pulses is 3, 4 or 5, the same on both ports",
       lambda: (HOLDS if R["counts"][0] == R["counts"][1] and R["counts"][0] in (3, 4, 5) else FAILS, f"{R['counts'][0]} and {R['counts'][1]}"))
    on("nom_cell", "L3", "A silent pulse of the nominal cell writes between 1.33 and 1.42 mV",
       lambda: (HOLDS if R["silent_steps"] and all(1.33 <= v <= 1.42 for v in R["silent_steps"]) else FAILS,
                f"{len(R['silent_steps'])} silent steps from {min(R['silent_steps']):.3f} to {max(R['silent_steps']):.3f} mV" if R["silent_steps"] else "no silent pulse"))
    on("nom_cell", "L4", "A firing pulse of the nominal cell moves the stored voltage by at most 0.005 mV",
       lambda: (HOLDS if R["firing_steps"] and all(abs(v) <= 0.005 for v in R["firing_steps"]) else FAILS,
                f"{len(R['firing_steps'])} steps of firing pulses, largest {max(abs(v) for v in R['firing_steps']):.3f} mV" if R["firing_steps"] else "no firing pulse"))
    add("L5", "The guard reports nothing on any run",
        NA if missing else (FAILS if R["events"] else HOLDS),
        ("; ".join(R["events"]) if R["events"] else "nothing") + (f"; {len(missing)} runs without a result" if missing else ""))
    on("nom_refresh", "L6", "Under 0.1 TΩ the nominal cell falls silent once every 20 to 25 periods",
       lambda: every(R["refresh"], 20, 25))

    # cells and ports
    cells = [c for c in CELLS if all(data.ok(n) for n in cell_runs(c))]
    ports = [(c, q) for c in cells for q in (1, 2)]
    pred, old, am, a1 = P["predictions"], P["ports"], P["amended"], P["a1"]
    sch = reference["predictions"]

    levels = []
    if data.ok("nom_ramp"):
        levels.append(("nominal", data.static_level("nom_ramp") - reference["static"]["nominal"]))
    levels += [(c, data.static_level(f"{c}_ramp") - reference["static"][c]) for c in cells]
    if not data.ok("nom_ramp") and not cells:
        add("L7", "The static FIRE level moves by less than 0.002 level unit", NA, "no ramp")
    else:
        worst = max(levels, key=lambda x: abs(x[1]))
        add("L7", "The static FIRE level of the nominal cell and of each cell moves by less than 0.002 level unit",
            HOLDS if all(abs(d) < 0.002 for _, d in levels) else FAILS,
            f"{len(levels)} cells; largest move {worst[1]:+.5f} ({worst[0]})"
            + ("" if data.ok("nom_ramp") else "; nominal ramp without a result"))

    shift = None
    if data.ok("nom_ramp") and data.ok("nom_read") and "mu" in P["calibration"] and P["calibration"].get("mu") is not None:
        post = nominal_gap(floats(read_csv(data.path("nom_read"))), data.static_level("nom_ramp"), P["calibration"])
        if None not in post.values():
            shift = {q: post[q] - reference["nominal_gap"][q] for q in (1, 2)}
    gaps = [(c, q, float(pred[(c, q)]["gap"]) - float(sch[(c, q)]["gap"])) for c, q in ports
            if pred.get((c, q), {}).get("gap", "") != ""]
    if shift is None or not gaps:
        add("L8", "The gap of the nominal cell moves by −0.005 to +0.030; each port follows within ±0.004", NA,
            "nominal ramp, nominal read or the constants are missing" if shift is None else "no evaluable port")
    else:
        rel = [(c, q, d - shift[q]) for c, q, d in gaps]
        worst = max(rel, key=lambda x: abs(x[2]))
        ok = all(-0.005 <= s <= 0.030 for s in shift.values()) and all(abs(d) <= 0.004 for _, _, d in rel)
        add("L8", "The gap of the nominal cell moves by −0.005 to +0.030; each port follows within ±0.004", HOLDS if ok else FAILS,
            f"nominal shift {shift[1]:+.5f} (port 1) and {shift[2]:+.5f} (port 2); {len(rel)} ports, "
            f"largest distance to the nominal shift {worst[2]:+.5f} ({worst[0]} port {worst[1]})")

    needs = [(c, q, int(pred[(c, q)]["m"]) - int(sch[(c, q)]["m"])) for c, q in ports if pred.get((c, q), {}).get("m", "") != ""]
    if not needs:
        add("L9", "The need of each port changes by 0 or +1", NA, "no evaluable port")
    else:
        bad = [f"{c} port {q}: {d:+d}" for c, q, d in needs if d not in (0, 1)]
        add("L9", "The need of each port changes by 0 or +1", FAILS if bad else HOLDS,
            f"{len(needs)} ports: {sum(d == 0 for _, _, d in needs)} unchanged, {sum(d == 1 for _, _, d in needs)} at +1"
            + (", others: " + ", ".join(bad) if bad else ""))

    counted = [(c, q, old[(c, q)]["count_agrees"] == "True") for c, q in ports if old.get((c, q), {}).get("count_agrees", "") != ""]
    n = len(counted)
    if n < 3:
        add("L10", "The observed count equals the post-layout need on enough ports", NA, f"{n} evaluable ports")
    else:
        need = n - 3 if n >= 13 else (n - 2 if n >= 6 else n - 1)
        agree = sum(a for _, _, a in counted)
        add("L10", f"The observed count equals the post-layout need on at least {need} of {n} ports",
            HOLDS if agree >= need else FAILS, f"{agree} of {n}")

    certified, wrong = [], []
    for c, q in ports:
        s3 = am.get((c, q), {}).get("status3", "")
        by3, by1 = s3.startswith("certified"), a1.get((c, q), {}).get("eligible", False)
        if by3 or by1:
            certified.append((c, q, by3, by1))
            if s3 == "certified, count contradicted" or a1.get((c, q), {}).get("contradicted", False):
                wrong.append(f"{c} port {q}")
    if not ports:
        add("L11", "No certified port has a count different from its need", NA, "no evaluable port")
    else:
        add("L11", "No port certified post-layout, at status 3 or by rule A1, has a count different from its need",
            FAILS if wrong else HOLDS,
            f"{len(certified)} certified ports of {len(ports)} ({sum(b for _, _, b, _ in certified)} at status 3, "
            f"{sum(b for _, _, _, b in certified)} by rule A1); contradicted: {', '.join(wrong) if wrong else 'none'}")

    large = [(c, q) for c, q in LARGE if c in cells]
    k = len(large)
    if k == 0:
        add("L12", "Of the status-3 ports with the largest room, enough are certified again at status 3", NA, "none evaluable")
    else:
        need = {4: 3, 3: 2, 2: 1, 1: 1}[k]
        again = [f"{c} port {q}" for c, q in large if am.get((c, q), {}).get("status3", "").startswith("certified")]
        add("L12", f"Of the {k} evaluable status-3 ports with the largest room, at least {need} are certified again at status 3",
            HOLDS if len(again) >= need else FAILS, f"{len(again)} of {k}: {', '.join(again) if again else 'none'}")

    on("nom_refresh125", "L13", "At 125 °C the nominal cell stops, then falls silent again once every 4 to 15 periods",
       lambda: every(R["refresh125"], 4, 15))
    return V, dict(readings=R, cells=cells, ports=ports, missing=missing, shift=shift, levels=levels, certified=certified)


def schematic_reference():
    cert = CIRCUIT / "certification"
    static = {"nominal": json.loads((cert / "results" / "preflight" / "nom_ramp.json").read_text())["static_level"]}
    for c in CELLS:
        static[c] = json.loads((cert / "results" / "characterization" / f"{c}_ramp.json").read_text())["static_level"]
    cal = json.loads((cert / "calibration.json").read_text())
    return dict(static=static, calibration=cal,
                predictions={(r["cell"], int(r["port"])): r for r in read_csv(cert / "predictions.csv")},
                ports={(r["cell"], int(r["port"])): r for r in read_csv(cert / "ports.csv")},
                amended={(r["cell"], int(r["port"])): r for r in read_csv(CIRCUIT / "certification-unconditional" / "ports_amendment1.csv")},
                nominal_gap=nominal_gap(floats(read_csv(REF / "nom_read.csv")), static["nominal"], cal))


def fm(x, spec="+.5f"):
    return "—" if x is None or x == "" else format(float(x), spec)


def report(results=RESULTS, out_path=None, work=None):
    """Writes the report. The arguments are for the tests, which try it on results of the schematic."""
    data = Data(results)
    ref = schematic_reference()
    work = work or HERE / "build" / "p_analysis"
    P = pipeline(data, work / "stage", "stage")
    F = pipeline(data, work / "campaign", "campaign")
    V, X = verdicts(data, P, ref)
    VF, XF = verdicts(data, F, ref)
    sec = Data(results, "s_")
    S = single_run_readings(sec, [n[2:] for q in p_plan.queues().values() for n in (r["name"] for r in q) if n.startswith("s_") and sec.ok(n[2:])])
    R = X["readings"]
    cal = P["calibration"]
    out = ["# Stage P: report", "",
           "Written by `p_analyze.py report` under [`../PREDICTION.md`](../PREDICTION.md) and its four amendments. "
           "**Simulations** of the cell of `cell.spice` with the source and drain areas of the layout and its extracted "
           "capacitances, capacitance only; typical corner; the primary list of capacitances "
           "([`../AMENDMENT_3.md`](../AMENDMENT_3.md)). No chip is built.", "",
           f"**{sum(v[2] == HOLDS for v in V)} hold, {sum(v[2] == FAILS for v in V)} fail, {sum(v[2] == NA for v in V)} not evaluable, of {len(V)}.**", ""]
    against = [v[0] for v in V if v[0] in ("L1", "L5", "L11") and v[2] == FAILS]
    shifts = [v[0] for v in V if v[0] in ("L2", "L3", "L8", "L9", "L12") and v[2] == FAILS]
    out += ["- Against the layout bet (L1, L5 or L11 failing): " + (", ".join(against) if against else "none") + ".",
            "- A shift and not a failure (L2, L3, L8, L9 or L12 outside its range): " + (", ".join(shifts) if shifts else "none") + ".", ""]
    if X["missing"]:
        out += [f"**The campaign is truncated: {len(X['missing'])} runs of its scope have no result:** "
                + ", ".join(f"`{n}` ({data.why(n)})" for n in X["missing"]) + ".", ""]
    out += ["| | Prediction | Measured | Verdict |", "|---|---|---|---|"]
    out += [f"| {k} | {t} | {m} | {s} |" for k, t, s, m in V]
    out.append("")
    l13 = next(v for v in V if v[0] == "L13")
    if l13[2] == HOLDS:
        out += [f"**{SENTENCE}** This rests on a nominal simulation, with the source and drain areas of the layout.", ""]
    out += ["## What the verdicts rest on", "",
            f"- Constants: {P['note']}. `d0` = {fm(cal.get('d0'), '.6f')}, `kappa` = {fm(cal.get('kappa'), '.6f')}, "
            f"`mu` = {fm(cal.get('mu'), '+.6f')}, `h_mu` = {fm(cal.get('h_mu'), '.6f')}; "
            f"in the campaign {ref['calibration']['d0']:.6f}, {ref['calibration']['kappa']:.6f}, {ref['calibration']['mu']:+.6f}, {ref['calibration']['h_mu']:.6f}.",
            f"- Evaluable cells: {len(X['cells'])} of 8 ({', '.join(X['cells'])}); evaluable ports: {len(X['ports'])}.",
            "- L11 can fail on one port and cannot establish a rate: with no contradiction among n certified ports the 95% upper "
            "bound on the rate is 1 − 0.05^(1/n) (53% for 4, 31% for 8, 17% for 16).", ""]
    out += ["## Ports", "",
            "Schematic: the committed values of the same cell and port. Post-layout: this stage, constants of this stage.", "",
            "| Cell | Port | Static level, move | Gap, schematic | Gap, post-layout | Need, schematic | Need, post-layout | Count | Status 3, schematic | Status 3, post-layout | Room at status 3 | Rule A1 |",
            "|---|---|---|---|---|---|---|---|---|---|---|---|"]
    lev = dict(X["levels"])
    for c in CELLS:
        for q in (1, 2):
            p, o, a, s = P["predictions"].get((c, q), {}), P["ports"].get((c, q), {}), P["amended"].get((c, q), {}), ref["predictions"][(c, q)]
            r1 = P["a1"].get((c, q), {})
            a1 = "eligible" + (", contradicted" if r1.get("contradicted") else "") if r1.get("eligible") else ("not eligible: " + r1.get("reasons", "") if r1 else "—")
            out.append(f"| `{c}` | {q} | {fm(lev.get(c))} | {fm(s['gap'])} | {fm(p.get('gap'))} | {s['m']} | {p.get('m', '') or '—'} | "
                       f"{o.get('count', '') or '—'} | {ref['amended'][(c, q)]['status3']} | {a.get('status3', '') or '—'} | {fm(a.get('room3'))} | {a1} |")
    out += ["", "## The same with the constants of the campaign", "",
            "Declared second analysis (decision D6). It decides no prediction.", "",
            "| | Measured | Would be |", "|---|---|---|"]
    out += [f"| {k} | {m} | {s} |" for k, t, s, m in VF if k in ("L8", "L9", "L10", "L11", "L12")]
    out += ["", "## Nominal cell: primary list and secondary list", "",
            "The secondary list keeps the plate term: an upper bound ([`../AMENDMENT_3.md`](../AMENDMENT_3.md)). "
            "It decides no prediction.", "",
            "| Reading | Primary | Secondary, upper bound |", "|---|---|---|"]

    def line(text, fn):
        def cell(r, d):
            try:
                return fn(r, d)
            except (KeyError, TypeError, ValueError):
                return "no result"
        out.append(f"| {text} | {cell(R, data)} | {cell(S, sec)} |")
    line("Silent pulses before the first FIRE, port 1 and port 2 (27 °C)", lambda r, d: f"{r['counts'][0]} and {r['counts'][1]}")
    line("Stops with no silent pulse after its first FIRE", lambda r, d: "yes" if r["stops"] else "no")
    line("Silent steps (mV)", lambda r, d: f"{min(r['silent_steps']):.3f} to {max(r['silent_steps']):.3f}")
    line("Largest step of a firing pulse (mV)", lambda r, d: f"{max(abs(v) for v in r['firing_steps']):.3f}")
    line("Static level, move against the schematic", lambda r, d: f"{d.static_level('nom_ramp') - ref['static']['nominal']:+.5f}")
    line("Under 0.1 TΩ: silent pulses after the stop", lambda r, d: f"{r['refresh']}")
    line("125 °C: silent pulses before the first FIRE", lambda r, d: f"{r['counts125'][0]} and {r['counts125'][1]}")
    line("125 °C, no imposed leak: silent pulses after the stop", lambda r, d: f"{r['refresh125']}")
    line("Guard", lambda r, d: "; ".join(r["events"]) if r["events"] else "nothing")
    if X["shift"]:
        out += ["", f"Gap of the nominal cell, primary list: {X['shift'][1]:+.5f} and {X['shift'][2]:+.5f} against the schematic "
                    f"(ports 1 and 2). With the secondary list no calibration is made, so no gap is given."]
    out += ["", "## Supply current of the nominal cell", "", "Reported, not predicted. A nominal simulation at 27 °C; the references, "
            "bias sinks and clocks are ideal sources outside the cell.", ""]
    def supply(path, rows):
        if not Path(path).exists() or not rows:
            return None
        z = json.loads(Path(path).read_text())["mean_A"]
        mean = lambda v: sum(v) / len(v) if v else None
        return (z[0], mean([z[x["pulse"] + 1] for x in rows if not x["fired"]]), mean([z[x["pulse"] + 1] for x in rows if x["fired"]]))

    def figure(v, rest=None):
        if v is None:
            return "—"
        return (f"{v * 1e6:.2f} µA, {v * 1.8e6:.1f} µW, {v * 1.8 * 440e-6 * 1e9:.2f} nJ per period"
                + ("" if rest is None else f" ({(v - rest) * 1.8 * 440e-6 * 1e12:+.1f} pJ against rest)"))
    post = supply(data.path("nom_cell", "supply.json"), data.rows("nom_cell"))
    sch = supply(REF / "nom_cell.supply.json", data.analyze.read_run(CIRCUIT / "results" / "nom.csv")[0])
    if post is None:
        out.append("No result.")
    else:
        out += ["Mean current delivered by the 1.8 V source, power, and energy over one period of 440 µs.", "",
                "| | Schematic | Post-layout, primary list |", "|---|---|---|"]
        for k, text in enumerate(("At rest", "Period with a silent pulse", "Period with a firing pulse")):
            out.append(f"| {text} | {figure(sch[k], sch[0] if k else None) if sch else '—'} | {figure(post[k], post[0] if k else None)} |")
    out += ["", "## Runs", "", "| Run | Analysis | Result | Wall time |", "|---|---|---|---|"]
    for m, q in p_plan.queues().items():
        for r in q:
            n = r["name"]
            meta = json.loads((data.folder / f"{n}.json").read_text()) if (data.folder / f"{n}.json").exists() else {}
            wall = f"{meta['finished_unix'] - meta['started_unix']:.0f} s" if "finished_unix" in meta else "—"
            d = data
            out.append(f"| `{n}` (machine {m}) | {r['analysis']} | {'result' if d.ok(n) else d.why(n)} | {wall} |")
    for tag, Z in (("this stage", P), ("the campaign", F)):
        bad = [f"{k}: status {v[0]}" for k, v in Z["log"].items() if v[0] != 0]
        if bad:
            out += ["", f"Scripts of the campaigns that ended with an error, constants of {tag}: " + "; ".join(bad) + "."]
    (out_path or HERE / "P_REPORT.md").write_text("\n".join(out) + "\n")
    for k, t, s, m in V:
        print(k, s, "|", m)
    return V


if __name__ == "__main__":
    if sys.argv[1:] == ["report"]:
        report()
    else:
        sys.exit(__doc__)
