"""Verdict on every check and prediction of PREDICTION.md, and the figures.

Reads results/*.csv. Writes results/summary.json, VERDICTS.md and figures/*.png.

The guard reports two kinds of event on the protection latch (DESIGN.md):
  not a FIRE            : at the pulse edge or before it, or in the period at rest.
                          The run is listed and left out of the statistics.
  against the mechanism : after the end of the pulse, twice in a period, or without an end.
                          The run is listed and stays in the statistics.
The titles of the figures say what is plotted. Counts in them are computed from the results.
"""
import csv, glob, json, os
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

DOSE = 1.3465          # mV, the step of the nominal cell (PREDICTION.md)
RES = "results"
ANOMALIES, AGAINST, FAILED = [], [], sorted(os.path.basename(p)[:-7] for p in glob.glob(RES + "/*.failed"))
REST_FIRE = sorted(os.path.basename(p)[:-9] for p in glob.glob(RES + "/*.restfire"))


def not_a_fire(x):
    """A protection that cannot be a FIRE. Reported, never used as a measure."""
    if x["fired"] == "1" and float(x["fire_latency"]) < 0.05:
        return "protection raised at the pulse edge or before it"
    return None


def against(x):
    """A protection that counts against the mechanism. Reported, and kept as a measure."""
    if x["fired"] != "1" or not_a_fire(x):
        return None
    if float(x["fire_latency"]) > 1.02:
        return "FIRE after the end of the pulse"
    if float(x["reopen"]) < 0:
        return "protection without an end"
    if x["second_rise"] == "1":
        return "protection raised twice in one period"
    return None


RAW = {}        # every run that produced a result, whatever the guard says of it


def load(name):
    path = f"{RES}/{name}.csv"
    if not os.path.exists(path):
        return None
    rows = list(csv.DictReader(open(path)))
    RAW[name] = rows
    late = sorted({against(x) for x in rows if against(x)})
    if late:
        AGAINST.append(dict(run=name, pulses=[x["pulse"] for x in rows if against(x)], kind=late))
    bad = sorted({not_a_fire(x) for x in rows if not_a_fire(x)})
    if name in REST_FIRE:
        bad.append("protection raised in the period at rest")
    if bad:
        ANOMALIES.append(dict(run=name, pulses=[x["pulse"] for x in rows if not_a_fire(x)], kind=bad))
        return None
    return rows


def names(prefix):
    return sorted(os.path.basename(p)[:-4] for p in glob.glob(f"{RES}/{prefix}*.csv"))


def port(rows, q):
    """One port during its own training pulses."""
    r = [x for x in rows if x["port"] == str(q)]
    fired = [x["fired"] == "1" for x in r]
    step = [float(x[f"step{q}_mV"]) for x in r]
    first = fired.index(True) if True in fired else None
    after = fired[first:] if first is not None else []
    return dict(n=len(r), stopped=first is not None, silent=first if first is not None else len(r),
                relapses=[first + i for i, f in enumerate(after) if not f] if first is not None else [],
                silent_steps=[s for s, f in zip(step[:first], fired[:first])] if first is not None else step,
                relapse_steps=[s for s, f in zip(step[first:], after) if not f] if first is not None else [],
                firing_steps=[s for s, f in zip(step, fired) if f],
                first_fire=float(r[first]["fire_latency"]) if first is not None else None,
                steered_on_fire=sum(int(x[f"steered{q}"]) for x, f in zip(r, fired) if f))


def cell(name):
    rows = load(name)
    if rows is None:
        return None
    j = rows[-1]
    idle = [float(x["step1_mV"]) for x in rows if x["port"] == "2"] + [float(x["step2_mV"]) for x in rows if x["port"] == "1"]
    return dict(name=name, p=[port(rows, 1), port(rows, 2)], idle=idle,
                joint=float(j["fire_latency"]) if j["fired"] == "1" else None,
                joint_steered=int(j["steered1"]) + int(j["steered2"]), rows=rows)


def refresh(name):
    rows = load(name)
    if rows is None:
        return None
    fired = [x["fired"] == "1" for x in rows]
    v = np.array([float(x["vmem1"]) for x in rows]) * 1e3
    step = [float(x["step1_mV"]) for x in rows]
    if True not in fired:
        return dict(name=name, stop=None, fired=fired, v=v)
    stop = fired.index(True)
    rel = [k for k in range(stop, len(rows)) if not fired[k]]
    return dict(name=name, stop=stop, fired=fired, v=v, relapses=rel, gaps=[b - a for a, b in zip(rel, rel[1:])],
                doubles=sum(1 for a, b in zip(rel, rel[1:]) if b == a + 1), relapse_steps=[step[k] for k in rel],
                band=float((v[stop:].max() - v[stop:].min()) / DOSE),
                steered_on_fire=sum(int(x["steered1"]) for x, f in zip(rows, fired) if f))


def pairs_within(x, tol=0.05):
    x = np.sort(np.asarray(x)); j = ok = 0
    for i in range(len(x)):
        while x[i] - x[j] >= tol:
            j += 1
        ok += i - j
    return ok, len(x) * (len(x) - 1) // 2


V = []          # verdicts: (id, statement, measured, holds)


def verdict(pid, statement, measured, holds):
    V.append((pid, statement, measured, None if holds is None else bool(holds)))


out = {}

# ---- checks on the nominal cell
nom = cell("nom")
if nom:
    r = nom["rows"]
    pat = "".join("F" if x["fired"] == "1" else "s" for x in r)
    sil = nom["p"][0]["silent_steps"] + nom["p"][1]["silent_steps"]
    fir = nom["p"][0]["firing_steps"] + nom["p"][1]["firing_steps"]
    ent = [float(x["entry1"]) for x in r if x["port"] == "1"]; ext = [float(x["exit1"]) for x in r if x["port"] == "1"]
    reo = [float(x["reopen"]) for x in r if x["port"] == "1" and x["fired"] == "1"]
    out["nominal"] = dict(pattern=pat, silent_steps_mV=sil, firing_step_max_mV=max(abs(s) for s in fir), entry=[min(ent), max(ent)],
                          exit=[min(ext), max(ext)], reopen=[min(reo), max(reo)], joint=nom["joint"],
                          first_fire=[nom["p"][0]["first_fire"], nom["p"][1]["first_fire"]])
    verdict("C1", "pattern ssssFFFFFF on both ports, FIRE on the joint pulse", pat[:10] + " " + pat[10:20] + " " + pat[20], pat == "ssssFFFFFF" * 2 + "F")
    verdict("C2", "silent steps between 1.345 and 1.348 mV", f"{min(sil):.3f} to {max(sil):.3f} mV", 1.345 <= min(sil) and max(sil) <= 1.348)
    verdict("C3", "firing steps below 0.002 mV", f"largest {max(abs(s) for s in fir):.3f} mV", max(abs(s) for s in fir) < 0.002)
    verdict("C4", "write window 1.777 to 2.040, protection ends at 5.59", f"{np.mean(ent):.3f} to {np.mean(ext):.3f}, end {np.mean(reo):.2f}",
            abs(np.mean(ent) - 1.777) < 0.002 and abs(np.mean(ext) - 2.040) < 0.002 and abs(np.mean(reo) - 5.59) < 0.01)
    verdict("C5", "joint read between 0.2665 and 0.2685", f"{nom['joint']:.4f}", nom["joint"] is not None and 0.2665 <= nom["joint"] <= 0.2685)

# ---- noise on the nominal cell
nz = [c for c in (cell(n) for n in names("nz_")) if c]
if nz:
    sil_n = np.array([[c["p"][0]["silent"], c["p"][1]["silent"]] for c in nz])
    joint = np.array([c["joint"] for c in nz if c["joint"] is not None])
    idle = np.concatenate([c["idle"] for c in nz])
    ss = np.concatenate([c["p"][q]["silent_steps"] for c in nz for q in (0, 1)])
    fs = np.concatenate([c["p"][q]["firing_steps"] for c in nz for q in (0, 1)])
    four = int(((sil_n[:, 0] == 4) & (sil_n[:, 1] == 4)).sum())
    s_idle, s_sil = idle.std(ddof=1), ss.std(ddof=1)
    write = float(np.sqrt(max(s_sil ** 2 - s_idle ** 2, 0.0)))
    out["noise"] = dict(runs=len(nz), four_silent=four, silent_min=int(sil_n.min()), silent_max=int(sil_n.max()), joint_fired=len(joint),
                        joint_mean=float(joint.mean()), joint_sigma=float(joint.std(ddof=1)), joint_min=float(joint.min()), joint_max=float(joint.max()),
                        idle_sigma_mV=float(s_idle), silent_sigma_mV=float(s_sil), silent_mean_mV=float(ss.mean()), write_sigma_mV=write,
                        firing_mean_mV=float(fs.mean()), firing_sigma_mV=float(fs.std(ddof=1)), firing_max_mV=float(np.abs(fs).max()),
                        relapses=int(sum(len(c["p"][q]["relapses"]) for c in nz for q in (0, 1))))
    verdict("P1", "4 silent pulses on both ports in at least 18 of 20 runs, never fewer than 3 or more than 5",
            f"{four} of {len(nz)} runs, range {sil_n.min()} to {sil_n.max()}", len(nz) == 20 and four >= 18 and sil_n.min() >= 3 and sil_n.max() <= 5)
    verdict("P2", "sigma of the joint read below 0.0012, every read between 0.264 and 0.271",
            f"sigma {joint.std(ddof=1):.4f}, {joint.min():.4f} to {joint.max():.4f}", len(joint) == len(nz) and joint.std(ddof=1) < 0.0012 and joint.min() >= 0.264 and joint.max() <= 0.271)
    verdict("P3", "a port at rest changes over a period with a sigma between 0.05 and 0.10 mV", f"{s_idle:.3f} mV", 0.05 <= s_idle <= 0.10)
    verdict("P4", "sigma of a silent step, read noise removed, below 0.067 mV", f"{write:.3f} mV (silent step {s_sil:.3f} mV)", write < 0.067)
    verdict("P5", "firing steps: mean within 0.01 mV of zero, sigma within 25% of the sigma at rest",
            f"mean {fs.mean():+.4f} mV, sigma {fs.std(ddof=1):.3f} mV ({fs.std(ddof=1) / s_idle:.2f} of rest)", abs(fs.mean()) < 0.01 and 0.75 <= fs.std(ddof=1) / s_idle <= 1.25)

# ---- mismatch and noise
mc = [c for c in (cell(n) for n in names("mc_")) if c]
if mc:
    ports = [c["p"][q] for c in mc for q in (0, 1)]
    stopped = sum(p["stopped"] for p in ports)
    sil_n = np.array([p["silent"] for p in ports])
    joint = np.array([c["joint"] for c in mc if c["joint"] is not None])
    ok, tot = pairs_within(joint)
    rel = [p for p in ports if p["relapses"]]
    calm = [p for p in ports if p["stopped"] and not p["relapses"]]
    rel_steps = np.array([s for p in rel for s in p["relapse_steps"]])
    idle = np.concatenate([c["idle"] for c in mc])
    total = np.array([sum(p["firing_steps"]) for p in calm])
    late = [p["first_fire"] for p in rel]
    out["mismatch_noise"] = dict(cells=len(mc), ports=len(ports), ports_stopped=int(stopped), silent_min=int(sil_n.min()), silent_max=int(sil_n.max()),
                                 silent_counts={int(k): int((sil_n == k).sum()) for k in np.unique(sil_n)},
                                 joint_fired=len(joint), joint_mean=float(joint.mean()), joint_sigma=float(joint.std(ddof=1)), joint_min=float(joint.min()),
                                 joint_max=float(joint.max()), pairs_within_005=[int(ok), int(tot)],
                                 ports_with_relapse=len(rel), ports_with_two_relapses=sum(len(p["relapses"]) > 1 for p in rel),
                                 first_fire_of_relapsing_ports=[min(late), max(late)] if late else None,
                                 first_fire_of_other_ports=[min(p["first_fire"] for p in calm), max(p["first_fire"] for p in calm)],
                                 other_ports_with_first_fire_after_095=sum(p["first_fire"] > 0.95 for p in calm),
                                 relapse_steps_mV=[float(rel_steps.min()), float(rel_steps.max())] if len(rel_steps) else None,
                                 idle_sigma_mV=float(idle.std(ddof=1)), total_firing_mean_mV=float(total.mean()), total_firing_sigma_mV=float(total.std(ddof=1)),
                                 firing_pulses_per_port=float(np.mean([len(p["firing_steps"]) for p in calm])),
                                 silent_step_mean_mV=float(np.mean([s for p in ports for s in p["silent_steps"]])),
                                 silent_step_sigma_mV=float(np.std([s for p in ports for s in p["silent_steps"]], ddof=1)))
    verdict("P6", "both ports of every cell stop within 10 pulses, after 2 to 8 silent pulses",
            f"{stopped} of {len(ports)} ports stop, {sil_n.min()} to {sil_n.max()} silent pulses", len(mc) == 100 and stopped == len(ports) and sil_n.min() >= 2 and sil_n.max() <= 8)
    verdict("P7", "every cell fires on the joint pulse; sigma 0.0025 to 0.0042; reads between 0.250 and 0.280; every pair within 0.05",
            f"{len(joint)} of {len(mc)} fire, sigma {joint.std(ddof=1):.4f}, {joint.min():.4f} to {joint.max():.4f}, {ok} of {tot} pairs",
            len(joint) == len(mc) and 0.0025 <= joint.std(ddof=1) <= 0.0042 and joint.min() >= 0.250 and joint.max() <= 0.280 and ok == tot)
    frac = 100.0 * len(rel) / len(ports)
    verdict("P8", "a port relapses only if its first FIRE came after 0.95; 4% to 14% of ports relapse; none twice; each relapse within 20% of a dose",
            f"{len(rel)} of {len(ports)} ports ({frac:.1f}%), first FIRE of these {min(late):.3f} to {max(late):.3f}, "
            f"{sum(len(p['relapses']) > 1 for p in rel)} relapse twice, steps {rel_steps.min():.3f} to {rel_steps.max():.3f} mV" if rel else "no port relapses",
            bool(rel) and min(late) > 0.95 and 4 <= frac <= 14 and all(len(p["relapses"]) == 1 for p in rel) and np.all(np.abs(rel_steps / DOSE - 1) <= 0.20))
    verdict("P9", "ports without relapse: total change over the firing pulses has mean within 0.03 mV of zero and sigma below 1.5 times the sigma at rest",
            f"mean {total.mean():+.4f} mV, sigma {total.std(ddof=1):.3f} mV ({total.std(ddof=1) / idle.std(ddof=1):.2f} of rest)",
            abs(total.mean()) < 0.03 and total.std(ddof=1) < 1.5 * idle.std(ddof=1))

# ---- after the stop
nl = cell("nom_long")
if nl:
    tot = [sum(p["firing_steps"]) for p in nl["p"]]
    out["nominal_long"] = dict(firing_pulses=[len(p["firing_steps"]) for p in nl["p"]], total_mV=tot, relapses=[len(p["relapses"]) for p in nl["p"]])
    verdict("P11", "over 22 firing pulses the stored voltage moves by less than 0.01 mV",
            f"{tot[0]:+.4f} mV and {tot[1]:+.4f} mV over {len(nl['p'][0]['firing_steps'])} firing pulses",
            len(nl["p"][0]["firing_steps"]) == 22 and max(abs(t) for t in tot) < 0.01)

# ---- corners
want = dict(pvt_ss_27=4, pvt_ff_27=4, pvt_sf_27=4, pvt_fs_27=4, pvt_tt_m40=2, pvt_tt_125=7)
pv = {n: cell(n) for n in want}
if all(pv.values()):
    out["corners"] = {n[4:]: dict(silent=[c["p"][0]["silent"], c["p"][1]["silent"]], joint=c["joint"],
                                  silent_step_mV=float(np.mean(c["p"][0]["silent_steps"]))) for n, c in pv.items()}
    good = all(c["p"][0]["stopped"] and c["p"][1]["stopped"] and c["p"][0]["silent"] == want[n] and c["p"][1]["silent"] == want[n]
               and c["joint"] is not None and 0.262 <= c["joint"] <= 0.272 for n, c in pv.items())
    verdict("P12", "the six corner runs stop after 4, 4, 4, 4, 2 and 7 silent pulses; joint read between 0.262 and 0.272",
            "; ".join(f"{n[4:]}: {c['p'][0]['silent']}/{c['p'][1]['silent']}, {c['joint']:.4f}" if c["joint"] is not None else f"{n[4:]}: no joint FIRE" for n, c in pv.items()), good)

# ---- refresh
rf = {n[8:]: refresh(n) for n in names("refresh_")}
rf = {k: v for k, v in rf.items() if v}
def brief(r):
    return {k: (v if not isinstance(v, np.ndarray) else None) for k, v in r.items() if k not in ("v", "fired")}
out["refresh"] = {k: brief(v) for k, v in rf.items()}
if "none" in rf:
    r = rf["none"]
    verdict("P13", "no leak, no noise: no relapse, stored voltage within 0.05 dose after the stop", f"{len(r['relapses'])} relapses, band {r['band']:.3f} dose",
            not r["relapses"] and r["band"] < 0.05)
if "none_nz" in rf:
    r = rf["none_nz"]
    verdict("P14", "no leak, with noise: at most one relapse", f"{len(r['relapses'])} relapses, band {r['band']:.2f} dose", len(r["relapses"]) <= 1)
if "lk11" in rf:
    r = rf["lk11"]
    verdict("P15", "0.1 TΩ: a relapse every 22 or 23 periods, never two silent pulses in a row, relapse steps 1.27 to 1.31 mV, band within 1.05 dose",
            f"{len(r['relapses'])} relapses, distances {sorted(set(r['gaps']))}, steps {min(r['relapse_steps']):.3f} to {max(r['relapse_steps']):.3f} mV, band {r['band']:.2f} dose",
            len(r["gaps"]) > 0 and set(r["gaps"]) <= {22, 23} and r["doubles"] == 0 and 1.27 <= min(r["relapse_steps"]) and max(r["relapse_steps"]) <= 1.31 and r["band"] <= 1.05)
if "lk12" in rf:
    r = rf["lk12"]
    verdict("P16", "1 TΩ: first relapse between pulses 85 and 100, relapses 220 to 224 periods apart",
            f"relapses at {r['relapses']}, distances {r['gaps']}", len(r["relapses"]) >= 2 and 85 <= r["relapses"][0] <= 100 and all(220 <= g <= 224 for g in r["gaps"]))
if "lk11_nz" in rf:
    r = rf["lk11_nz"]
    verdict("P17", "0.1 TΩ with noise: relapses 17 to 28 periods apart, never two silent pulses in a row, band within 1.6 dose",
            f"{len(r['relapses'])} relapses, distances {r['gaps']}, band {r['band']:.2f} dose",
            len(r["gaps"]) > 0 and all(17 <= g <= 28 for g in r["gaps"]) and r["doubles"] == 0 and r["band"] < 1.6)
mm = [rf[k] for k in sorted(rf) if k.startswith("mm_")]
if mm:
    rowsmm, good = [], len(mm) == 8
    for r in mm:
        if r["stop"] is None or len(r["relapses"]) < 2:
            rowsmm.append(f"{r['name'][11:]}: " + ("never fires" if r["stop"] is None else f"{len(r['relapses'])} relapse")); good = False; continue
        mg = float(np.mean(r["gaps"]))
        rowsmm.append(f"{r['name'][11:]}: {mg:.1f}, {r['doubles']} double, {r['band']:.2f}")
        good = good and 17 <= mg <= 29 and r["doubles"] <= 1 and r["band"] < 1.8
    verdict("P18", "8 cells with mismatch and noise under 0.1 TΩ: mean distance between relapses 17 to 29, two silent pulses in a row at most once, band within 1.8 dose",
            "cell: mean distance, doubles, band in doses. " + "; ".join(rowsmm), good)

# ---- the gate, over every run
# Every run that produced a result is used here, also a run that the guard left out of the statistics.
for n in names(""):
    if n not in RAW:
        load(n)
fired_rows = [x for rows in RAW.values() for x in rows if x["fired"] == "1"]
fires = len(fired_rows)
steer = sum(1 for x in fired_rows if x["steered1"] == "1" or x["steered2"] == "1")
latest = max(float(x["fire_latency"]) for x in fired_rows) if fired_rows else None
verdict("P10", "no firing pulse steers the sensor current to the integrator, in any run", f"{steer} of {fires} firing pulses in {len(RAW)} runs", bool(fires) and steer == 0)
done = len(glob.glob(RES + "/*.csv"))
verdict("P19", "no run fails and the guard reports nothing",
        f"{done} runs complete, {len(FAILED)} failed, {len(ANOMALIES)} with a protection that is not a FIRE, {len(AGAINST)} with an event against the mechanism",
        done == 146 and not FAILED and not ANOMALIES and not AGAINST)
out["runs_complete"], out["failed"], out["not_a_fire"], out["against_the_mechanism"] = done, FAILED, ANOMALIES, AGAINST
out["firing_pulses_checked_for_steering"], out["latest_fire_latency"] = fires, latest

V.sort(key=lambda v: (v[0][0], int(v[0][1:])))
json.dump(dict(summary=out, verdicts=[dict(id=a, statement=b, measured=c, holds=d) for a, b, c, d in V]), open(RES + "/summary.json", "w"), indent=1)
with open("VERDICTS.md", "w") as fh:
    fh.write("# Verdicts\n\nWritten by `analyze.py` from `results/`. The statements are those of `PREDICTION.md`.\n\n| | Statement | Measured | Verdict |\n|---|---|---|---|\n")
    for a, b, c, d in V:
        fh.write(f"| {a} | {b} | {c} | {'holds' if d else 'fails'} |\n")
    fh.write(f"\n{sum(1 for v in V if v[3])} of {len(V)} hold.\n\n## Guard\n\n")
    fh.write(f"- Runs that the simulator aborted: {', '.join(FAILED) if FAILED else 'none'}.\n")
    fh.write("- Runs with a protection that is not a FIRE, left out of the statistics: "
             + ("; ".join(f"{a['run']} ({', '.join(a['kind'])}; pulses {', '.join(a['pulses'])})" for a in ANOMALIES) if ANOMALIES else "none") + ".\n")
    fh.write("- Runs with an event against the mechanism, kept in the statistics: "
             + ("; ".join(f"{a['run']} ({', '.join(a['kind'])}; pulses {', '.join(a['pulses'])})" for a in AGAINST) if AGAINST else "none") + ".\n")
    if latest is not None:
        fh.write(f"- Latest FIRE of the campaign: {latest:.4f} units after the start of its pulse. The pulse ends at 1.\n")
for a, b, c, d in V:
    print(f"{a:4s} {'holds' if d else 'FAILS':6s} {c}")
print("failed:", FAILED, "not a FIRE:", ANOMALIES, "against the mechanism:", AGAINST)
print("latest FIRE of the campaign:", latest)

# ---- figures
BLUE, ORANGE, INK, MUTED, GRID, SURF = "#2a78d6", "#eb6834", "#0b0b0b", "#52514e", "#e4e3df", "#fcfcfb"
plt.rcParams.update({"figure.facecolor": SURF, "axes.facecolor": SURF, "savefig.facecolor": SURF, "axes.edgecolor": GRID, "axes.labelcolor": MUTED,
                     "xtick.color": MUTED, "ytick.color": MUTED, "text.color": INK, "axes.titlesize": 10.5, "axes.titleweight": "bold",
                     "axes.titlelocation": "left", "axes.spines.top": False, "axes.spines.right": False, "axes.grid": True, "grid.color": GRID,
                     "grid.linewidth": 0.6, "axes.axisbelow": True, "font.size": 9.5, "legend.frameon": False, "lines.linewidth": 2.0})
os.makedirs("figures", exist_ok=True)

def save(fig, name):
    fig.tight_layout(); fig.savefig(f"figures/{name}.png", dpi=170); plt.close(fig)

if nom:
    r = nom["rows"]; k = np.arange(1, len(r) + 1)
    v1 = np.array([float(x["vmem1"]) for x in r]) * 1e3; v2 = np.array([float(x["vmem2"]) for x in r]) * 1e3
    fired = np.array([x["fired"] == "1" for x in r])
    fig, ax = plt.subplots(figsize=(7.4, 3.5))
    ax.step(k, v1, where="mid", color=BLUE, label="port 1"); ax.step(k, v2, where="mid", color=ORANGE, label="port 2")
    lo = min(v1.min(), v2.min()) - 0.9
    ax.scatter(k[fired], np.full(fired.sum(), lo), marker="|", s=90, color=INK, linewidths=1.6)
    ax.annotate("FIRE", (k[fired][0], lo), xytext=(-30, -3), textcoords="offset points", color=MUTED, fontsize=8.5)
    ax.axvspan(0.5, 10.5, color=BLUE, alpha=0.05, lw=0); ax.axvspan(10.5, 20.5, color=ORANGE, alpha=0.05, lw=0)
    ax.text(5.5, v1.max() + 0.25, "pulses on port 1", ha="center", color=MUTED, fontsize=8.5); ax.text(15.5, v1.max() + 0.25, "pulses on port 2", ha="center", color=MUTED, fontsize=8.5)
    ax.text(21, v1.max() + 0.25, "both", ha="center", color=MUTED, fontsize=8.5)
    ax.set_xlabel("pulse"); ax.set_ylabel("stored voltage (mV)"); ax.set_xticks(range(1, 22, 2)); ax.set_ylim(lo - 0.7, v1.max() + 0.9)
    ax.set_title(f"Nominal cell, no noise: stored voltage after each pulse (s silent, F fire: {pat[:10]} {pat[10:20]} {pat[20:]})")
    ax.legend(loc="center right")
    save(fig, "fig1_nominal")

if mc:
    fig, ax = plt.subplots(1, 2, figsize=(9.6, 3.5))
    cnt = out["mismatch_noise"]["silent_counts"]; ks = sorted(cnt)
    ax[0].bar(ks, [cnt[c] for c in ks], width=0.72, color=BLUE)
    for c in ks:
        ax[0].text(c, cnt[c] + 1.2, str(cnt[c]), ha="center", color=MUTED, fontsize=8.5)
    ax[0].set_xlabel("silent pulses before the first FIRE"); ax[0].set_ylabel("ports"); ax[0].set_xticks(ks); ax[0].grid(axis="x", visible=False)
    ax[0].set_title(f"Silent pulses before the first FIRE ({stopped} of {len(ports)} ports fire)")
    ax[1].hist(joint, bins=np.arange(joint.min() - 0.00025, joint.max() + 0.00075, 0.001), color=BLUE, rwidth=0.86)
    ax[1].axvspan(0.239, 0.256, color=MUTED, alpha=0.13, lw=0)       # stopped_pair_read_latency: (239/1000, 32/125]
    inside = int(((joint > 0.239) & (joint <= 0.256)).sum())
    ax[1].text(0.2475, ax[1].get_ylim()[1] * 0.8, "window proved\nfor the ideal model", ha="center", color=MUTED, fontsize=8.5)
    ax[1].set_xlim(0.238, max(0.282, joint.max() + 0.003)); ax[1].set_xlabel("joint read latency (time units)"); ax[1].set_ylabel("cells")
    ax[1].set_title(f"Joint read of {len(joint)} of {len(mc)} cells: sigma {joint.std(ddof=1):.4f}, {inside} inside the window")
    save(fig, "fig2_cells")

    ss_all = np.array([s for p in ports for s in p["silent_steps"]] + [s for p in ports for s in p["relapse_steps"]])
    fs_all = np.array([s for p in ports for s in p["firing_steps"]])
    fig, ax = plt.subplots(figsize=(7.4, 3.5))
    bins = np.arange(-0.4, 1.8, 0.04)
    ax.hist(idle, bins=bins, histtype="step", color=MUTED, linewidth=1.4, label=f"port at rest ({len(idle)})")
    ax.hist(fs_all, bins=bins, histtype="step", color=BLUE, linewidth=2.0, label=f"firing pulse ({len(fs_all)})")
    ax.hist(ss_all, bins=bins, histtype="step", color=ORANGE, linewidth=2.0, label=f"silent pulse ({len(ss_all)})")
    ax.axvline(DOSE, color=GRID, linewidth=1.0); ax.text(DOSE, ax.get_ylim()[1] * 0.93, " one dose", color=MUTED, fontsize=8.5)
    ax.set_xlabel("change of the stored voltage over one period (mV)"); ax.set_ylabel("pulses")
    ax.set_title(f"Change of the stored voltage over one period, {len(mc)} cells with mismatch and noise")
    ax.legend(loc="upper center")
    save(fig, "fig3_steps")

    fig, ax = plt.subplots(figsize=(7.4, 3.2))
    ff_all = [p["first_fire"] for p in calm] + late
    bins = np.arange(min(0.78, min(ff_all) - 0.01), max(1.0101, max(ff_all) + 0.0101), 0.01)
    ax.hist([p["first_fire"] for p in calm], bins=bins, color=BLUE, rwidth=0.86, label=f"no relapse ({len(calm)} ports)")
    ax.hist(late, bins=bins, color=ORANGE, rwidth=0.86, label=f"a silent pulse later ({len(rel)} ports)")
    ax.axvline(1.0, color=GRID, linewidth=1.0); ax.text(0.999, ax.get_ylim()[1] * 0.9, "end of the pulse ", ha="right", color=MUTED, fontsize=8.5)
    ax.set_xlabel("latency of the first FIRE of a port (time units)"); ax.set_ylabel("ports")
    ax.set_title("Latency of the first FIRE of a port, and whether a silent pulse follows")
    ax.legend(loc="upper left")
    save(fig, "fig4_late_stop")

panels = [(k, t) for k, t in (("none_nz", "no leak, with noise"), ("lk11", "leak through 0.1 TΩ, no noise"), ("lk11_nz", "leak through 0.1 TΩ, with noise"),
                              ("lk12", "leak through 1 TΩ, no noise")) if k in rf and rf[k]["stop"] is not None]
if panels:
    fig, ax = plt.subplots(len(panels), 1, figsize=(7.8, 1.9 * len(panels) + 0.5), squeeze=False)
    for a, (kk, title) in zip(ax[:, 0], panels):
        r = rf[kk]; x = np.arange(1, len(r["v"]) + 1)
        a.plot(x, r["v"], color=BLUE, linewidth=1.3)
        s = [i for i in range(len(r["v"])) if not r["fired"][i]]
        a.scatter(x[s], r["v"][s], color=ORANGE, s=22, zorder=3, edgecolors=SURF, linewidths=0.8)
        a.set_ylabel("stored (mV)"); a.set_title(title, fontsize=9.5, fontweight="normal", color=MUTED)
    ax[0, 0].scatter([], [], color=ORANGE, s=22, label="silent pulse"); ax[0, 0].plot([], [], color=BLUE, linewidth=1.3, label="stored voltage after each pulse")
    ax[0, 0].legend(loc="upper right", ncol=2, fontsize=8.5)
    ax[-1, 0].set_xlabel("pulse")
    fig.suptitle("Stored voltage of one port under continued pulses", x=0.01, ha="left", fontsize=10.5, fontweight="bold")
    save(fig, "fig5_refresh")

if mm:
    fig, ax = plt.subplots(2, 4, figsize=(10.4, 4.2), sharex=True)
    for a, r in zip(ax.ravel(), mm):
        x = np.arange(1, len(r["v"]) + 1)
        a.plot(x, r["v"] - r["v"][-1], color=BLUE, linewidth=1.2)
        if r["stop"] is not None:
            s = [i for i in range(len(r["v"])) if not r["fired"][i]]
            a.scatter(x[s], (r["v"] - r["v"][-1])[s], color=ORANGE, s=16, zorder=3, edgecolors=SURF, linewidths=0.6)
        a.set_title("cell " + r["name"][11:], fontsize=9, fontweight="normal", color=MUTED)
    for a in ax[:, 0]: a.set_ylabel("stored, from its end (mV)")
    for a in ax[-1, :]: a.set_xlabel("pulse")
    fig.suptitle("Eight cells with mismatch and noise under a leak of 0.1 TΩ (orange: silent pulse)", x=0.01, ha="left", fontsize=10.5, fontweight="bold")
    save(fig, "fig6_refresh_cells")
