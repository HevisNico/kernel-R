"""Verdict on every check and prediction of PREDICTION.md, and the figures.

  analyze.py [--results DIR] [--out DIR] [--no-figures]

Reads DIR/*.csv. Writes summary.json in the results folder, VERDICTS.md and figures/*.png in the
output folder. The list of runs is the one of campaign.py: no total is written here.

Each check has one of three statuses, with its reason:
  holds          the statement is true of the results
  fails          the statement is false of the results
  not evaluable  the results do not allow to tell (a run is missing, no FIRE to time, ...)

The report is always written, whatever the results are. A value that does not exist is shown as "—".

The guard reports two kinds of event on the protection latch (DESIGN.md):
  not a FIRE            : at the pulse edge or before it, or in the period at rest.
                          The run is listed and left out of the statistics.
  against the mechanism : after the end of the pulse, twice in a period, or without an end.
                          The run is listed and stays in the statistics.
The titles of the figures say what is plotted. Counts in them are computed from the results.
"""
import argparse, csv, glob, json, math, os, random, statistics, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from campaign import jobs          # the same list of runs as the launcher

DOSE = 1.3465                      # mV, the step of the nominal cell (PREDICTION.md)
HOLDS, FAILS, NA = "holds", "fails", "not evaluable"
DASH = "—"
COLS = ("pulse,port,fired,fire_latency,reopen,entry1,exit1,steered1,entry2,exit2,steered2,"
        "vmem1,vmem2,vq_min,second_rise,step1_mV,step2_mV").split(",")


# ---- numbers that may not exist
def fm(x, spec=".3f"):
    return DASH if x is None else format(x, spec)

def mean(x):
    return sum(x) / len(x) if x else None

def sd(x):
    return statistics.stdev(x) if len(x) >= 2 else None

def lo(x):
    return min(x) if x else None

def hi(x):
    return max(x) if x else None

def span(x, spec=".3f"):
    return f"{fm(lo(x), spec)} to {fm(hi(x), spec)}"


# ---- reading the runs
def read_run(path):
    """Rows of one run, or None and the reason."""
    try:
        with open(path, newline="") as fh:
            raw = list(csv.DictReader(fh))
    except OSError as e:
        return None, f"file not readable ({e.__class__.__name__})"
    if not raw:
        return None, "result without a row"
    absent = [c for c in COLS if c not in raw[0]]
    if absent:
        return None, "column absent: " + ", ".join(absent)
    rows = []
    for i, x in enumerate(raw):
        try:
            pos = lambda k: float(x[k]) if float(x[k]) >= 0 else None
            fired = x["fired"] == "1"
            rows.append(dict(pulse=int(x["pulse"]), port=int(x["port"]), fired=fired,
                             lat=float(x["fire_latency"]) if fired else None, reopen=pos("reopen") if fired else None,
                             entry=(None, pos("entry1"), pos("entry2")), exit=(None, pos("exit1"), pos("exit2")),
                             steered=(None, x["steered1"] == "1", x["steered2"] == "1"),
                             v=(None, float(x["vmem1"]), float(x["vmem2"])), vq_min=float(x["vq_min"]),
                             second=x["second_rise"] == "1", step=(None, float(x["step1_mV"]), float(x["step2_mV"]))))
        except (ValueError, TypeError, KeyError):
            return None, f"value not readable in row {i + 1}"
    return rows, None


def not_a_fire(x):
    """A protection that cannot be a FIRE. Reported, never used as a measure."""
    return "protection raised at the pulse edge or before it" if x["fired"] and x["lat"] < 0.05 else None


def against(x):
    """A protection that counts against the mechanism. Reported, and kept as a measure."""
    if not x["fired"] or not_a_fire(x):
        return None
    if x["lat"] > 1.02:
        return "FIRE after the end of the pulse"
    if x["reopen"] is None:
        return "protection without an end"
    if x["second"]:
        return "protection raised twice in one period"
    return None


class Campaign:
    """Every run of the plan, with its state."""

    def __init__(self, res, plan=None):
        self.res = res
        self.plan = list(plan) if plan is not None else [j[0] for j in jobs]
        self.state = {}        # run -> (state, reason); state is complete, missing, failed, left out or unreadable
        self.raw = {}          # rows of every run that produced a readable result
        self.rows = {}         # rows of the runs used in the statistics
        self.not_fire, self.against = [], []
        for name in self.plan:
            path = f"{res}/{name}.csv"
            if os.path.exists(f"{res}/{name}.failed"):
                self.state[name] = ("failed", "the simulator aborted the run or the run passed its time limit")
                continue
            if not os.path.exists(path):
                self.state[name] = ("missing", "run missing")
                continue
            rows, why = read_run(path)
            if rows is None:
                self.state[name] = ("unreadable", why)
                continue
            self.raw[name] = rows
            late = sorted({against(x) for x in rows if against(x)})
            if late:
                self.against.append(dict(run=name, pulses=[x["pulse"] for x in rows if against(x)], kind=late))
            bad = sorted({not_a_fire(x) for x in rows if not_a_fire(x)})
            if os.path.exists(f"{res}/{name}.restfire"):
                bad.append("protection raised in the period at rest")
            if bad:
                self.not_fire.append(dict(run=name, pulses=[x["pulse"] for x in rows if not_a_fire(x)], kind=bad))
                self.state[name] = ("left out", "; ".join(bad))
                continue
            self.rows[name] = rows
            self.state[name] = ("complete", "")
        self.extra = sorted(set(os.path.basename(p)[:-4] for p in glob.glob(res + "/*.csv")) - set(self.plan) - {"summary"})

    def series(self, prefix):
        return [n for n in self.plan if n.startswith(prefix)]

    def unusable(self, names):
        """Reason if some of these runs cannot be used, else None."""
        bad = [n for n in names if n not in self.rows]
        if not bad:
            return None
        kinds = {}
        for n in bad:
            kinds.setdefault(self.state[n][0], []).append(n)
        return (f"{len(bad)} of {len(names)} runs not usable ("
                + "; ".join(f"{k}: {', '.join(v[:4])}{' ...' if len(v) > 4 else ''}" for k, v in kinds.items()) + ")")


# ---- views of a run
def port_view(rows, q):
    """Port q during its own training pulses."""
    r = [x for x in rows if x["port"] == q]
    fired = [x["fired"] for x in r]
    step = [x["step"][q] for x in r]
    first = fired.index(True) if True in fired else None
    stopped = first is not None
    after = fired[first:] if stopped else []
    return dict(n=len(r), stopped=stopped, silent=first if stopped else len(r),
                relapses=[first + i for i, f in enumerate(after) if not f],
                silent_steps=step[:first] if stopped else step,
                relapse_steps=[s for s, f in zip(step[first:], after) if not f] if stopped else [],
                firing_steps=[s for s, f in zip(step, fired) if f],
                first_fire=r[first]["lat"] if stopped else None,
                vq_min=[x["vq_min"] for x in r], fired=fired)


def cell_view(name, rows):
    j = [x for x in rows if x["port"] == 0]
    j = j[-1] if j else None
    idle = [x["step"][1] for x in rows if x["port"] == 2] + [x["step"][2] for x in rows if x["port"] == 1]
    return dict(name=name, p=[port_view(rows, 1), port_view(rows, 2)], idle=idle, rows=rows,
                joint=j["lat"] if j and j["fired"] else None, has_joint_pulse=j is not None)


def refresh_view(name, rows):
    fired = [x["fired"] for x in rows]
    v = [x["v"][1] * 1e3 for x in rows]
    step = [x["step"][1] for x in rows]
    d = dict(name=name, fired=fired, v=v, stop=None, relapses=[], gaps=[], doubles=0, relapse_steps=[], band=None)
    if True in fired:
        stop = fired.index(True)
        rel = [k for k in range(stop, len(rows)) if not fired[k]]
        d.update(stop=stop, relapses=rel, gaps=[b - a for a, b in zip(rel, rel[1:])],
                 doubles=sum(1 for a, b in zip(rel, rel[1:]) if b == a + 1), relapse_steps=[step[k] for k in rel],
                 band=(max(v[stop:]) - min(v[stop:])) / DOSE)
    return d


def pairs_within(x, tol=0.05):
    x = sorted(x); j = ok = 0
    for i in range(len(x)):
        while x[i] - x[j] >= tol:
            j += 1
        ok += i - j
    return ok, len(x) * (len(x) - 1) // 2


# ---- the verdicts
class Report:
    def __init__(self):
        self.v, self.errors = [], 0

    def add(self, pid, statement, status, measured, reason=""):
        self.v.append(dict(id=pid, statement=statement, status=status, measured=measured or DASH, reason=reason or ""))

    def judge(self, pid, statement, measured, broken, gap=None):
        """broken: what makes the statement false of the usable runs.
        gap: reason if some runs of the series cannot be used. A statement that is already false stays false."""
        if broken:
            self.add(pid, statement, FAILS, measured, "; ".join(broken) + (f". Also: {gap}" if gap else ""))
        elif gap:
            self.add(pid, statement, NA, measured, gap)
        else:
            self.add(pid, statement, HOLDS, measured)

    def run(self, pid, statement, fn):
        """A check never stops the analysis."""
        try:
            fn(pid, statement)
        except Exception as e:                     # last resort: reported, and the exit code says so
            self.errors += 1
            self.add(pid, statement, NA, DASH, f"error in the analysis: {e.__class__.__name__}: {e}")


def analyse(res):
    c = Campaign(res)
    R = Report()
    S = {}                                         # numbers for summary.json and the figures
    cells = lambda names: [cell_view(n, c.rows[n]) for n in names if n in c.rows]

    # ---- checks on the nominal cell
    nom = cells(["nom"])
    nom = nom[0] if nom else None
    nom_gap = c.unusable(["nom"])

    def c1(pid, st):
        if not nom:
            return R.add(pid, st, NA, DASH, nom_gap)
        pat = "".join("F" if x["fired"] else "s" for x in nom["rows"])
        S["nominal_pattern"] = pat
        why = [f"port {q + 1} never fires" for q in (0, 1) if not nom["p"][q]["stopped"]]
        if nom["joint"] is None:
            why.append("no FIRE on the joint pulse")
        if pat != "ssssFFFFFF" * 2 + "F" and not why:
            why.append("the pattern differs")
        R.judge(pid, st, pat[:10] + " " + pat[10:20] + " " + pat[20:], why)
    R.run("C1", "pattern ssssFFFFFF on both ports, FIRE on the joint pulse", c1)

    def c2(pid, st):
        if not nom:
            return R.add(pid, st, NA, DASH, nom_gap)
        sil = nom["p"][0]["silent_steps"] + nom["p"][1]["silent_steps"]
        if not sil:
            return R.add(pid, st, NA, DASH, "no silent pulse")
        R.judge(pid, st, span(sil) + " mV", [] if 1.345 <= min(sil) and max(sil) <= 1.348 else ["a silent step is outside the range"])
    R.run("C2", "silent steps between 1.345 and 1.348 mV", c2)

    def c3(pid, st):
        if not nom:
            return R.add(pid, st, NA, DASH, nom_gap)
        fir = [abs(s) for q in (0, 1) for s in nom["p"][q]["firing_steps"]]
        if not fir:
            return R.add(pid, st, NA, DASH, "no FIRE")
        R.judge(pid, st, f"largest {max(fir):.3f} mV", [] if max(fir) < 0.002 else ["a firing step is 0.002 mV or more"])
    R.run("C3", "firing steps below 0.002 mV", c3)

    def c4(pid, st):
        if not nom:
            return R.add(pid, st, NA, DASH, nom_gap)
        r = [x for x in nom["rows"] if x["port"] == 1]
        ent = [x["entry"][1] for x in r if x["entry"][1] is not None]
        ext = [x["exit"][1] for x in r if x["exit"][1] is not None]
        reo = [x["reopen"] for x in r if x["fired"] and x["reopen"] is not None]
        S["nominal_window"] = [mean(ent), mean(ext), mean(reo)]
        measured = f"{fm(mean(ent))} to {fm(mean(ext))}, end {fm(mean(reo), '.2f')}"
        if not ent or not ext:
            return R.add(pid, st, NA, measured, "the write window was not seen")
        if not (abs(mean(ent) - 1.777) < 0.002 and abs(mean(ext) - 2.040) < 0.002):
            return R.add(pid, st, FAILS, measured, "the write window is not at 1.777 to 2.040")
        if not reo:
            return R.add(pid, st, NA, measured, "no FIRE: the end of the protection is not measured")
        R.judge(pid, st, measured, [] if abs(mean(reo) - 5.59) < 0.01 else ["the end of the protection is not at 5.59"])
    R.run("C4", "write window 1.777 to 2.040, protection ends at 5.59", c4)

    def c5(pid, st):
        if not nom:
            return R.add(pid, st, NA, DASH, nom_gap)
        if nom["joint"] is None:
            return R.add(pid, st, NA, DASH, "joint read without a FIRE")
        S["nominal_joint"] = nom["joint"]
        R.judge(pid, st, f"{nom['joint']:.4f}", [] if 0.2665 <= nom["joint"] <= 0.2685 else ["the joint read is outside the range"])
    R.run("C5", "joint read between 0.2665 and 0.2685", c5)

    # ---- noise on the nominal cell
    nz_names = c.series("nz_")
    nz = cells(nz_names)
    nz_gap = c.unusable(nz_names)
    nz_idle = [s for x in nz for s in x["idle"]]
    nz_sil = [s for x in nz for q in (0, 1) for s in x["p"][q]["silent_steps"]]
    nz_fir = [s for x in nz for q in (0, 1) for s in x["p"][q]["firing_steps"]]
    nz_joint = [x["joint"] for x in nz if x["joint"] is not None]
    S["noise"] = dict(runs=len(nz), joint=nz_joint, joint_sigma=sd(nz_joint), joint_mean=mean(nz_joint), idle_sigma_mV=sd(nz_idle),
                      silent_sigma_mV=sd(nz_sil), silent_mean_mV=mean(nz_sil), firing_mean_mV=mean(nz_fir), firing_sigma_mV=sd(nz_fir),
                      silent=[[x["p"][0]["silent"], x["p"][1]["silent"]] for x in nz],
                      relapses=sum(len(x["p"][q]["relapses"]) for x in nz for q in (0, 1)))

    def p1(pid, st):
        if not nz:
            return R.add(pid, st, NA, DASH, nz_gap)
        counts = [x["p"][q]["silent"] for x in nz for q in (0, 1)]
        never = sum(not x["p"][q]["stopped"] for x in nz for q in (0, 1))
        four = sum(all(x["p"][q]["silent"] == 4 and x["p"][q]["stopped"] for q in (0, 1)) for x in nz)
        broken = []
        if never:
            broken.append(f"{never} ports never fire")
        if min(counts) < 3 or max(counts) > 5:
            broken.append("a port is outside 3 to 5 silent pulses")
        if len(nz) - four > len(nz_names) - 18:
            broken.append(f"{len(nz) - four} runs do not have 4 silent pulses on both ports")
        R.judge(pid, st, f"{four} of {len(nz)} runs, range {min(counts)} to {max(counts)}", broken, nz_gap)
    R.run("P1", "4 silent pulses on both ports in at least 18 of 20 runs, never fewer than 3 or more than 5", p1)

    def p2(pid, st):
        if not nz:
            return R.add(pid, st, NA, DASH, nz_gap)
        s = sd(nz_joint)
        unc = f" (±{100 / math.sqrt(2 * (len(nz_joint) - 1)):.0f}% for {len(nz_joint)} runs)" if s is not None else ""
        measured = f"sigma {fm(s, '.5f')}{unc}, {span(nz_joint, '.4f')}"
        broken = []
        if len(nz_joint) < len(nz):
            broken.append(f"{len(nz) - len(nz_joint)} runs without a joint FIRE")
        if nz_joint and (min(nz_joint) < 0.264 or max(nz_joint) > 0.271):
            broken.append("a joint read is outside 0.264 to 0.271")
        if s is None and not broken:
            return R.add(pid, st, NA, measured, "fewer than two joint reads")
        if s is not None and s >= 0.0012 and nz_gap is None:
            broken.append("sigma is not below 0.0012")
        R.judge(pid, st, measured, broken, nz_gap)
    R.run("P2", "sigma of the joint read below 0.0012, every read between 0.264 and 0.271", p2)

    part = lambda gap: gap and gap + " (measured on the others)"

    def p3(pid, st):
        s = sd(nz_idle)
        if s is None:
            return R.add(pid, st, NA, DASH, nz_gap or "no port at rest")
        R.judge(pid, st, f"{s:.3f} mV", [] if 0.05 <= s <= 0.10 or nz_gap else ["sigma is outside the range"], part(nz_gap))
    R.run("P3", "a port at rest changes over a period with a sigma between 0.05 and 0.10 mV", p3)

    def p4(pid, st):
        a, b = sd(nz_sil), sd(nz_idle)
        if a is None or b is None:
            return R.add(pid, st, NA, DASH, nz_gap or "fewer than two silent pulses")
        # The write noise is what a silent step has beyond the read noise: a difference of two variances.
        # When that difference is not positive the write noise is not resolved; it is not measured as zero.
        w, top = write_noise(nz)
        S["noise"].update(write_sigma_mV=w, write_sigma_upper_mV=top)
        if w is None:
            measured = f"not resolved: a silent step ({a:.3f} mV) is not noisier than a port at rest ({b:.3f} mV)"
        else:
            measured = f"{w:.3f} mV (silent step {a:.3f} mV, port at rest {b:.3f} mV)"
        measured += f"; upper end of its 95% interval {fm(top)} mV"
        R.judge(pid, st, measured, [] if (w or 0.0) < 0.067 or nz_gap else ["the write is noisier than predicted"], part(nz_gap))
    R.run("P4", "sigma of a silent step, read noise removed, below 0.067 mV", p4)

    def p5(pid, st):
        a, b, m = sd(nz_fir), sd(nz_idle), mean(nz_fir)
        if a is None or b is None or b == 0:
            return R.add(pid, st, NA, DASH, nz_gap or "fewer than two firing pulses")
        ok = abs(m) < 0.01 and 0.75 <= a / b <= 1.25
        R.judge(pid, st, f"mean {m:+.4f} mV, sigma {a:.3f} mV ({a / b:.2f} of rest)",
                [] if ok or nz_gap else ["the firing steps differ from the steps at rest"], part(nz_gap))
    R.run("P5", "firing steps: mean within 0.01 mV of zero, sigma within 25% of the sigma at rest", p5)

    # ---- mismatch and noise
    mc_names = c.series("mc_")
    mc = cells(mc_names)
    mc_gap = c.unusable(mc_names)
    ports = [x["p"][q] for x in mc for q in (0, 1)]
    stopped = [p for p in ports if p["stopped"]]
    mc_joint = [x["joint"] for x in mc if x["joint"] is not None]
    rel = [p for p in stopped if p["relapses"]]
    calm = [p for p in stopped if not p["relapses"]]
    mc_idle = [s for x in mc for s in x["idle"]]
    counts = {}
    for p in stopped:
        counts[p["silent"]] = counts.get(p["silent"], 0) + 1
    S["mismatch_noise"] = dict(cells=len(mc), ports=len(ports), ports_stopped=len(stopped), silent_counts=counts, joint=mc_joint,
                               joint_sigma=sd(mc_joint), joint_mean=mean(mc_joint), ports_with_relapse=len(rel),
                               first_fire_calm=[p["first_fire"] for p in calm], first_fire_relapsing=[p["first_fire"] for p in rel],
                               relapse_steps_mV=[s for p in rel for s in p["relapse_steps"]], idle_sigma_mV=sd(mc_idle),
                               silent_steps_mV=[s for p in ports for s in p["silent_steps"]] + [s for p in rel for s in p["relapse_steps"]],
                               firing_steps_mV=[s for p in ports for s in p["firing_steps"]], idle_steps_mV=mc_idle)

    def p6(pid, st):
        if not mc:
            return R.add(pid, st, NA, DASH, mc_gap)
        n = [p["silent"] for p in stopped]
        broken = []
        if len(stopped) < len(ports):
            broken.append(f"{len(ports) - len(stopped)} ports never fire")
        out = sum(1 for k in n if k < 2 or k > 8)
        if out:
            broken.append(f"{out} ports are outside 2 to 8 silent pulses")
        dist = ", ".join(f"{k}: {counts[k]}" for k in sorted(counts))
        R.judge(pid, st, f"{len(stopped)} of {len(ports)} ports stop, {fm(lo(n), 'd')} to {fm(hi(n), 'd')} silent pulses (ports per count: {dist or DASH})",
                broken, mc_gap)
    R.run("P6", "both ports of every cell stop within 10 pulses, after 2 to 8 silent pulses", p6)

    def p7(pid, st):
        if not mc:
            return R.add(pid, st, NA, DASH, mc_gap)
        s = sd(mc_joint)
        ok, tot = pairs_within(mc_joint)
        broken = []
        if len(mc_joint) < len(mc):
            broken.append(f"{len(mc) - len(mc_joint)} cells without a joint FIRE")
        if mc_joint and (min(mc_joint) < 0.250 or max(mc_joint) > 0.280):
            broken.append("a joint read is outside 0.250 to 0.280")
        if ok < tot:
            broken.append(f"{tot - ok} pairs of cells are 0.05 apart or more")
        measured = f"{len(mc_joint)} of {len(mc)} fire, sigma {fm(s, '.4f')}, {span(mc_joint, '.4f')}, {ok} of {tot} pairs"
        if s is None and not broken:
            return R.add(pid, st, NA, measured, "fewer than two joint reads")
        if s is not None and not 0.0025 <= s <= 0.0042 and mc_gap is None:
            broken.append("sigma is outside 0.0025 to 0.0042")
        R.judge(pid, st, measured, broken, mc_gap)
    R.run("P7", "every cell fires on the joint pulse; sigma 0.0025 to 0.0042; reads between 0.250 and 0.280; every pair within 0.05", p7)

    def p8(pid, st):
        if not mc:
            return R.add(pid, st, NA, DASH, mc_gap)
        if not stopped:
            return R.add(pid, st, NA, DASH, "no port fires")
        late = [p["first_fire"] for p in rel]
        steps = [s for p in rel for s in p["relapse_steps"]]
        twice = sum(len(p["relapses"]) > 1 for p in rel)
        frac = 100.0 * len(rel) / len(ports)
        broken = []
        if late and min(late) <= 0.95:
            broken.append("a port relapses after a first FIRE at 0.95 or earlier")
        if twice:
            broken.append(f"{twice} ports relapse twice")
        if any(abs(s / DOSE - 1) > 0.20 for s in steps):
            broken.append("a relapse step is more than 20% from a dose")
        measured = (f"{len(rel)} of {len(ports)} ports ({frac:.1f}%), first FIRE of these {span(late)}, {twice} relapse twice, steps {span(steps)} mV"
                    if rel else f"no port relapses (0 of {len(ports)})")
        if mc_gap is None and not 4 <= frac <= 14:
            broken.append("no relapse observed: 4% to 14% of the ports were predicted" if not rel else "the share of relapsing ports is outside 4% to 14%")
        R.judge(pid, st, measured, broken, mc_gap)
    R.run("P8", "a port relapses only if its first FIRE came after 0.95; 4% to 14% of ports relapse; none twice; each relapse within 20% of a dose", p8)

    def p9(pid, st):
        if not mc:
            return R.add(pid, st, NA, DASH, mc_gap)
        total = [sum(p["firing_steps"]) for p in calm]
        a, b, m = sd(total), sd(mc_idle), mean(total)
        if a is None or b is None or b == 0:
            return R.add(pid, st, NA, DASH, "fewer than two ports stop without a relapse")
        S["mismatch_noise"].update(total_firing_mean_mV=m, total_firing_sigma_mV=a)
        ok = abs(m) < 0.03 and a < 1.5 * b
        R.judge(pid, st, f"mean {m:+.4f} mV, sigma {a:.3f} mV ({a / b:.2f} of rest), {len(calm)} ports",
                [] if ok or mc_gap else ["the stored voltage moves over the firing pulses"], part(mc_gap))
    R.run("P9", "ports without relapse: total change over the firing pulses has mean within 0.03 mV of zero and sigma below 1.5 times the sigma at rest", p9)

    # ---- the gate, on every run that produced a result, also a run that the guard left out of the statistics
    def p10(pid, st):
        fired_rows = [(n, x) for n, rows in c.raw.items() for x in rows if x["fired"]]
        steer = [(n, x["pulse"]) for n, x in fired_rows if x["steered"][1] or x["steered"][2]]
        S["firing_pulses"] = len(fired_rows)
        S["latest_fire"] = hi([x["lat"] for _, x in fired_rows])
        measured = f"{len(steer)} of {len(fired_rows)} firing pulses in {len(c.raw)} runs"
        if steer:
            return R.add(pid, st, FAILS, measured, "a firing pulse writes: " + ", ".join(f"{n} pulse {k}" for n, k in steer[:6]))
        if not fired_rows:
            return R.add(pid, st, NA, measured, "no firing pulse in any run")
        R.judge(pid, st, measured, [], None if len(c.raw) == len(c.plan) else f"{len(c.plan) - len(c.raw)} of {len(c.plan)} runs without a result")
    R.run("P10", "no firing pulse steers the sensor current to the integrator, in any run", p10)

    # ---- after the stop
    def p11(pid, st):
        nl = cells(["nom_long"])
        if not nl:
            return R.add(pid, st, NA, DASH, c.unusable(["nom_long"]))
        p = nl[0]["p"]
        tot = [sum(q["firing_steps"]) for q in p]
        nf = [len(q["firing_steps"]) for q in p]
        S["nominal_long"] = dict(firing_pulses=nf, total_mV=tot)
        measured = f"{tot[0]:+.4f} mV and {tot[1]:+.4f} mV over {nf[0]} and {nf[1]} firing pulses"
        broken = [f"port {i + 1} has {n} firing pulses, not 22" for i, n in enumerate(nf) if n != 22]
        if max(abs(t) for t in tot) >= 0.01:
            broken.append("the stored voltage moves by 0.01 mV or more")
        R.judge(pid, st, measured, broken)
    R.run("P11", "over 22 firing pulses the stored voltage moves by less than 0.01 mV", p11)

    # ---- corners
    want = dict(pvt_ss_27=4, pvt_ff_27=4, pvt_sf_27=4, pvt_fs_27=4, pvt_tt_m40=2, pvt_tt_125=7)

    def p12(pid, st):
        pv = cells(list(want))
        gap = c.unusable(list(want))
        if not pv:
            return R.add(pid, st, NA, DASH, gap)
        broken, shown = [], []
        S["corners"] = {}
        for x in pv:
            a, b = x["p"]
            n = x["name"][4:]
            S["corners"][n] = dict(silent=[a["silent"], b["silent"]], stopped=[a["stopped"], b["stopped"]], joint=x["joint"])
            shown.append(f"{n}: {a['silent'] if a['stopped'] else 'never'}/{b['silent'] if b['stopped'] else 'never'}, {fm(x['joint'], '.4f')}")
            if not (a["stopped"] and b["stopped"]):
                broken.append(f"{n}: a port never fires")
            elif a["silent"] != want[x["name"]] or b["silent"] != want[x["name"]]:
                broken.append(f"{n}: not {want[x['name']]} silent pulses")
            if x["joint"] is None:
                broken.append(f"{n}: joint read without a FIRE")
            elif not 0.262 <= x["joint"] <= 0.272:
                broken.append(f"{n}: joint read outside 0.262 to 0.272")
        R.judge(pid, st, "; ".join(shown), broken, gap)
    R.run("P12", "the six corner runs stop after 4, 4, 4, 4, 2 and 7 silent pulses; joint read between 0.262 and 0.272", p12)

    # ---- refresh
    rf = {n[8:]: refresh_view(n, c.rows[n]) for n in c.series("refresh_") if n in c.rows}
    S["refresh"] = {k: {a: b for a, b in v.items() if a not in ("v", "fired")} for k, v in rf.items()}

    def one(key, pid, st, fn):
        r = rf.get(key)
        if r is None:
            return R.add(pid, st, NA, DASH, c.unusable(["refresh_" + key]))
        if r["stop"] is None:
            return R.add(pid, st, FAILS, f"no FIRE in {len(r['fired'])} pulses", "the port never fires")
        fn(r, pid, st)

    def p13(r, pid, st):
        broken = []
        if r["relapses"]:
            broken.append(f"{len(r['relapses'])} relapses")
        if r["band"] >= 0.05:
            broken.append("the stored voltage moves by 0.05 dose or more")
        R.judge(pid, st, f"{len(r['relapses'])} relapses, band {r['band']:.3f} dose", broken)
    R.run("P13", "no leak, no noise: no relapse, stored voltage within 0.05 dose after the stop", lambda p, s: one("none", p, s, p13))

    def p14(r, pid, st):
        R.judge(pid, st, f"{len(r['relapses'])} relapses, band {r['band']:.2f} dose", [] if len(r["relapses"]) <= 1 else ["more than one relapse"])
    R.run("P14", "no leak, with noise: at most one relapse", lambda p, s: one("none_nz", p, s, p14))

    def leak(r, pid, st, gap_ok, gap_text, band, steps=None):
        """A run under a leak: relapses were predicted, so a run without them fails."""
        measured = f"{len(r['relapses'])} relapses, distances {sorted(set(r['gaps'])) if r['gaps'] else DASH}"
        if steps:
            measured += f", steps {span(r['relapse_steps'])} mV"
        measured += f", band {fm(r['band'], '.2f')} dose"
        if not r["relapses"]:
            return R.add(pid, st, FAILS, measured, "no relapse observed: relapses were predicted under this leak")
        if not r["gaps"]:
            return R.add(pid, st, FAILS, measured, "one relapse only: no distance between two relapses")
        broken = []
        if not all(gap_ok(g) for g in r["gaps"]):
            broken.append("a distance between two relapses is outside " + gap_text)
        if r["doubles"]:
            broken.append(f"two silent pulses in a row, {r['doubles']} times")
        if steps and not (steps[0] <= min(r["relapse_steps"]) and max(r["relapse_steps"]) <= steps[1]):
            broken.append("a relapse step is outside the range")
        if not r["band"] <= band[0] if band[1] else not r["band"] < band[0]:
            broken.append("the stored voltage leaves the band")
        R.judge(pid, st, measured, broken)

    R.run("P15", "0.1 TΩ: a relapse every 22 or 23 periods, never two silent pulses in a row, relapse steps 1.27 to 1.31 mV, band within 1.05 dose",
          lambda p, s: one("lk11", p, s, lambda r, p, s: leak(r, p, s, lambda g: g in (22, 23), "22 or 23", (1.05, True), (1.27, 1.31))))

    def p16(r, pid, st):
        measured = f"relapses at {r['relapses'] or DASH}, distances {r['gaps'] or DASH}"
        if not r["relapses"]:
            return R.add(pid, st, FAILS, measured, "no relapse observed: relapses were predicted under this leak")
        broken = []
        if not 85 <= r["relapses"][0] <= 100:
            broken.append("the first relapse is outside pulses 85 to 100")
        if not r["gaps"]:
            broken.append("one relapse only: no distance between two relapses")
        elif not all(220 <= g <= 224 for g in r["gaps"]):
            broken.append("a distance between two relapses is outside 220 to 224")
        R.judge(pid, st, measured, broken)
    R.run("P16", "1 TΩ: first relapse between pulses 85 and 100, relapses 220 to 224 periods apart", lambda p, s: one("lk12", p, s, p16))

    R.run("P17", "0.1 TΩ with noise: relapses 17 to 28 periods apart, never two silent pulses in a row, band within 1.6 dose",
          lambda p, s: one("lk11_nz", p, s, lambda r, p, s: leak(r, p, s, lambda g: 17 <= g <= 28, "17 to 28", (1.6, False))))

    def p18(pid, st):
        names = c.series("refresh_mm_")
        gap = c.unusable(names)
        mm = [rf[n[8:]] for n in names if n[8:] in rf]
        if not mm:
            return R.add(pid, st, NA, DASH, gap)
        shown, broken = [], []
        for r in mm:
            k = r["name"][11:]
            if r["stop"] is None:
                shown.append(f"{k}: never fires"); broken.append(f"cell {k} never fires"); continue
            if len(r["relapses"]) < 2:
                shown.append(f"{k}: {len(r['relapses'])} relapse")
                broken.append(f"cell {k}: fewer than two relapses, relapses were predicted"); continue
            mg = mean(r["gaps"])
            shown.append(f"{k}: {mg:.1f}, {r['doubles']} double, {r['band']:.2f}")
            if not (17 <= mg <= 29 and r["doubles"] <= 1 and r["band"] < 1.8):
                broken.append(f"cell {k} is outside the predicted ranges")
        R.judge(pid, st, "cell: mean distance, doubles, band in doses. " + "; ".join(shown), broken, gap)
    R.run("P18", "8 cells with mismatch and noise under 0.1 TΩ: mean distance between relapses 17 to 29, two silent pulses in a row at most once, band within 1.8 dose", p18)

    # ---- the runs and the guard
    def p19(pid, st):
        by = {}
        for n in c.plan:
            by.setdefault(c.state[n][0], []).append(n)
        got = len(by.get("complete", [])) + len(by.get("left out", []))
        measured = (f"{got} of {len(c.plan)} runs with a result, {len(by.get('failed', []))} failed, {len(by.get('missing', []))} missing, "
                    f"{len(by.get('unreadable', []))} not readable, {len(c.not_fire)} with a protection that is not a FIRE, "
                    f"{len(c.against)} with an event against the mechanism")
        broken = []
        if by.get("failed"):
            broken.append(f"{len(by['failed'])} runs failed")
        if c.not_fire:
            broken.append(f"{len(c.not_fire)} runs with a protection that is not a FIRE")
        if c.against:
            broken.append(f"{len(c.against)} runs with an event against the mechanism")
        lost = len(by.get("missing", [])) + len(by.get("unreadable", []))
        R.judge(pid, st, measured, broken, f"{lost} runs missing or not readable" if lost else None)
    R.run("P19", "no run fails and the guard reports nothing", p19)

    R.v.sort(key=lambda v: (v["id"][0], int(v["id"][1:])))
    S["runs"] = {n: dict(state=s, reason=w) for n, (s, w) in c.state.items()}
    S["not_a_fire"], S["against_the_mechanism"], S["results_not_in_the_plan"] = c.not_fire, c.against, c.extra
    return c, R, S, dict(nom=nom, mc=mc, rf=rf, ports=ports, stopped=stopped, calm=calm, rel=rel)


VR0 = 1.25                         # V, rest level of the main capacitor (cell.spice)


def port_swings(cv):
    """For each port of a cell that stops: its count of silent pulses, its swing at the first pulse, the swing at which the cell
    fires, and the log-gain it gains at each silent pulse. The swing is the rest level minus the lowest level of the main capacitor."""
    fire = [VR0 - x["vq_min"] for x in cv["rows"] if x["fired"] and x["port"] in (1, 2)]
    if not fire:
        return []
    trip = statistics.median(fire)                 # swing at which this cell fires
    out = []
    for q in (0, 1):
        p = cv["p"][q]
        sw = [VR0 - v for v in p["vq_min"]]
        if not p["stopped"] or not sw or min(sw) <= 0 or trip <= 0:
            continue
        out.append(dict(run=cv["name"], port=q + 1, n=p["silent"], s1=sw[0], trip=trip, joint=cv["joint"],
                        d=[math.log(sw[i + 1] / sw[i]) for i in range(p["silent"] - 1)],
                        other=cv["p"][1 - q]["silent"] if cv["p"][1 - q]["stopped"] else None))
    return out


def start_gaps(ports):
    """Adds to each port its start gap in its own doses and the count that this gap predicts. Returns the mean dose in log-gain, or None."""
    dm = mean([x for p in ports for x in p["d"]])
    if not dm:
        return None
    for p in ports:
        p["gap"] = math.log(p["trip"] / p["s1"]) / (mean(p["d"]) or dm)
        p["pred"] = max(0, math.ceil(p["gap"]))
    return dm


def observations(c):
    """Measures made after the campaign on its results. They are not predictions.

    The peak of the main charge in a pulse is proportional to the gain of the pulsed port. The
    swing is the rest level minus the lowest level of the main capacitor in the period."""
    lines, O = [], {}

    ports_of = lambda name: port_swings(cell_view(name, c.rows[name])) if name in c.rows else []

    # the dose in log-gain: the gain of a port grows by this much at each silent pulse
    lines.append("### The dose in log-gain\n")
    lines.append("Measured from the peak of the main charge at consecutive silent pulses.\n")
    lines.append("| Runs | Dose in log-gain | Steps measured |\n|---|---|---|")
    O["dose_log_gain"] = {}
    for label, names in (("nominal, 27 °C", ["nom"]), ("ss, ff, sf, fs at 27 °C", ["pvt_ss_27", "pvt_ff_27", "pvt_sf_27", "pvt_fs_27"]),
                         ("typical, −40 °C", ["pvt_tt_m40"]), ("typical, 125 °C", ["pvt_tt_125"]), ("mismatch and noise, 27 °C", c.series("mc_"))):
        d = [x for n in names for p in ports_of(n) for x in p["d"]]
        O["dose_log_gain"][label] = dict(mean=mean(d), sigma=sd(d), n=len(d))
        lines.append(f"| {label} | {fm(mean(d), '.4f')}" + (f" (sigma {sd(d):.4f})" if len(d) > 20 else "") + f" | {len(d)} |")

    # the count of silent pulses against the start gap
    ports = [p for n in c.series("mc_") for p in ports_of(n)]
    lines.append("\n### The count of silent pulses and the start gap\n")
    if not ports:
        lines.append("Not evaluable: no port of the mismatch series fires.")
        return lines, O
    dm = start_gaps(ports)
    if not dm:
        lines.append("Not evaluable: no port has two silent pulses, so the dose in log-gain is not measured.")
        return lines, O
    same = [p for p in ports if p["pred"] == p["n"]]
    off = [p for p in ports if p["pred"] != p["n"]]
    far = hi([min(abs(p["gap"] - round(p["gap"])), 1.0) for p in off])
    gaps = [p["gap"] for p in ports]
    O["start_gap"] = dict(ports=len(ports), count_equals_ceiling=len(same), others=len(off), others_farthest_from_an_integer=far,
                          mean=mean(gaps), sigma=sd(gaps), min=min(gaps), max=max(gaps))
    lines.append("The start gap of a port is the log of the ratio of the swing at which its cell fires to its swing at the first pulse, "
                 "in doses of that port. A port should need the next whole number of doses.\n")
    lines.append(f"- {len(same)} of {len(ports)} ports have a count of silent pulses equal to their start gap rounded up.")
    if off:
        lines.append(f"- The {len(off)} others have a start gap within {far:.2f} dose of a whole number, where the estimate of the firing swing decides.")
    lines.append(f"- Start gap over the {len(ports)} ports: mean {mean(gaps):.2f} doses, sigma {fm(sd(gaps), '.2f')}, from {min(gaps):.2f} to {max(gaps):.2f}.")
    if sd(gaps):
        N = statistics.NormalDist(mean(gaps), sd(gaps))
        O["start_gap"]["normal_fit_ports_at_one_or_fewer"] = len(ports) * N.cdf(1)
        lines.append(f"- A normal law with this mean and sigma puts {len(ports) * N.cdf(1):.1f} of {len(ports)} ports at one silent pulse or fewer, "
                     f"and {100 * (N.cdf(8) - N.cdf(1)):.1f}% of the ports between 2 and 8.")
    few = [p for p in ports if p["n"] < 2]
    O["ports_below_two"] = [dict(run=p["run"], port=p["port"], silent=p["n"], gap=p["gap"], other_port_silent=p["other"], joint=p["joint"]) for p in few]
    for p in few:
        lines.append(f"- Port {p['port']} of `{p['run']}` has {p['n']} silent pulse: its start gap is {p['gap']:.2f} dose. The other port of that cell has "
                     f"{fm(p['other'], 'd')} silent pulses. The joint read of that cell: " + (f"FIRE at {p['joint']:.4f}." if p["joint"] is not None else "no FIRE."))
    return lines, O


def write_noise(cells):
    """Sigma of a silent step with the read noise removed, and the upper end of its 95% interval.
    The sigma is None when the difference of the two variances is not positive: not resolved."""
    units = [dict(silent=[s for p in x["p"] for s in p["silent_steps"]], idle=x["idle"]) for x in cells]
    def excess(runs):
        a, b = sd([s for r in runs for s in r["silent"]]), sd([s for r in runs for s in r["idle"]])
        return None if a is None or b is None else a * a - b * b
    e, ci = excess(units), interval(units, excess)
    return (math.sqrt(e) if e is not None and e > 0 else None), (math.sqrt(max(ci[1], 0.0)) if ci else None)


def interval(units, stat, draws=1000):
    """95% interval of a statistic by resampling whole runs with replacement (the draws are fixed: same report each time)."""
    if len(units) < 3:
        return None
    rng = random.Random(0)
    got = []
    for _ in range(draws):
        v = stat([units[rng.randrange(len(units))] for _ in units])
        if v is not None:
            got.append(v)
    got.sort()
    return (got[int(0.025 * len(got))], got[int(0.975 * len(got)) - 1]) if len(got) >= 40 else None


def intervals(c, O):
    """The numbers that come from noise, with the interval that the number of runs allows."""
    flat = lambda key: (lambda runs: sd([x for r in runs for x in r[key]]))
    nz = [cell_view(n, c.rows[n]) for n in c.series("nz_") if n in c.rows]
    mc = [cell_view(n, c.rows[n]) for n in c.series("mc_") if n in c.rows]
    def unit(x):
        ports = [p for p in x["p"] if p["stopped"]]
        return dict(joint=[x["joint"]] if x["joint"] is not None else [], idle=x["idle"], silent=[s for p in x["p"] for s in p["silent_steps"]],
                    firing=[s for p in x["p"] for s in p["firing_steps"]], ports=len(x["p"]), relapsing=sum(1 for p in ports if p["relapses"]),
                    total=[sum(p["firing_steps"]) for p in ports if not p["relapses"]])
    a, b = [unit(x) for x in nz], [unit(x) for x in mc]
    share = lambda runs: 100.0 * sum(r["relapsing"] for r in runs) / sum(r["ports"] for r in runs) if runs else None
    rows = [("Sigma of the joint read, noise only (P2)", a, flat("joint"), ".5f", ""),
            ("Sigma of the change of a port at rest, noise only (P3)", a, flat("idle"), ".3f", " mV"),
            ("Sigma of a silent step with its read noise, noise only", a, flat("silent"), ".3f", " mV"),
            ("Sigma of a firing step, noise only (P5)", a, flat("firing"), ".3f", " mV"),
            ("Sigma of the joint read, mismatch and noise (P7)", b, flat("joint"), ".4f", ""),
            ("Share of the ports with a relapse, mismatch and noise (P8)", b, share, ".1f", "%"),
            ("Sigma of the total change over the firing pulses (P9)", b, flat("total"), ".3f", " mV")]
    L = ["\n### Intervals of the numbers that come from noise\n",
         "A noisy run cannot be replayed: its seed does not set its noise (COMPLEMENT.md). Running the campaign again gives other runs from "
         "the same distribution. The intervals below are 95% intervals, from resampling the runs of the campaign.\n",
         "| Number | Value | 95% interval | Runs |\n|---|---|---|---|"]
    O["intervals"] = {}
    for label, units, stat, spec, unit_ in rows:
        v, ci = stat(units), interval(units, stat)
        O["intervals"][label] = dict(value=v, interval=ci, runs=len(units))
        L.append(f"| {label} | {fm(v, spec)}{unit_ if v is not None else ''} | " + (f"{ci[0]:{spec}} to {ci[1]:{spec}}{unit_}" if ci else DASH) + f" | {len(units)} |")
    w, top = write_noise(nz)
    L.append(f"| Write noise: sigma of a silent step with the read noise removed, noise only (P4) | {fm(w) + ' mV' if w is not None else 'not resolved'} | "
             f"{'below ' + fm(top) + ' mV' if top is not None else DASH} | {len(nz)} |")
    mm = [refresh_view(n, c.rows[n]) for n in c.series("refresh_mm_") if n in c.rows]
    gaps = [mean(r["gaps"]) for r in mm if r["gaps"]]
    bands = [r["band"] for r in mm if r["band"] is not None]
    L.append(f"| Mean distance between two relapses, one value per cell under 0.1 TΩ (P18) | {fm(mean(gaps), '.1f')} | "
             f"cells from {fm(lo(gaps), '.1f')} to {fm(hi(gaps), '.1f')}, sigma {fm(sd(gaps), '.1f')} | {len(gaps)} |")
    L.append(f"| Band of the stored voltage after the stop, one value per cell under 0.1 TΩ (P18) | {fm(mean(bands), '.2f')} dose | "
             f"cells from {fm(lo(bands), '.2f')} to {fm(hi(bands), '.2f')}, sigma {fm(sd(bands), '.2f')} | {len(bands)} |")
    L.append("\nThe two noisy refresh runs of one port without mismatch (P14, P17) are one run each in the campaign. "
             "One run gives no interval. The complement repeats them.\n")
    return L


def write_report(c, R, S, out):
    n = {k: sum(v["status"] == k for v in R.v) for k in (HOLDS, FAILS, NA)}
    with open(f"{out}/VERDICTS.md", "w") as fh:
        fh.write("# Verdicts\n\nWritten by `analyze.py` from the results. The statements are those of `PREDICTION.md`.\n\n")
        fh.write("The date of `PREDICTION.md` cannot be checked from this repository alone: see `PREDICTION_PROVENANCE.md`. "
                 "The predictions are not blind.\n\n")
        fh.write(f"{n[HOLDS]} hold, {n[FAILS]} fail, {n[NA]} not evaluable, of {len(R.v)}.\n\n")
        fh.write("| | Statement | Measured | Status | Reason |\n|---|---|---|---|---|\n")
        for v in R.v:
            fh.write(f"| {v['id']} | {v['statement']} | {v['measured']} | {v['status']} | {v['reason'] or DASH} |\n")
        states = {}
        for name in c.plan:
            states.setdefault(c.state[name][0], []).append(name)
        fh.write(f"\n## Runs\n\nThe plan of `campaign.py` has {len(c.plan)} runs.\n\n| State | Runs | Which |\n|---|---|---|\n")
        label = {"complete": "complete", "left out": "left out by the guard", "failed": "failed",
                 "missing": "not evaluable: run missing", "unreadable": "not evaluable: result not readable"}
        for k in label:
            v = states.get(k, [])
            which = DASH if k == "complete" or not v else "; ".join(f"{x} ({c.state[x][1]})" for x in v[:12]) + (" ..." if len(v) > 12 else "")
            fh.write(f"| {label[k]} | {len(v)} | {which} |\n")
        if c.extra:
            fh.write(f"\nResults that are not in the plan, not used: {', '.join(c.extra)}.\n")
        show = lambda L: ("; ".join(f"{a['run']} ({', '.join(a['kind'])}; pulses {', '.join(str(p) for p in a['pulses']) or DASH})" for a in L)
                          if L else "none")
        fh.write("\n## Guard\n\n")
        fh.write(f"- Runs with a protection that is not a FIRE, left out of the statistics: {show(c.not_fire)}.\n")
        fh.write(f"- Runs with an event against the mechanism, kept in the statistics: {show(c.against)}.\n")
        fh.write(f"- Latest FIRE of the campaign: {fm(S.get('latest_fire'), '.4f')} units after the start of its pulse. The pulse ends at 1.\n")
        fh.write("\n## Observations made after the campaign\n\nThese are not predictions.\n\n")
        try:
            lines, S["observations"] = observations(c)
            fh.write("\n".join(lines + intervals(c, S["observations"])) + "\n")
        except Exception as e:
            R.errors += 1
            fh.write(f"Not evaluable: error in the analysis ({e.__class__.__name__}: {e}).\n")
    return n


def figures(S, X, out):
    """Each figure is drawn only if its data exist."""
    import numpy as np
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    import matplotlib.ticker
    BLUE, ORANGE, INK, MUTED, GRID, SURF = "#2a78d6", "#eb6834", "#0b0b0b", "#52514e", "#e4e3df", "#fcfcfb"
    plt.rcParams.update({"figure.facecolor": SURF, "axes.facecolor": SURF, "savefig.facecolor": SURF, "axes.edgecolor": GRID, "axes.labelcolor": MUTED,
                         "xtick.color": MUTED, "ytick.color": MUTED, "text.color": INK, "axes.titlesize": 10.5, "axes.titleweight": "bold",
                         "axes.titlelocation": "left", "axes.spines.top": False, "axes.spines.right": False, "axes.grid": True, "grid.color": GRID,
                         "grid.linewidth": 0.6, "axes.axisbelow": True, "font.size": 9.5, "legend.frameon": False, "lines.linewidth": 2.0})
    os.makedirs(f"{out}/figures", exist_ok=True)
    drawn = []

    def save(fig, name):
        fig.tight_layout(); fig.savefig(f"{out}/figures/{name}.png", dpi=170); plt.close(fig); drawn.append(name)

    nom, mc, rf, ports, stopped = (X[k] for k in ("nom", "mc", "rf", "ports", "stopped"))
    if nom and nom["rows"]:
        r = nom["rows"]; k = np.arange(1, len(r) + 1)
        v1 = np.array([x["v"][1] for x in r]) * 1e3; v2 = np.array([x["v"][2] for x in r]) * 1e3
        fired = np.array([x["fired"] for x in r])
        pat = "".join("F" if f else "s" for f in fired)
        fig, ax = plt.subplots(figsize=(7.4, 3.5))
        ax.step(k, v1, where="mid", color=BLUE, label="port 1"); ax.step(k, v2, where="mid", color=ORANGE, label="port 2")
        low = min(v1.min(), v2.min()) - 0.9; top = max(v1.max(), v2.max())
        if fired.any():
            ax.scatter(k[fired], np.full(fired.sum(), low), marker="|", s=90, color=INK, linewidths=1.6)
            ax.annotate("FIRE", (k[fired][0], low), xytext=(-30, -3), textcoords="offset points", color=MUTED, fontsize=8.5)
        ax.set_xlabel("pulse"); ax.set_ylabel("stored voltage (mV)"); ax.set_ylim(low - 0.7, top + 0.9)
        ax.set_xticks(range(1, len(r) + 1, 2 if len(r) <= 30 else 5))
        ax.set_title("Nominal cell, no noise: stored voltage after each pulse", pad=20)
        ax.text(0.0, 1.02, f"s silent, F fire, pulse by pulse:  {pat[:len(pat) // 2]} {pat[len(pat) // 2:-1]} {pat[-1:]}", transform=ax.transAxes,
                va="bottom", color=MUTED, fontsize=8.5)
        ax.legend(loc="center right")
        save(fig, "fig1_nominal")

    M = S.get("mismatch_noise", {})
    joint = np.array(M.get("joint", []))
    if mc and M.get("silent_counts") and len(joint) >= 2:
        fig, ax = plt.subplots(1, 2, figsize=(9.6, 3.5))
        cnt = M["silent_counts"]; ks = sorted(cnt)
        ax[0].bar(ks, [cnt[c] for c in ks], width=0.72, color=BLUE)
        for c in ks:
            ax[0].text(c, cnt[c] + 1.2, str(cnt[c]), ha="center", color=MUTED, fontsize=8.5)
        ax[0].set_xlabel("silent pulses before the first FIRE"); ax[0].set_ylabel("ports"); ax[0].set_xticks(ks); ax[0].grid(axis="x", visible=False)
        ax[0].set_title(f"Silent pulses before the first FIRE, {len(stopped)} of {len(ports)} ports")
        ax[1].hist(joint, bins=np.arange(joint.min() - 0.00025, joint.max() + 0.00075, 0.001), color=BLUE, rwidth=0.86)
        ax[1].axvspan(0.239, 0.256, color=MUTED, alpha=0.13, lw=0)        # stopped_pair_read_latency: (239/1000, 32/125]
        inside = int(((joint > 0.239) & (joint <= 0.256)).sum())
        ax[1].text(0.2475, ax[1].get_ylim()[1] * 0.8, "window proved\nfor the ideal model", ha="center", color=MUTED, fontsize=8.5)
        ax[1].set_xlim(min(0.238, joint.min() - 0.003), max(0.282, joint.max() + 0.003))
        ax[1].set_xlabel("joint read latency (time units)"); ax[1].set_ylabel("cells")
        ax[1].set_title(f"Joint read latency, {len(joint)} of {len(mc)} cells")
        ax[1].text(0.99, 0.97, f"sigma {joint.std(ddof=1):.4f}\n{inside} of {len(joint)} inside the window", transform=ax[1].transAxes,
                   ha="right", va="top", color=MUTED, fontsize=8.5)
        save(fig, "fig2_cells")

    if mc and M.get("idle_steps_mV") and M.get("firing_steps_mV") and M.get("silent_steps_mV"):
        idle, fs_all, ss_all = (np.array(M[k]) for k in ("idle_steps_mV", "firing_steps_mV", "silent_steps_mV"))
        allv = np.concatenate([idle, fs_all, ss_all])
        fig, ax = plt.subplots(figsize=(7.4, 3.5))
        bins = np.arange(min(-0.4, allv.min() - 0.04), max(1.8, allv.max() + 0.08), 0.04)
        ax.hist(idle, bins=bins, histtype="step", color=MUTED, linewidth=1.4, label=f"port at rest ({len(idle)})")
        ax.hist(fs_all, bins=bins, histtype="step", color=BLUE, linewidth=2.0, label=f"firing pulse ({len(fs_all)})")
        ax.hist(ss_all, bins=bins, histtype="step", color=ORANGE, linewidth=2.0, label=f"silent pulse ({len(ss_all)})")
        ax.axvline(DOSE, color=GRID, linewidth=1.0); ax.text(DOSE, ax.get_ylim()[1] * 0.93, " one dose", color=MUTED, fontsize=8.5)
        ax.set_xlabel("change of the stored voltage over one period (mV)"); ax.set_ylabel("pulses")
        ax.set_title(f"Change of the stored voltage over one period, {len(mc)} cells with mismatch and noise")
        ax.legend(loc="upper center")
        save(fig, "fig3_steps")

    ff_calm, ff_rel = M.get("first_fire_calm", []), M.get("first_fire_relapsing", [])
    if mc and (ff_calm or ff_rel):
        ff_all = ff_calm + ff_rel
        fig, ax = plt.subplots(figsize=(7.4, 3.2))
        bins = np.arange(min(0.78, min(ff_all) - 0.01), max(1.0101, max(ff_all) + 0.0101), 0.01)
        ax.hist([ff_calm, ff_rel], bins=bins, stacked=True, color=[BLUE, ORANGE], rwidth=0.86,
                label=[f"no relapse ({len(ff_calm)} ports)", f"a silent pulse later ({len(ff_rel)} ports)"])
        ax.set_ylim(0, ax.get_ylim()[1] * 1.3); ax.yaxis.set_major_locator(matplotlib.ticker.MaxNLocator(integer=True))
        ax.axvline(1.0, color=GRID, linewidth=1.0); ax.text(0.999, ax.get_ylim()[1] * 0.9, "end of the pulse ", ha="right", color=MUTED, fontsize=8.5)
        ax.set_xlabel("latency of the first FIRE of a port (time units)"); ax.set_ylabel("ports")
        ax.set_title("Latency of the first FIRE of a port, and whether a silent pulse follows")
        ax.legend(loc="upper left")
        save(fig, "fig4_late_stop")

    panels = [(k, t) for k, t in (("none_nz", "no leak, with noise"), ("lk11", "leak through 0.1 TΩ, no noise"),
                                  ("lk11_nz", "leak through 0.1 TΩ, with noise"), ("lk12", "leak through 1 TΩ, no noise")) if k in rf and rf[k]["v"]]
    if panels:
        fig, ax = plt.subplots(len(panels), 1, figsize=(7.8, 1.9 * len(panels) + 0.5), squeeze=False)
        for a, (kk, title) in zip(ax[:, 0], panels):
            r = rf[kk]; x = np.arange(1, len(r["v"]) + 1); v = np.array(r["v"])
            a.plot(x, v, color=BLUE, linewidth=1.3)
            s = [i for i in range(len(v)) if not r["fired"][i]]
            a.scatter(x[s], v[s], color=ORANGE, s=22, zorder=3, edgecolors=SURF, linewidths=0.8)
            a.set_ylabel("stored (mV)"); a.set_title(title, fontsize=9.5, fontweight="normal", color=MUTED)
        ax[0, 0].scatter([], [], color=ORANGE, s=22, label="silent pulse"); ax[0, 0].plot([], [], color=BLUE, linewidth=1.3, label="stored voltage after each pulse")
        ax[0, 0].legend(loc="upper right", ncol=2, fontsize=8.5)
        ax[-1, 0].set_xlabel("pulse")
        fig.suptitle("Stored voltage of one port under continued pulses", x=0.01, ha="left", fontsize=10.5, fontweight="bold")
        save(fig, "fig5_refresh")

    mm = [rf[k] for k in sorted(rf) if k.startswith("mm_") and rf[k]["v"]]
    if mm:
        fig, ax = plt.subplots(2, 4, figsize=(10.4, 4.2), sharex=True)
        for a, r in zip(ax.ravel(), mm):
            x = np.arange(1, len(r["v"]) + 1); v = np.array(r["v"])
            a.plot(x, v - v[-1], color=BLUE, linewidth=1.2)
            s = [i for i in range(len(v)) if not r["fired"][i]]
            a.scatter(x[s], (v - v[-1])[s], color=ORANGE, s=16, zorder=3, edgecolors=SURF, linewidths=0.6)
            a.set_title("cell " + r["name"][11:], fontsize=9, fontweight="normal", color=MUTED)
        for a in ax[:, 0]: a.set_ylabel("stored, from its end (mV)")
        for a in ax[-1, :]: a.set_xlabel("pulse")
        fig.suptitle("Eight cells with mismatch and noise under a leak of 0.1 TΩ (orange: silent pulse)", x=0.01, ha="left", fontsize=10.5, fontweight="bold")
        save(fig, "fig6_refresh_cells")
    return drawn


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--results", default="results")
    ap.add_argument("--out", default=".")
    ap.add_argument("--no-figures", action="store_true")
    a = ap.parse_args(argv)
    c, R, S, X = analyse(a.results)
    os.makedirs(a.out, exist_ok=True)
    n = write_report(c, R, S, a.out)                       # the report is written before anything else can go wrong
    if os.path.isdir(a.results):
        with open(f"{a.results}/summary.json", "w") as fh:
            json.dump(dict(counts=n, verdicts=R.v, summary=S), fh, indent=1)
    for v in R.v:
        print(f"{v['id']:4s} {v['status']:14s} {v['measured']}" + (f"   [{v['reason']}]" if v["reason"] else ""))
    print(f"{n[HOLDS]} hold, {n[FAILS]} fail, {n[NA]} not evaluable, of {len(R.v)}")
    if not a.no_figures:
        try:
            print("figures:", ", ".join(figures(S, X, a.out)) or "none")
        except Exception as e:
            R.errors += 1
            print(f"figures not drawn: {e.__class__.__name__}: {e}")
    return 2 if R.errors else 0


if __name__ == "__main__":
    sys.exit(main())
