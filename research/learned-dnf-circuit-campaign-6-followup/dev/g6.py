"""Development only: G6 of DOSE_PLAN.md, "the noise in mV, per constant", on the noisy network runs of the nominal
cell at each dose. No simulation: it reads the runs' records and waveforms with campaign 5's readers.

  g6.py REPO CONFIG.json OUT.json

CONFIG.json: {"doses": {"1x": {"cal_on": DIR, "quiet": DIR, "noisy": [DIR, ...]}, "2x": {...}}}
  cal_on: the guard-on calibration deck at that dose (for the slope and the doses); quiet: the quiet network run at
  the same needs; noisy: the noisy network runs.

Three readings, each noisy run against the quiet run of its dose:

1. The definition of campaign 3 (its analyze.py, M5; phase 1's constants.py). Per noisy run and kind of read (pair
   of a, pair of b, line 1 of c alone, line 2 of c alone), only if the run gave the quiet run's word for that kind and
   has at least 3 FIREs of it:
       offset = (median FIRE latency of the quiet run - mean FIRE latency of the noisy run) / slope
       within = stdev(FIRE latencies of the noisy run) / slope
   b = root mean square of the offsets; w = root mean square of the withins. The slope is phase 1's `secant`, copied,
   on the firing reads of the kind in the dose's own guard-on deck, at the trained state (the deck's first firing
   stage); for a pair the stored voltage is the mean of its two ports.
   d = root mean square of (dose of a noisy run - dose of the same slot in the quiet run), on the reads where both
   runs write the port once.
2. The same with a three-point slope at the trained state (1.5 x first secant - 0.5 x next): a sensitivity case.
3. The audit's instrument (NOISE_AUDIT.md sections 4 and 5.3): the score of silent training reads and the FIRE level
   of firing reads, noisy minus quiet, in steps of the quiet run, split into what a run adds and the scatter within.

G6, as written in DOSE_PLAN.md: go if d, w and b are each within 25 % of their 1x value; stop if w or b grows by
more than 60 % at 2x; otherwise unclear. It is judged on reading 1, all kinds together; readings 2 and 3, and
reading 1 by kind, are given beside it. By the letter, a constant that falls by more than 25 % at 2x also gives
"unclear". The quiet run's FIRE latencies are not all equal (the reads of a kind are not at the same state): their
own scatter, in the same mV, is reported under quiet, as the floor of `within`.

Fixed before any noisy run of the experiment: reading 1 governs; a run counts for a kind only if its word for that
kind equals the quiet run's exactly; if the noise fingerprints of a dose's noisy runs are not all distinct, or one is
the quiet run's, G6 is "not judged: noise fingerprints" and nothing is computed. Beside the verdict, and not governing:
the verdict reading 2 would give, b and w in latency units (no slope), and b and w divided by the dose of the kind,
in stages.
"""
import json
import math
from pathlib import Path
import statistics
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import dosedev

KINDS = ("a", "b", "c1", "c2")
DECK = dict(a=("a", "both", ("1", "2")), b=("b", "both", ("1", "2")), c1=("c", "port 1", ("1",)), c2=("c", "port 2", ("2",)))
GO_WITHIN, STOP_ABOVE = 0.25, 0.60


def rms(xs):
    return math.sqrt(sum(x * x for x in xs) / len(xs)) if xs else None


def sd(xs):
    return statistics.pstdev(xs) if len(xs) > 1 else None


def secant(points, u):                                       # research/network-circuit/phase1/constants.py, verbatim
    points = sorted(set(points))
    merged = []
    for p in points:
        if merged and p[0] - merged[-1][0][0] < 0.02:
            merged[-1].append(p)
        else:
            merged.append([p])
    points = [(statistics.mean(x[0] for x in g), statistics.mean(x[1] for x in g)) for g in merged]
    assert len(points) >= 2
    i = min(max(sum(1 for p in points if p[0] <= u), 1), len(points) - 1)
    (u0, l0), (u1, l1) = points[i - 1], points[i]
    return (l1 - l0) / (u1 - u0)


def split(groups):
    """groups: {name: [values]}. Scatter within a group (pooled, n - 1), the rms of the group means, and that rms with
    the part due to the scatter within removed. As noise_audit.constants."""
    gs = [v for v in groups.values() if len(v) >= 2]
    if not gs:
        return None
    dof = sum(len(v) - 1 for v in gs)
    within2 = sum(sum((x - statistics.fmean(v)) ** 2 for x in v) for v in gs) / dof
    means2 = statistics.fmean(statistics.fmean(v) ** 2 for v in gs)
    corrected2 = means2 - statistics.fmean(within2 / len(v) for v in gs)
    return dict(groups=len(gs), values=sum(len(v) for v in gs), within_sd=math.sqrt(within2), rms_of_group_means=math.sqrt(means2),
                between_corrected=math.sqrt(max(corrected2, 0.0)))


def kind_of(x, c, r):
    """The kind of a read of cell c in slot x: a, b (their pair, in any stage but the skew control), c1, c2 (one line
    arrived), or None."""
    if x["stage"] == "skew control":
        return None
    if c in "ab":
        return c
    arrived = sorted({a["port"] for a in r["arrivals"]})
    return f"c{arrived[0]}" if len(arrived) == 1 else None


def one_dose(repo_modules, label, cfg):
    measure, plans4, reads4 = repo_modules
    # precondition: the noise of every noisy run is its own, and none is the quiet run's. Nothing is read past a failure.
    marks = {json.loads((Path(d) / "record.json").read_text())["id"]: json.loads((Path(d) / "record.json").read_text())["noise_fingerprint"] for d in cfg["noisy"]}
    quiet_mark = json.loads((Path(cfg["quiet"]) / "record.json").read_text())["noise_fingerprint"]
    if len(marks) != len(cfg["noisy"]) or len(set(marks.values())) != len(marks) or quiet_mark in marks.values():
        return dict(label=label, noise_fingerprints=marks, quiet_noise_fingerprint=quiet_mark, fingerprints_all_distinct_and_not_the_quiet_one=False)

    def rows_of(d):
        d = Path(d)
        rec = json.loads((d / "record.json").read_text())
        plan, slots = plans4.network(tuple(rec["needs"]), rec["control"])
        result = json.loads((d / "evidence" / "result.json").read_text())
        rows = reads4.network_reads(measure.Trace(d / "evidence" / "trace.raw"), result, slots)
        return rec, rows, reads4.words(rows)

    # the dose's own guard-on deck: the doses and the slopes
    cal = Path(cfg["cal_on"])
    crec = json.loads((cal / "record.json").read_text())
    cres = json.loads((cal / "evidence" / "result.json").read_text())
    crows = reads4.calibration_reads(measure.Trace(cal / "evidence" / "trace.raw"), cres, crec["reads"])
    D = {}
    for c in "abc":
        for p in ("1", "2"):
            moves = [r["ports"][p]["move_mV"] for r in crows if r["cell"] == c and r["read"] == "joint dose"]
            D[f"{c}{p}"] = statistics.fmean(moves)
    slopes = {}
    for key, (cell, read, ports) in DECK.items():
        mine = sorted((r for r in crows if r["cell"] == cell and r["read"] == read), key=lambda r: r["stage"])
        u = lambda r: statistics.fmean(r["ports"][p]["u_before_mV"] for p in ports)
        fired = [(u(r), r["latency"]) for r in mine if r["fire"]]
        first = next(r for r in mine if r["fire"])
        pts = sorted(fired, reverse=True)
        s1 = secant(fired, u(first))
        s2 = (pts[2][1] - pts[1][1]) / (pts[2][0] - pts[1][0]) if len(pts) >= 3 else None
        slopes[key] = dict(need=first["stage"], firing_stages=[r["stage"] for r in mine if r["fire"]], latencies=[r["latency"] for r in mine if r["fire"]],
                           slope_per_mV=s1, slope_one_stage_further_per_mV=s2, slope_three_points_per_mV=None if s2 is None else 1.5 * s1 - 0.5 * s2,
                           dose_mV=statistics.fmean(D[f"{cell}{p}"] for p in ports))

    qrec, qrows, qwords = rows_of(cfg["quiet"])
    qby = {r["slot"]: r for r in qrows}
    qlat = {k: [] for k in KINDS}
    ladder = {k: [] for k in KINDS}                          # the quiet run's silent training reads, in order
    for x in qrows:
        for c, r in x["reads"].items():
            k = kind_of(x, c, r)
            if k and r["fire"]:
                qlat[k].append(r["latency"])
            if k and not r["fire"] and ((x["stage"] == "layer 1" and c in "ab") or (x["stage"] == "layer 2" and c == "c")):
                ladder[k].append(r["q_peak"])
    steps = {k: [v[i + 1] - v[i] for i in range(len(v) - 1)] for k, v in ladder.items()}
    word_key = dict(a="a1", b="b1", c1="c1", c2="c2")

    runs, m5, doses, flips, fingerprints = [], [], [], [], {}
    score, level = {"pair": {}, "line": {}}, {"pair": {}, "line": {}}
    for d in cfg["noisy"]:
        rec, rows, words = rows_of(d)
        assert rec["needs"] == qrec["needs"], "a noisy run and its quiet run must have the same needs"
        rid = rec["id"]
        fingerprints[rid] = rec["noise_fingerprint"]
        same_word = {k: words["words"][word_key[k]] == qwords["words"][word_key[k]] for k in KINDS}
        runs.append(dict(id=rid, noise_seed=rec["noise"].get("noise_seed"), reached_its_last_date=rec["reached_its_last_date"], wall_s=rec["wall_s"],
                         words=words["words"], same_word_as_quiet=same_word, tests_equal_quiet=words["tests"] == qwords["tests"]))
        lat = {k: [] for k in KINDS}
        seen = {k: 0 for k in KINDS}
        for x in rows:
            q = qby.get(x["slot"])
            assert q is not None and q["stage"] == x["stage"] and q.get("pattern") == x.get("pattern") and q.get("line") == x.get("line"), f"slot mismatch {rid} {x['slot']}"
            for c, r in x["reads"].items():
                qr = q["reads"].get(c)
                if qr is None:
                    continue
                k = kind_of(x, c, r)
                training = (x["stage"] == "layer 1" and c in "ab") or (x["stage"] == "layer 2" and c == "c")
                idx = None
                if k and training:
                    idx = seen[k]
                    seen[k] += 1
                if r["fire"] != qr["fire"]:
                    flips.append(dict(run=rid, slot=x["slot"], stage=x["stage"], cell=c, kind=k, fire_noisy=r["fire"], fire_quiet=qr["fire"],
                                      q_peak_noisy=r["q_peak"], q_peak_quiet=qr["q_peak"]))
                    continue
                for p in ("1", "2"):
                    if r["ports"][p]["writes"] == 1 and qr["ports"][p]["writes"] == 1:
                        doses.append(dict(run=rid, cell=c, port=p, slot=x["slot"], d_mV=r["ports"][p]["move_mV"] - qr["ports"][p]["move_mV"]))
                if k is None:
                    continue
                group = "pair" if k in "ab" else "line"
                if r["fire"]:
                    lat[k].append(r["latency"])
                    if steps[k]:
                        level[group].setdefault((rid, k), []).append((r["q_peak_before_fire"] - qr["q_peak_before_fire"]) / steps[k][-1])
                elif training and steps[k]:
                    st = steps[k][idx] if idx < len(steps[k]) else steps[k][-1]
                    score[group].setdefault((rid, k), []).append((r["q_peak"] - qr["q_peak"]) / st)
        for k in KINDS:
            if same_word[k] and len(lat[k]) >= 3 and qlat[k]:
                off, wit = statistics.median(qlat[k]) - statistics.mean(lat[k]), statistics.stdev(lat[k])
                s1, s3 = slopes[k]["slope_per_mV"], slopes[k]["slope_three_points_per_mV"]
                m5.append(dict(run=rid, kind=k, fires=len(lat[k]), offset_units=off, within_sd_units=wit, offset_mV=off / s1, within_sd_mV=wit / s1,
                               offset_stages=off / s1 / slopes[k]["dose_mV"], within_sd_stages=wit / s1 / slopes[k]["dose_mV"],
                               offset_mV_three_points=None if s3 is None else off / s3, within_sd_mV_three_points=None if s3 is None else wit / s3))

    def cut(rows_):
        if not rows_:
            return dict(port_runs=0)
        out = dict(port_runs=len(rows_), b_mV=rms([r["offset_mV"] for r in rows_]), w_mV=rms([r["within_sd_mV"] for r in rows_]),
                   mean_offset_mV=statistics.fmean(r["offset_mV"] for r in rows_),
                   b_units=rms([r["offset_units"] for r in rows_]), w_units=rms([r["within_sd_units"] for r in rows_]),
                   b_stages=rms([r["offset_stages"] for r in rows_]), w_stages=rms([r["within_sd_stages"] for r in rows_]),
                   offset_over_within=rms([r["offset_units"] for r in rows_]) / rms([r["within_sd_units"] for r in rows_]))
        three = [r for r in rows_ if r["offset_mV_three_points"] is not None]
        if three:
            out.update(b_mV_three_points=rms([r["offset_mV_three_points"] for r in three]), w_mV_three_points=rms([r["within_sd_mV_three_points"] for r in three]))
        return out

    audit = {}
    for group in ("pair", "line"):
        sc, lv = split(score[group]), split(level[group])
        x = dict(score_of_silent_training_reads=sc, fire_level=lv)
        if sc and lv:
            x["run_offset_steps"] = math.sqrt(sc["between_corrected"] ** 2 + lv["between_corrected"] ** 2)
            x["within_run_steps"] = math.sqrt(sc["within_sd"] ** 2 + lv["within_sd"] ** 2)
            x["total_steps"] = math.sqrt(x["run_offset_steps"] ** 2 + x["within_run_steps"] ** 2)
            x["three_sigma_steps"] = 3 * x["total_steps"]
        audit[group] = x
    line_dose = statistics.fmean(slopes[k]["dose_mV"] for k in ("c1", "c2"))
    if "total_steps" in audit["line"]:
        audit["line"]["in_mV_of_one_port"] = dict(dose_mV=line_dose, run_offset=audit["line"]["run_offset_steps"] * line_dose,
                                                  within_run=audit["line"]["within_run_steps"] * line_dose, total=audit["line"]["total_steps"] * line_dose)
    distinct = len(set(fingerprints.values())) == len(fingerprints) and qrec["noise_fingerprint"] not in fingerprints.values()
    own = {k: dict(fires=len(v), sd_units=statistics.stdev(v), sd_mV=statistics.stdev(v) / slopes[k]["slope_per_mV"]) for k, v in qlat.items() if len(v) >= 3}
    return dict(label=label, needs=qrec["needs"], doses_mV=D, slopes=slopes,
                quiet=dict(id=qrec["id"], words=qwords["words"], noise_fingerprint=qrec["noise_fingerprint"], scatter_of_its_own_fire_latencies=own),
                runs=runs, noise_fingerprints=fingerprints, fingerprints_all_distinct_and_not_the_quiet_one=distinct,
                fire_bits_that_differ_from_quiet=flips,
                campaign_3=dict(pair=cut([r for r in m5 if r["kind"] in "ab"]), line=cut([r for r in m5 if r["kind"] in ("c1", "c2")]), all=cut(m5), rows=m5),
                d_mV=dict(n=len(doses), rms=rms([x["d_mV"] for x in doses]), max_abs=max((abs(x["d_mV"]) for x in doses), default=None)),
                audit_instrument=audit)


def verdict(one, two, slope=""):
    """G6 on campaign 3's definition, all kinds together, 2x against 1x. slope: "" for reading 1 (the secant, which
    governs), "_three_points" for reading 2 (beside it)."""
    out = {}
    for name, a, b in (("d", one["d_mV"]["rms"], two["d_mV"]["rms"]), ("w", one["campaign_3"]["all"].get(f"w_mV{slope}"), two["campaign_3"]["all"].get(f"w_mV{slope}")),
                       ("b", one["campaign_3"]["all"].get(f"b_mV{slope}"), two["campaign_3"]["all"].get(f"b_mV{slope}"))):
        out[name] = dict(at_1x_mV=a, at_2x_mV=b, ratio=None if not a or b is None else b / a)
    ratios = {k: v["ratio"] for k, v in out.items()}
    if any(v is None for v in ratios.values()):
        g6 = "not judged: a constant is missing"
    elif all(abs(v - 1) <= GO_WITHIN for v in ratios.values()):
        g6 = "go"
    elif ratios["w"] > 1 + STOP_ABOVE or ratios["b"] > 1 + STOP_ABOVE:
        g6 = "stop"
    else:
        g6 = "unclear"
    return dict(constants=out, G6=g6, rule="go: d, w and b each within 25 % of the 1x value; stop: w or b more than 60 % above its 1x value; otherwise unclear")


if __name__ == "__main__":
    repo, config, dest = sys.argv[1:4]
    dosedev.repo_paths(repo)
    import measure
    import plans4
    import reads4
    cfg = json.loads(Path(config).read_text())
    res = {label: one_dose((measure, plans4, reads4), label, c) for label, c in cfg["doses"].items()}
    if any(not v["fingerprints_all_distinct_and_not_the_quiet_one"] for v in res.values()):
        res["G6"] = dict(G6="not judged: noise fingerprints")
        Path(dest).write_text(json.dumps(res, indent=1) + "\n")
        print(json.dumps(res, indent=1))
        raise SystemExit(0)
    if "1x" in res and "2x" in res:
        res["G6"] = verdict(res["1x"], res["2x"])
        other = verdict(res["1x"], res["2x"], "_three_points")
        res["G6"]["beside, all kinds, three-point slope"] = dict(constants=other["constants"], G6_if_it_governed=other["G6"])
        res["G6"]["the verdict depends on the slope"] = other["G6"] != res["G6"]["G6"]
        res["G6"]["beside, all kinds, no slope and in stages"] = {
            label: {k: res[label]["campaign_3"]["all"].get(k) for k in ("port_runs", "b_units", "w_units", "b_stages", "w_stages")} for label in ("1x", "2x")}
        for which in ("pair", "line"):                       # beside the verdict: by kind, the two other readings
            res["G6"][f"beside, {which}"] = {
                label: dict(campaign_3={k: res[label]["campaign_3"][which].get(k) for k in ("port_runs", "b_mV", "w_mV", "b_mV_three_points", "w_mV_three_points", "b_units", "w_units", "b_stages", "w_stages", "offset_over_within")},
                            audit_instrument={k: res[label]["audit_instrument"][which].get(k) for k in ("run_offset_steps", "within_run_steps", "total_steps", "three_sigma_steps", "in_mV_of_one_port")})
                for label in ("1x", "2x")}
    Path(dest).write_text(json.dumps(res, indent=1) + "\n")
    print(json.dumps({k: (v if k == "G6" else dict(needs=v["needs"], runs=len(v["runs"]), flips=len(v["fire_bits_that_differ_from_quiet"]),
                                                     fingerprints_ok=v["fingerprints_all_distinct_and_not_the_quiet_one"], d_mV=v["d_mV"],
                                                     campaign_3={a: {x: y for x, y in b.items()} for a, b in v["campaign_3"].items() if a != "rows"}))
                      for k, v in res.items()}, indent=1))
