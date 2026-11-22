"""The family campaign's declared comparisons and H (PREDICTION.md 5.3 and 5.7): campaign 5's M1 to M8 and h_check
(analyze.py, as campaign 6 ran it unchanged), re-expressed per member: its own cells, ports, lines and 2^M patterns.
New code. None of it decides a claim. Where a comparison has no meaning for a member, or has no data, the output says
so in a string that starts with "no meaning" or "no data" or "not computed", and nothing is put in its place.

Input, per counted run (analysis.py's run record), beyond words, tests and skew:
  rows:        the reads of the run, reads4.network_reads' form: [{slot, stage ("layer 1" | "layer 2" | "test" |
               "skew control"), date, pattern, reads: {cell: read}}], read = {fire, latency, start_s, gated, late_fires,
               ports: {"1"|"2": {writes, writes_prime, u_before_mV, move_mV, rises: [{rise_s, width_s}]}}, and for c:
               arrivals: [{port, date_s, fire_date_s}], skew_units, q_peak, fire_date_s}
  result:      the run's evidence/result.json (occurrences [{cell, port, date_s, delivered}], fires [{cell, date_s}],
               still_queued_at_the_horizon)
  words_prime: the words with write' in place of write (reads4.words(rows, prime=True)["words"]), noisy runs
  observation: the run's observation in family_predict.observation's serialized form (M8; its scores may hold only the
               observed mask of each test, the other submasks are taken from the prediction, as campaign 5's
               run_observation did)
A missing field gives "no data" for the comparisons that need it, never an error.
"""
from fractions import Fraction
import math
import statistics

import campaign_common as CC

LINE_PORT = dict(a=1, b=2)                           # family_predict.LINE_PORT
WINDOW, DEADLINE_C, SKEW_C, WRITE_PRIME_S = 1.1, 2.2, 1.1, 1e-6     # c4.WINDOW, c4.DEADLINE_C, c4.SKEW_C, c4.WRITE_PRIME_S
TU_S = Fraction(1, 50000)                            # the time unit, 20 us
NOMINAL_NEED = 4                                     # campaign 5's M4: dnf.zero_error(4, 4, 4, 4), pair cells and lines


def terms(member):
    import family_predict as FP
    return FP.MEMBERS[member]["terms"]


def cells(member):
    return list(CC.KINDS[member])


def pattern_set(key):
    return set() if key == "-" else set(key)


def truth(member, key):
    """The member's cells on a test pattern: each first-layer cell fires on the patterns containing its term, c on f."""
    x = pattern_set(key)
    out = {c: set(t) <= x for c, t in terms(member).items()}
    out["c"] = any(out.values())
    return out


def learning_ports(x):
    import campaign_predict as CP
    return CP.ports_of(x["member"], x["unary_ports"] or {})


def need_of(x, port):
    return x["needs"][port] if port.startswith("c") else x["needs"][port[0]]


def exact(v):
    """A date at its exact value: a float's binary value, or the rational a string encodes."""
    return Fraction(v)


# ------------------------------------------------------------------------------------------------ the comparisons

def M1(inst, noisy):
    """Outputs of a noisy run that count for no claim, observed. By O6 every noisy run is on an instance where every
    cell has room at K = 3, so every output counts and the list is empty by construction; it is still computed."""
    out = {m: [] for m in CC.MEMBERS}
    for rid, (r, w) in noisy.items():
        x = inst[(r["seed"], r["member"])]
        if x["room_K3"]:
            continue
        for k, v in w["tests"].items():
            for c, f in v.items():
                out[r["member"]].append(dict(run=rid, pattern=k, cell=c, output=f, why="the instance has no room at K = 3"))
    return {m: (v if v else "no data: every noisy run of this member is on an instance with room (O6), every output counts")
            for m, v in out.items()}


def M2(predicted):
    bad = [r["id"] for r in predicted["network_runs"]
           if not next(x for x in predicted["instances"] if (x["seed"], x["member"]) == (r["seed"], r["member"]))["eligible"]]
    return dict(note="no data: no network run is made on an instance that is not eligible (section 5.7)",
                runs_on_instances_not_eligible=bad)


def M3(every):
    """Latencies of every FIRE (layer 1: from the start of the read; c: from its first arrival) and c's arrival skews,
    against the decision window, c's deadline and the skew bound. A member whose c has one line has no skew."""
    out = {}
    for rid, (r, w) in every.items():
        m = r["member"]
        if w.get("rows") is None:
            out[rid] = "no data: the run record has no rows"
            continue
        lat = {c: [] for c in cells(m) + ["c"]}
        skews = []
        for y in w["rows"]:
            for c, rd in y["reads"].items():
                if rd.get("fire") and c in lat:
                    lat[c].append(dict(slot=y["slot"], latency=rd["latency"]))
                if c == "c" and len(cells(m)) == 2:
                    skews.append(dict(slot=y["slot"], skew=rd.get("skew_units")))
        row = dict(member=m, max_latency={c: max((v["latency"] for v in L), default=None) for c, L in lat.items()},
                   latencies=lat, bounds=dict(window=WINDOW, deadline_c=DEADLINE_C, skew=SKEW_C))
        if len(cells(m)) == 2:
            row.update(max_skew=max((v["skew"] for v in skews if v["skew"] is not None), default=None), skews=skews)
        else:
            row["skews"] = f"no meaning for {m}: c has one line, so no arrival skew"
        out[rid] = row
    return out


def nominal(x):
    """Campaign 5's nominal predictor generalised [reading of this code]: need 4 on every pair cell's port and every
    line, over the instance's own calendar (the predicted word's length), and the member's truth table. A unary cell
    has no nominal need in campaign 5 or 6: its ports get no nominal word."""
    m = x["member"]
    words = {}
    for p, w in x["predicted"]["words"].items():
        if not p.startswith("c") and CC.KINDS[m][p[0]] == "unary":
            words[p] = f"no meaning for {m}: no nominal need is defined for a unary cell"
        else:
            words[p] = ("s" * NOMINAL_NEED + "F" * len(w))[:len(w)]
    return dict(words=words, tests={k: truth(m, k) for k in x["predicted"]["tests"]})


def M4(inst, quiet):
    """The nominal predictor against the measured predictor and against the run without noise: letters and outputs
    where they differ."""
    out = {}
    for key, x in sorted(inst.items()):
        if not x.get("measured") or not x.get("predicted"):
            continue
        nom = nominal(x)

        def diff(a, b):
            res = []
            for p, u in a.items():
                if isinstance(u, str) and u.startswith("no meaning"):
                    continue
                v = b.get(p)
                if v is None:
                    res.append(dict(port=p, other=None))
                    continue
                res += [dict(port=p, i=i, nominal=s, other=t) for i, (s, t) in enumerate(zip(u, v)) if s != t]
                if len(u) != len(v):
                    res.append(dict(port=p, length=(len(u), len(v))))
            return res
        tdiff = lambda t: [dict(pattern=k, cell=c) for k, v in nom["tests"].items() for c, f in v.items() if t.get(k, {}).get(c) != f]
        row = dict(member=x["member"], nominal_words=nom["words"], words_vs_measured=diff(nom["words"], x["predicted"]["words"]),
                   tests_vs_measured=tdiff(x["predicted"]["tests"]))
        if key in quiet:
            w = quiet[key][1]
            row["words_vs_run"] = diff(nom["words"], w["words"])
            row["tests_vs_run"] = tdiff(w["tests"])
        else:
            row["vs_run"] = "no data: no counted run without noise on this instance"
        out[f"{key[0]}-{key[1]}"] = row
    return out


def M5(inst):
    return {f"{s}-{m}": "not computed: the frozen family_predict.py computes no validation residual of the geometric fits"
            for (s, m) in sorted(inst)}


def M6(every, noisy):
    """Every write-signal crossing narrower than a write' (1 us), with its date in the cycle and its width; per
    port-run of the noisy runs, whether its word and its word' differ."""
    narrow, differ = {}, {}
    for rid, (r, w) in every.items():
        if w.get("rows") is None:
            narrow[rid] = "no data: the run record has no rows"
            continue
        for y in w["rows"]:
            for c, rd in y["reads"].items():
                for p, v in rd.get("ports", {}).items():
                    for rise in v.get("rises", []):
                        if rise["width_s"] < WRITE_PRIME_S:
                            narrow.setdefault(rid, []).append(dict(slot=y["slot"], cell=c, port=p, width_s=rise["width_s"],
                                                                   date_in_cycle_s=rise["rise_s"] - rd["start_s"]))
    for rid, (r, w) in noisy.items():
        wp = w.get("words_prime")
        if wp is None:
            differ[rid] = "no data: the run record has no words_prime"
            continue
        differ[rid] = {p: dict(word=w["words"].get(p), word_prime=wp.get(p)) for p in w["words"] if w["words"].get(p) != wp.get(p)}
    return dict(narrow_crossings=narrow, word_and_word_prime_differ=differ)


def M7(inst, noisy, const):
    """Per instance and learning port, over its noisy runs: the spread of the stored voltage at the end of its
    training (u before its first read after training: the first layer-2 slot that reads the cell, for a first-layer
    cell; the first test slot that reads c, for a line), and of the FIRE latency of its first F, against the model's
    sigma sqrt(w^2 + b^2 + n d^2) for the stored voltage, n the port's need. The model gives no latency spread."""
    by = {}
    for rid, (r, w) in noisy.items():
        x = inst[(r["seed"], r["member"])]
        if w.get("rows") is None:
            by.setdefault((r["seed"], r["member"]), {})["no_rows"] = by.get((r["seed"], r["member"]), {}).get("no_rows", []) + [rid]
            continue
        rows = w["rows"]
        for port in learning_ports(x):
            c, p = port[0], port[1]
            stage = "test" if c == "c" else "layer 2"
            y = next((y for y in rows if y["stage"] == stage and c in y["reads"]), None)
            first_f = None
            for z in rows:
                rd = z["reads"].get(c)
                if not rd or not rd.get("fire"):
                    continue
                if c != "c" and z["stage"] == "layer 1":
                    first_f = rd["latency"]
                    break
                if c == "c" and z["stage"] == "layer 2" and {a["port"] for a in rd.get("arrivals", [])} == {int(p)}:
                    first_f = rd["latency"]
                    break
            d = by.setdefault((r["seed"], r["member"]), {}).setdefault(port, dict(u_end_mV=[], first_F_latency=[]))
            if y is not None:
                d["u_end_mV"].append(y["reads"][c]["ports"][p]["u_before_mV"])
            if first_f is not None:
                d["first_F_latency"].append(first_f)
    sd = lambda v: statistics.pstdev(v) if len(v) > 1 else None
    out = {}
    for (s, m), ports in sorted(by.items()):
        x = inst[(s, m)]
        row = {}
        for port, d in ports.items():
            if port == "no_rows":
                row["runs_without_rows"] = d
                continue
            n = need_of(x, port)
            sigma = "no data: the record has no constants" if not const else \
                math.sqrt(const["within_mV"] ** 2 + const["between_mV"] ** 2 + n * const["per_dose_mV"] ** 2)
            row[port] = dict(runs=len(d["u_end_mV"]), u_end_mV=d["u_end_mV"], u_end_spread_mV=sd(d["u_end_mV"]), model_sigma_mV=sigma,
                             first_F_latency=d["first_F_latency"], first_F_latency_spread=sd(d["first_F_latency"]))
        out[f"{s}-{m}"] = row
    return out


def assumption_on_c(x, w):
    """M8's declared assumption on c, per member with two lines and n_c1 != n_c2: the run's FIRE latency of c on each
    line alone at test (the pattern that is exactly that cell's term) against the latency of the predicted observation,
    and the run's peak q of c's empty test read against the predicted scores."""
    m = x["member"]
    if len(cells(m)) == 1:
        return f"no meaning for {m}: c has one line"
    if x["needs"]["c1"] == x["needs"]["c2"]:
        return None
    if w.get("rows") is None:
        return "no data: the run record has no rows"
    t = {("".join(sorted(y["pattern"])) or "-"): y for y in w["rows"] if y["stage"] == "test"}
    po = x["observation"]["secondTest"]
    lat = lambda k: (lambda rd: rd["latency"] if rd and rd.get("fire") else None)(t[k]["reads"].get("c")) if k in t else None
    pred = lambda k: float(exact(po[k]["emissions"][0]) - exact(po[k]["start"])) if po[k]["emissions"] else None
    out = {}
    for c, term in terms(m).items():
        k = "".join(sorted(term))
        out[f"line_{c}_alone"] = dict(pattern=k, run=lat(k), calibration=pred(k))
    e = t.get("-", {}).get("reads", {}).get("c")
    out["empty"] = dict(run_q_peak=None if e is None else e.get("q_peak"), calibration_scores=x["observation"]["scores"]["-"])
    return out


def run_instance(x, o):
    """The instance with the run's observation; the scores of the submasks the run did not observe come from the
    prediction (campaign 5's run_observation)."""
    o = dict(o, scores={k: {**x["observation"]["scores"][k], **o.get("scores", {}).get(k, {})} for k in x["observation"]["scores"]})
    return dict(x, observation=o)


def M8(inst, quiet, gate=None):
    """The checkers on the run's observation, per counted run without noise of an eligible instance: the generator's
    mirror on the spec of the instance with the run's observation (family_predict.raw_spec, spec.load,
    mirror_verdicts); with gate = dict(out_dir, gen, lean, build), the kernel too (family_predict.lean_gate). And the
    declared assumption on c. gate None: the mirror only, and the output says the kernel was not run."""
    import family_predict as FP
    out = {}
    for key, (r, w) in sorted(quiet.items()):
        x = inst[key]
        row = dict(member=x["member"], assumption_on_c=assumption_on_c(x, w))
        if w.get("observation") is None:
            row["checkers"] = "no data: the run record has no observation"
            out[r["id"]] = row
            continue
        y = run_instance(x, w["observation"])
        _, _, spec, *_ = FP.mods()
        tag = f"{x['member']}_{x['seed']}_run"
        try:
            s = spec.load(FP.raw_spec(y, tag, f"comparisons.py M8, run {r['id']}"))
        except spec.SpecError as e:
            row["checkers"] = f"spec refused: {e}"
            out[r["id"]] = row
            continue
        mv = FP.mirror_verdicts(s)
        row["mirror"] = {K: dict(checks=v["checks"], per_checker=v["per_checker"], failing=v["failing"]) for K, v in mv.items()}
        if gate:
            g = FP.lean_gate(s, mv, gate["out_dir"], gate["gen"], gate["lean"], gate["build"])
            row["kernel"], row["kernel_agrees_with_mirror"] = g["kernel"], g.get("kernel_agrees_with_mirror")
        else:
            row["kernel"] = "not computed: no Lean gate was given"
        out[r["id"]] = row
    return out


def H(every):
    """Campaign 5's h_check per run, by the member's lines: separation (the smallest gap above 3 units between
    deliveries to each cell), late FIRE, routing (an arrival on c's port p comes from the cell of that line, 3/2 units
    after its FIRE, within 1/50), skews above the bound (two lines only), c firing before its last arrival, deliveries
    undelivered and still queued. Observed and reported, never refuting."""
    tol = Fraction(1, 10 ** 9)
    key = lambda s: round(exact(s), 12)
    out = {}
    for rid, (r, w) in every.items():
        m = r["member"]
        if w.get("rows") is None or w.get("result") is None:
            out[rid] = "no data: the run record has no rows or no result"
            continue
        res = w["result"]
        src = {LINE_PORT[c]: c for c in cells(m)}
        h = dict(member=m, min_separation_units={}, late_fires=0, arrivals_not_routed=0, c_fire_outside=0,
                 undelivered=sum(1 for o in res["occurrences"] if not o["delivered"]), queued=len(res.get("still_queued_at_the_horizon", [])))
        h["skews_above_bound"] = 0 if len(cells(m)) == 2 else f"no meaning for {m}: c has one line"
        for c in cells(m) + ["c"]:
            d = sorted({key(o["date_s"]) for o in res["occurrences"] if o["delivered"] and o["cell"] == c})
            gaps = [(b - a) / TU_S for a, b in zip(d, d[1:]) if (b - a) / TU_S > 3]
            h["min_separation_units"][c] = float(min(gaps)) if gaps else None
        fires = {(f["cell"], key(f["date_s"])) for f in res["fires"]}
        for y in w["rows"]:
            for c, rd in y["reads"].items():
                h["late_fires"] += rd.get("late_fires", 0)
            rd = y["reads"].get("c")
            if rd:
                for a in rd.get("arrivals", []):
                    s = src.get(a["port"])
                    ok = s is not None and a["fire_date_s"] is not None and (s, key(a["fire_date_s"])) in fires and \
                        abs((exact(a["date_s"]) - exact(a["fire_date_s"])) / TU_S - Fraction(3, 2)) <= Fraction(1, 50) + tol
                    h["arrivals_not_routed"] += not ok
                if len(cells(m)) == 2:
                    h["skews_above_bound"] += exact(rd["skew_units"]) > Fraction(11, 10) + tol
                if rd.get("fire") and rd.get("arrivals") and rd["fire_date_s"] < max(a["date_s"] for a in rd["arrivals"]):
                    h["c_fire_outside"] += 1
        out[rid] = h
    return out


def comparisons(predicted, runs, gate=None):
    """All of them, from PREDICTED.json and the counted runs (the same `counts` rule as analysis.py)."""
    inst = {(x["seed"], x["member"]): x for x in predicted["instances"]}
    ok = lambda r: runs.get(r["id"]) if runs.get(r["id"], {}).get("counts") else None
    quiet = {(r["seed"], r["member"]): (r, ok(r)) for r in predicted["network_runs"] if r["control"] == "skew" and ok(r)}
    noisy = {r["id"]: (r, ok(r)) for r in predicted["network_runs"] if r["noise"] != "none" and ok(r)}
    every = {v[0]["id"]: v for v in quiet.values()}
    every.update(noisy)
    per_member = lambda d: {m: {k: v for k, v in d.items() if (v.get("member") if isinstance(v, dict) else None) == m
                                or f"-{m}-" in f"-{k}-"} for m in CC.MEMBERS}
    return dict(M1=M1(inst, noisy), M2=M2(predicted), M3=per_member(M3(every)), M4=per_member(M4(inst, quiet)), M5=M5(inst),
                M6=M6(every, noisy), M7=per_member(M7(inst, noisy, predicted.get("constants"))),
                M8=per_member(M8(inst, quiet, gate)), H=per_member(H(every)))
