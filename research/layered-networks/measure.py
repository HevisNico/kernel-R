"""From record.json: every quantity the Lean chain needs, the checks in Python, and the trace data for the Lean file.

Dates become exact fractions of a time unit (ns / 20000). Per layer l:
  s(l)      the read start (T + offset(l)), skew(l), deadline(l), duration(l): design constants (spec.timing);
  dmin, dmax  the intrinsic delay, emission - max(read start, last arrival), least and largest over every read of the
            layer that emitted (tests and lessons together; also reported apart);
  lambda_max = skew + dmax (latency_of_intrinsic), lambda_min = dmin.
Layer 0: the external window w (no front end), or the front end: emit_early, emit_late, window, the measured
inverter emission offsets and the direct-rail lag. Wire delay delta on every port.

The chain (ChainDates with e = latencyLow dmin, f = latencyHigh w (skew + dmax)) is checked on the constants; the
trace premises (Scheduled, IntrinsicDelays, ExternalWindow or LayeredFront, Latencies) on every test and lesson.
Each Python check mirrors one Lean checker; the Lean file asserts the Python value, so it compiles only if the kernel
agrees.
"""
from fractions import Fraction as F
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import spec as specmod  # noqa: E402


def tu(ns, tu_ns=20000):
    return None if ns is None else F(ns, tu_ns)


class Measure:
    def __init__(self, s, cfg, rec):
        self.s, self.cfg, self.rec = s, cfg, rec
        self.tim = specmod.timing(s, cfg)
        self.L = len(s["layers"])
        self.tu_ns = round(cfg["stimulus"]["tu_s"] * 1e9)
        self.slots = rec["slots"]

    def d(self, ns):
        return tu(ns, self.tu_ns)

    def sched(self, slot):
        T = self.d(slot["T"])
        return {k: T + v for k, v in self.tim["offset"].items()}

    # ----------------------------------------------------------- reads in Lean form

    def read_of(self, slot, k, i):
        for r in slot["reads"]:
            if r["layer"] == k and r["index"] == i:
                return dict(start=self.d(r["start"]), arrivals=[self.d(a) for a in r["arrivals"]],
                            emissions=[self.d(r["emission"])] + ([self.d(r["second"])] if r["second"] else [])
                            if r["emission"] is not None else [],
                            latch=self.d(r["latch"]), second=r["second"])
        return None

    def trace(self, slot, top):
        """Layers 1..top of a slot as lists of reads (a cell absent from the slot: an empty read at its start)."""
        sc = self.sched(slot)
        out = []
        for k in range(1, top + 1):
            row = []
            for i in range(len(self.s["layers"][k - 1])):
                r = self.read_of(slot, k, i)
                row.append(r or dict(start=sc[k], arrivals=[None, None], emissions=[], latch=None, second=None))
            out.append(row)
        return out

    def lines(self, slot):
        return [self.d(t) for t in slot["lines"]]

    def inverters(self, slot):
        return [dict(start=self.d(v["start"]), arrival=self.d(v["arrival"]),
                     emissions=[] if v["emission"] is None else [self.d(v["emission"])] + ([self.d(v["second"])] if v["second"] else []),
                     latch=self.d(v["latch"])) for v in slot["inv"]]

    def tests(self):
        return [self.slots[j] for j in self.rec["tests"]]

    def lessons(self):
        """{(layer, cell, group, round): slot}, keeping per cell only rounds 0..maxWrites (maxWrites + 1 = the least
        number of rounds over its active groups)."""
        rounds = {}
        for x in self.rec["lessons"]:
            rounds.setdefault((x["layer"], x["cell"]), {}).setdefault(x["group"], []).append(x)
        out, maxw = {}, {}
        for (k, i), groups in rounds.items():
            n = min(len(v) for v in groups.values())
            maxw[(k, i)] = n - 1
            for g, xs in groups.items():
                for x in xs[:n]:
                    out[(k, i, g, x["round"])] = self.slots[x["slot"]]
        return out, maxw

    # ----------------------------------------------------------- quantities

    def intrinsic(self):
        per = {k: dict(test=[], lesson=[]) for k in range(1, self.L + 1)}

        def add(kind, slot, top):
            for k, row in enumerate(self.trace(slot, top), start=1):
                for r in row:
                    if r["emissions"]:
                        ref = max([r["start"]] + [a for a in r["arrivals"] if a is not None])
                        per[k][kind].append(r["emissions"][0] - ref)
        for t in self.tests():
            add("test", t, self.L)
        lessons, _ = self.lessons()
        for (k, i, g, r), slot in lessons.items():
            add("lesson", slot, k)
        q = {}
        for k, v in per.items():
            allv = v["test"] + v["lesson"]
            q[k] = dict(dmin=min(allv) if allv else F(0), dmax=max(allv) if allv else F(0), n=len(allv),
                        test=(min(v["test"]), max(v["test"])) if v["test"] else None,
                        lesson=(min(v["lesson"]), max(v["lesson"])) if v["lesson"] else None)
        return q

    def quantities(self):
        q = self.intrinsic()
        tim = self.tim
        dmin = {k: q[k]["dmin"] for k in q}
        dmax = {k: q[k]["dmax"] for k in q}
        lmax = {k: tim["skew"][k] + dmax[k] for k in q}
        out = dict(layers={}, wire_delay=tim["delta"], w=tim["w"], offsets=tim["offset"])
        for k in q:
            out["layers"][k] = dict(offset=tim["offset"][k], skew=tim["skew"][k], deadline=tim["deadline"][k],
                                    duration=tim["duration"][k], dmin=dmin[k], dmax=dmax[k], lambda_min=dmin[k],
                                    lambda_max=lmax[k], reads_emitted=q[k]["n"], test_range=q[k]["test"],
                                    lesson_range=q[k]["lesson"])
        if self.s["front"]:
            em, lag = [], []
            slots = self.tests() + list(self.lessons()[0].values())
            for sl in slots:
                T = self.d(sl["T"])
                for v in self.inverters(sl):
                    if v["emissions"]:
                        em.append(v["emissions"][0] - T)
                for j, t in enumerate(self.lines(sl)[:self.s["m"]]):
                    if t is not None:
                        lag.append(t - T)
            out["front"] = dict(emit_early=tim["emit_early"], emit_late=tim["emit_late"], window=tim["inverter_window"],
                                inverter_emission_offsets=(min(em), max(em)) if em else None,
                                direct_rail_lag=(min(lag), max(lag)) if lag else None)
        return out, dmin, dmax

    # ----------------------------------------------------------- the checks (each mirrors a Lean checker)

    def chain(self, dmin, dmax):
        """checkChainDates s (latencyLow dmin) (latencyHigh w (skew + dmax)): per wired port of layer k + 1."""
        tim, res = self.tim, []
        s = tim["offset"]
        e = {0: F(0), **dmin}
        f = {0: tim["w"], **{k: tim["skew"][k] + dmax[k] for k in dmax}}
        for k in range(self.L):
            for i, n in enumerate(self.s["layers"][k]):
                for a in range(2):
                    if n["source"][a] is None:
                        continue
                    lo = s[k + 1] <= s[k] + e[k] + tim["delta"]
                    hi = s[k] + f[k] + tim["delta"] <= s[k + 1] + tim["skew"][k + 1]
                    res.append(dict(layer=k + 1, cell=i, port=a, start_ok=lo, skew_ok=hi,
                                    margin_skew=s[k + 1] + tim["skew"][k + 1] - (s[k] + f[k] + tim["delta"])))
        return all(r["start_ok"] and r["skew_ok"] for r in res), res

    def read_checks(self, slot, top, dmin, dmax):
        """Scheduled, IntrinsicDelays, Latencies (lambda = dmin, skew + dmax), arrival windows, decoder clause
        (one emission, after every arrival, by the deadline), routing (arrival = emission below + delta)."""
        tim, sc = self.tim, self.sched(slot)
        ok = dict(scheduled=True, intrinsic=True, latency=True, window=True, decoder=True, routed=True)
        rows = self.trace(slot, top)
        below = self.lines(slot)
        # PulseWindows of the replay (layers below top), e = latencyLow dmin, f = latencyHigh w (skew + dmax)
        ok["pulses"] = all(t is None or sc[0] <= t <= sc[0] + tim["w"] for t in below) and all(
            not r["emissions"] or sc[k] + dmin[k] <= r["emissions"][0] <= sc[k] + tim["skew"][k] + dmax[k]
            for k, row in enumerate(rows[:-1], start=1) for r in row)
        for k, row in enumerate(rows, start=1):
            for i, r in enumerate(row):
                n = self.s["layers"][k - 1][i]
                ok["scheduled"] &= r["start"] == sc[k]
                arr = [a for a in r["arrivals"] if a is not None]
                for t in r["emissions"]:
                    ref = max([r["start"]] + arr)
                    ok["intrinsic"] &= ref + dmin[k] <= t <= ref + dmax[k]
                    ok["latency"] &= r["start"] + dmin[k] <= t <= r["start"] + tim["skew"][k] + dmax[k]
                ok["window"] &= all(r["start"] <= a <= r["start"] + tim["skew"][k] for a in arr)
                ok["decoder"] &= len(r["emissions"]) <= 1 and all(
                    r["start"] <= t <= r["start"] + tim["deadline"][k] and all(a <= t for a in arr) for t in r["emissions"])
                for a in range(2):
                    src = n["source"][a]
                    want = None if src is None or below[src] is None else below[src] + tim["delta"]
                    ok["routed"] &= r["arrivals"][a] == want
            below = [r["emissions"][0] if r["emissions"] else None for r in row]
        return ok

    def front_checks(self, slot, x):
        """checkLayeredFront (each inverter: start, input, InverterRead; the lines = frontArrival) and the
        external pattern; or checkExternalWindow without a front end."""
        tim, T, m = self.tim, self.d(slot["T"]), self.s["m"]
        lines = self.lines(slot)
        if not self.s["front"]:
            s0 = self.sched(slot)[0]
            return dict(external_window=all(t is None or s0 <= t <= s0 + tim["w"] for t in lines),
                        realised=all((t is not None) == b for t, b in zip(lines, x)))
        ok = dict(front=True, realised=True)
        e, l, win = tim["emit_early"], tim["emit_late"], tim["inverter_window"]
        for j, v in enumerate(self.inverters(slot)):
            ext = T if x[j] else None
            ok["realised"] &= (ext is not None) == x[j]
            good = v["start"] == T and v["arrival"] == ext and 0 <= win <= e < l
            good &= v["arrival"] is None or T <= v["arrival"] <= T + win
            good &= len(v["emissions"]) <= 1 and all(T + e < t <= T + l for t in v["emissions"])
            good &= bool(v["emissions"]) == (not x[j])
            good &= lines[j] == (None if ext is None else ext + e)
            good &= lines[m + j] == (v["emissions"][0] if v["emissions"] else None)
            ok["front"] &= good
        return ok

    def report(self):
        s, rec = self.s, self.rec
        qty, dmin, dmax = self.quantities()
        chain_ok, chain_rows = self.chain(dmin, dmax)
        tests = []
        for x, slot in zip(specmod.patterns(s["m"]), self.tests()):
            rows = self.trace(slot, self.L)
            pred = specmod.predict_layers(s, specmod.rails(s, x))
            seen = [tuple(bool(r["emissions"]) for r in row) for row in rows]
            tests.append(dict(pattern="".join(str(int(b)) for b in x), out=seen[-1][0], expected=s["expect"][specmod.code(x)],
                              cells_as_predicted=seen == pred, **self.read_checks(slot, self.L, dmin, dmax),
                              **self.front_checks(slot, x)))
        lessons, maxw = self.lessons()
        les = []
        for (k, i, g, r), slot in sorted(lessons.items()):
            n = s["layers"][k - 1][i]
            x = specmod.input_of_lines(s, specmod.line_pattern(s, n["stimulus"][g]))
            les.append(dict(layer=k, cell=i, group=g, round=r, **self.read_checks(slot, k, dmin, dmax), **self.front_checks(slot, x)))
        keys = lambda rows: sorted({k for r in rows for k, v in r.items() if isinstance(v, bool) and k not in ("out", "expected")})
        summary = dict(
            chain=chain_ok,
            outputs=all(t["out"] == t["expected"] for t in tests),
            tests={k: all(t[k] for t in tests) for k in keys(tests)},
            lessons={k: all(t[k] for t in les) for k in keys(les)},
            words=rec["words"], maxWrites={f"{k}/{i}": v for (k, i), v in maxw.items()})
        return dict(quantities=qty, chain=chain_rows, tests=tests, summary=summary), dmin, dmax, lessons, maxw


def fr(x):
    if isinstance(x, F):
        return str(x) if x.denominator == 1 else f"{x.numerator}/{x.denominator}"
    if isinstance(x, (list, tuple)):
        return [fr(v) for v in x]
    if isinstance(x, dict):
        return {str(k): fr(v) for k, v in x.items()}
    return x


def main(spec_path, out):
    cfg = json.loads((HERE / "config.json").read_text())
    s = specmod.load(spec_path)
    rec = json.loads((Path(out) / "record.json").read_text())
    rep = Measure(s, cfg, rec).report()[0]
    (Path(out) / "measure.json").write_text(json.dumps(fr(rep), indent=1) + "\n")
    print(json.dumps(fr(rep["summary"]), indent=1))
    print(json.dumps(fr(rep["quantities"]), indent=1))


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
