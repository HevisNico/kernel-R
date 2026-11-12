"""Decomposition of the per-write budget and the cumulative budget, by the rule of CUMULATIVE_PROTOCOL.md.

No simulation is run. Inputs: ../need_budget_ports.csv (d0, a, m, unchanged), ../results/mc_*.csv
(stored voltages of the original runs), local_summary.json (calibration at 27 C and the bounds measured
on the nominal replays) and level_summary.json (ell_static of cell 2064).

Writes cumulative_ports.csv, cumulative_summary.json and CUMULATIVE_RESULTS.md.
"""
import csv
import json
import statistics
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
DASH = "—"


def stored(run, port):
    """V(0) and the stored voltage after each write of the port, from the campaign CSV of the original run."""
    with (ROOT / "results" / f"{run}.csv").open(newline="") as fh:
        rows = list(csv.DictReader(fh))
    q = str(port)
    own = [r for r in rows if r["port"] == q]
    if not own:
        return None, []
    if port == 1:
        v0 = float(own[0]["vmem1"]) + float(own[0]["step1_mV"]) / 1000      # the read of the period at rest
    else:
        before = [r for r in rows if int(r["pulse"]) == int(own[0]["pulse"]) - 1]
        if not before:
            return None, []
        v0 = float(before[0]["vmem2"])
    return v0, [float(r[f"vmem{q}"]) for r in own if r["fired"] == "0"]


def main():
    local = json.loads((HERE / "local_summary.json").read_text())
    level = json.loads((HERE / "level_summary.json").read_text())
    fit = next(f for f in local["local_fit"] if f["temperature_C"] == 27)
    beta, eps = fit["beta_per_V"], fit["epsilon_per_V"]
    nom = local["windows"]["nominal_200ns_retry1"]["silent"]
    parts = dict(k_eta=nom["residual_log_gain_local"]["max"], sigma=nom["sensor_tolerance_local"]["max"],
                 linkage=nom["handoff_local"]["max"], calibration=nom["increment_error_bound_local"]["max"])
    b = sum(parts.values())
    with (ROOT / "need_budget_ports.csv").open(newline="") as fh:
        table = list(csv.DictReader(fh))
    out = []
    for p in table:
        row = dict(run=p["run"], port=int(p["port"]), observed_silent=p["observed_silent"], m=p["ceiling_count"], count_agrees=p["count_agrees"],
                   room_historical=p["room_proxy"])
        out.append(row)
        if not p["d0_proxy"] or not p["a_proxy"] or not p["ceiling_count"] or int(p["ceiling_count"]) == 0:
            row.update(per_write_status="not evaluable: a value is missing or m = 0", cumulative_status="not evaluable: a value is missing or m = 0")
            continue
        d0, a, m = float(p["d0_proxy"]), float(p["a_proxy"]), int(p["ceiling_count"])
        measured = p["run"] == level["cell"]
        ell = level["ell_static"] if measured else 0.0
        terms = {"a": a, "m*b": m * b, "(20/17)*ell": 20 / 17 * ell, "1/8000": 1 / 8000}
        b_max = (d0 / 2 - a - 20 / 17 * ell - 1 / 8000) / m
        row.update(d0=d0, half_d0=d0 / 2, a=a, ell=ell, ell_measured=measured, m_times_b=m * b, level_term=20 / 17 * ell,
                   per_write_room=d0 / 2 - sum(terms.values()), largest_term=max(terms, key=terms.get), b_max=b_max,
                   b_over_b_max=b / b_max if b_max > 0 else None, per_write_status="evaluated")
        # the cumulative budget
        v0, writes = stored(p["run"], int(p["port"]))
        row["writes"] = len(writes)
        if v0 is None or len(writes) < m:
            row["cumulative_status"] = f"not evaluable: the port made {len(writes)} writes, fewer than m"
            continue
        dev = [abs(beta * (v0 - writes[n - 1]) - n * d0) for n in range(1, m + 1)]
        cal = [eps * abs(v0 - writes[n - 1]) for n in range(1, m + 1)]
        big = max(range(m), key=lambda i: dev[i] + cal[i])
        room = d0 / 2 - a - (dev[big] + cal[big]) - 20 / 17 * ell - 1 / 8000
        agrees = p["count_agrees"] == "True"
        row.update(B=dev[big] + cal[big], B_at_n=big + 1, B_deviation=dev[big], B_calibration=cal[big], cumulative_room=room,
                   cumulative_status="outside the sufficient region" if room <= 0 else
                   "inside under estimates, count agrees" if agrees else "inside under estimates, count disagrees")
    fields = []
    for r in out:
        fields += [k for k in r if k not in fields]
    with (HERE / "cumulative_ports.csv").open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=fields, lineterminator="\n")
        w.writeheader(); w.writerows(out)

    ev = [r for r in out if r["per_write_status"] == "evaluated"]
    best = max(ev, key=lambda r: r["per_write_room"])
    finite = sorted(r["b_over_b_max"] for r in ev if r["b_over_b_max"] is not None)
    dominant = {}
    for r in ev:
        dominant[r["largest_term"]] = dominant.get(r["largest_term"], 0) + 1
    by_m = {}
    for r in ev:
        by_m.setdefault(int(r["m"]), []).append(r)
    status = {}
    for r in out:
        key = r["cumulative_status"].split(":")[0]
        status[key] = status.get(key, 0) + 1
    inside = [r for r in out if r["cumulative_status"].startswith("inside")]
    wrong = [r for r in inside if r["cumulative_status"].endswith("disagrees")]
    cum = [r for r in out if "cumulative_room" in r]
    cbest = max(cum, key=lambda r: r["cumulative_room"]) if cum else None
    S = dict(rule="CUMULATIVE_PROTOCOL.md", beta_per_V=beta, epsilon_per_V=eps, b_parts=parts, b=b, ports=len(out),
             per_write=dict(evaluated=len(ev), positive_room=sum(r["per_write_room"] > 0 for r in ev),
                            positive_room_count_disagrees=[f"{r['run']} port {r['port']}" for r in ev if r["per_write_room"] > 0 and r["count_agrees"] != "True"],
                            largest_term_counts=dominant,
                            closest=dict(run=best["run"], port=best["port"], room=best["per_write_room"], m=best["m"], a=best["a"],
                                         b_over_b_max=best["b_over_b_max"]),
                            median_b_over_b_max=statistics.median(finite) if finite else None,
                            ports_where_no_b_suffices=sum(r["b_over_b_max"] is None for r in ev)),
             cumulative=dict(status=status, inside=len(inside), inside_disagree=[f"{r['run']} port {r['port']}" for r in wrong],
                             median_B=statistics.median(r["B"] for r in cum) if cum else None,
                             median_B_calibration=statistics.median(r["B_calibration"] for r in cum) if cum else None,
                             median_B_deviation=statistics.median(r["B_deviation"] for r in cum) if cum else None,
                             closest=None if cbest is None else dict(run=cbest["run"], port=cbest["port"], room=cbest["cumulative_room"])))
    (HERE / "cumulative_summary.json").write_text(json.dumps(S, indent=2) + "\n")

    f = lambda x, spec="+.5f": DASH if x is None or x == "" else format(float(x), spec)
    L = ["# Decomposition of the budget, and the cumulative budget", "",
         "Written by `cumulative_analyze.py` under `CUMULATIVE_PROTOCOL.md`, a rule declared after the result of",
         "[`BRIDGE_APPLICATION.md`](../BRIDGE_APPLICATION.md): **no port is in the certified domain**. That result is not changed by anything here.", "",
         "## Part 1. Which term makes the per-write budget fail", "",
         f"`b = k*eta + sigma + e`, measured on the nominal replays: {parts['k_eta']:.2e} + {parts['sigma']:.2e} + ({parts['linkage']:.2e} + {parts['calibration']:.2e}) = **{b:.5f}** per write. "
         f"The local calibration error is {parts['calibration'] / b:.0%} of it and the transfer residual {parts['k_eta'] / b:.0%}. `d0/2` is about {statistics.median(r['half_d0'] for r in ev):.4f}.", "",
         f"- Ports evaluated: {len(ev)} of {len(out)}. Positive room under these estimates: **{S['per_write']['positive_room']}**, "
         f"of which the count disagrees on {len(S['per_write']['positive_room_count_disagrees'])}. This is not a certificate.",
         "- Largest term of the budget: " + ", ".join(f"`{k}` on {v} ports" for k, v in sorted(dominant.items(), key=lambda kv: -kv[1])) + ".",
         f"- Port with the largest room: `{best['run']}`, port {best['port']}, with `m` = {best['m']}, `a` = {best['a']:.5f}, `m*b` = {best['m_times_b']:.5f}, room {best['per_write_room']:+.5f}. "
         + (f"Its `b` could be {1 / best['b_over_b_max']:.1f} times larger." if best["b_over_b_max"] else "No `b` gives it a positive room."),
         f"- For the median port `b` would have to be divided by {S['per_write']['median_b_over_b_max']:.1f}: from {b:.4f} to {b / S['per_write']['median_b_over_b_max']:.4f} per write, "
         f"{b / S['per_write']['median_b_over_b_max'] / statistics.median(r['d0'] for r in ev):.0%} of a dose. "
         f"On {S['per_write']['ports_where_no_b_suffices']} port no `b` suffices: `a` alone exceeds what `d0/2` leaves.", "",
         "| m | Ports | `m*b` | Median `a` | Median room | Largest room | Median `b_max` | `b / b_max`, median |", "|---|---|---|---|---|---|---|---|"]
    for m in sorted(by_m):
        g = by_m[m]
        ratios = [r["b_over_b_max"] for r in g if r["b_over_b_max"] is not None]
        L.append(f"| {m} | {len(g)} | {m * b:.5f} | {statistics.median(r['a'] for r in g):.5f} | {statistics.median(r['per_write_room'] for r in g):+.5f} | "
                 f"{max(r['per_write_room'] for r in g):+.5f} | {statistics.median(r['b_max'] for r in g):+.5f} | {f(statistics.median(ratios), '.1f') if ratios else DASH} |")
    L += ["", "`b` is one number, measured on nominal devices and applied to every port as an estimate. `ell` is 0 where it is not measured, that is everywhere except cell 2064.", "",
          "## Part 2. The cumulative budget", "",
          "Lean: `needAlong_of_cumulative_tolerance`. `B = max over n <= m of |beta*(V(0)-V(n)) - n*d0| + epsilon*|V(0)-V(n)|`, from the stored voltages of the original runs, "
          f"with `beta` = {beta:.3f} and `epsilon` = {eps:.3f} per V.", "",
          "| Status | Ports |", "|---|---|"]
    L += [f"| {k} | {v} |" for k, v in sorted(status.items(), key=lambda kv: -kv[1])]
    L += [""]
    if cum:
        L += [f"- Median `B` over the {len(cum)} ports with a value: {S['cumulative']['median_B']:.5f}, of which calibration {S['cumulative']['median_B_calibration']:.5f} "
              f"and distance of the measured cumulated gain to `n*d0` {S['cumulative']['median_B_deviation']:.5f}.",
              f"- Port with the largest room: `{cbest['run']}`, port {cbest['port']}: {cbest['cumulative_room']:+.5f}.",
              f"- Inside under estimates: **{len(inside)}** ports, of which the count disagrees on **{len(wrong)}**" + (": " + ", ".join(S["cumulative"]["inside_disagree"]) if wrong else "") + "."]
    L += ["", "**Inside under estimates is not certified.** `a` and `d0` are peak-based proxies, `ell` is not measured for 99 cells, the calibration is that of nominal devices, "
          "a stored voltage of the campaign is a 40 µs average of a noisy signal, and the scalar read equation is not established. The count of certified ports stays 0.", ""]
    two = [r for r in out if r["run"] == level["cell"]]
    L += ["## Cell 2064", "", "| Port | Observed | m | Historical room, `ell = 0` | Per-write room | Writes | `B` | Cumulative room | Status |", "|---|---|---|---|---|---|---|---|---|"]
    for r in two:
        L.append(f"| {r['port']} | {r['observed_silent']} | {r['m']} | {f(r['room_historical'], '+.6f')} | {f(r.get('per_write_room'), '+.6f')} | {r.get('writes', DASH)} | "
                 f"{f(r.get('B'), '.5f')} | {f(r.get('cumulative_room'), '+.6f')} | {r['cumulative_status']} |")
    if inside:
        L += ["", "## Ports inside under estimates", "", "| Run | Port | Observed | m | `a` | `B` | Cumulative room | Count |", "|---|---|---|---|---|---|---|---|"]
        for r in sorted(inside, key=lambda r: -r["cumulative_room"]):
            L.append(f"| `{r['run']}` | {r['port']} | {r['observed_silent']} | {r['m']} | {r['a']:.5f} | {r['B']:.5f} | {r['cumulative_room']:+.5f} | {'agrees' if r['count_agrees'] == 'True' else 'DISAGREES'} |")
    L += ["", "Every port is in `cumulative_ports.csv`.", ""]
    (HERE / "CUMULATIVE_RESULTS.md").write_text("\n".join(L))
    print("\n".join(L))


if __name__ == "__main__":
    main()
