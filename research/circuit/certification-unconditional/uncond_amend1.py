"""Status 3 of AMENDMENT_1.md. No simulation is run.

  uncond_amend1.py report [BASE]   run once, after uncond_analyze.py report   -> ports_amendment1.csv, REPORT_AMENDMENT_1.md

Reads cells.csv and ports.csv written by uncond_analyze.py (statuses 1 and 2, as registered), the
results of the runs, and the early charges written by uncond_early.py. BASE is the folder that holds
results/, cells.csv and ports.csv and receives the two files; it is this folder unless a dry run on
synthetic data names another one.
"""
import csv
import json
import math
from pathlib import Path
import statistics
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import uncond_analyze as U

A, CERT, MG, fm, DASH = U.A, U.CERT, U.MG, U.fm, U.DASH


def load_early(base, stage, name, rows):
    path = base / "results" / stage / f"{name}.early.csv"
    if not path.exists():
        return None, "early charge missing"
    with path.open(newline="") as fh:
        early = [{k: float(v) for k, v in r.items()} for r in csv.DictReader(fh)]
    if len(early) != len(rows) or any(int(e["pulse"]) != int(r["pulse"]) or int(e["port"]) != int(r["port"]) for e, r in zip(early, rows)):
        return None, "early charge: rows do not match"
    if not all(math.isfinite(e[k]) and e[k] > 0 for e in early for k in ("e1", "e2")):
        return None, "early charge: a value is not finite or not positive"
    return early, None


def eps3_of(rows, charge, early, port):
    """eps3 of AMENDMENT_1.md for the single-port reads of a port in one run, or None and the reason."""
    reads = [(r, math.log(c[f"w{port}"]), math.log(e[f"e{port}"])) for r, c, e in zip(rows, charge, early) if int(r["port"]) == port]
    silent = [(A.gain_silent(r), A.gain_early(r), gi, ge) for r, gi, ge in reads if r["fired"] != 1]
    if not silent:
        return None, "no silent read in the run"
    if any(g is None or y is None for g, y, _, _ in silent):
        return None, "a silent read has no gain"
    d = statistics.mean(g - gi for g, _, gi, _ in silent)
    de = statistics.mean(y - ge for _, y, _, ge in silent)
    full = [abs(g - gi - d) for g, _, gi, _ in silent]
    early_s = [abs(y - ge - de) for _, y, _, ge in silent]
    early_f, left = [], 0
    for r, _, ge in reads:
        if r["fired"] == 1:
            y = A.gain_early(r) if r["fire_latency"] >= A.EARLY else None
            if y is None:
                left += 1
            else:
                early_f.append(abs(y - ge - de))
    return dict(DE=de, eps3=max(full + early_s + early_f) + MG, full_silent=max(full), early_silent=max(early_s),
                early_fired=max(early_f) if early_f else None, fired=len(early_f), left_out=left), None


def report(base):
    cal = json.loads((CERT / "calibration.json").read_text())
    kappa, d0 = cal["kappa"], cal["d0"]
    with (base / "cells.csv").open(newline="") as fh:
        cells = {r["cell"]: r for r in csv.DictReader(fh)}
    with (base / "ports.csv").open(newline="") as fh:
        ports = list(csv.DictReader(fh))
    with (CERT / "ports.csv").open(newline="") as fh:
        old = {(r["cell"], int(r["port"])): r for r in csv.DictReader(fh)}
    scan3, port3 = {}, {}
    for scan, train in zip(U.MANIFEST["stages"]["scan"], U.MANIFEST["stages"]["gain"]):
        cell = f"t{scan['seed']}"
        c = cells[cell]
        # the scan: eps3_scan and the upper end of the bracket
        rows, charge, _, why = U.load(base, "scan", scan["name"])
        early, why_e = load_early(base, "scan", scan["name"], rows) if rows is not None else (None, why)
        if rows is None or early is None:
            scan3[cell] = (None, "scan: " + (why or why_e))
        elif c["h1"] == "":
            scan3[cell] = (None, "cell not evaluable for condition 1: " + c["reason"])
        else:
            g, why_g = eps3_of(rows, charge, early, 1)
            if g is None:
                scan3[cell] = (None, "scan: " + why_g)
            else:
                before = rows[int(c["silent_read"]) - 1]
                level0, ps = float(c["level0"]), float(c["Ps"])
                pf3 = 0.1 + (before["c_pre"] - 0.1) * math.exp(-0.5) + math.exp(A.gain(before, kappa) + g["eps3"])
                scan3[cell] = (dict(eps3_scan=g["eps3"], Pf3=pf3, h3=max(abs(ps - level0), abs(pf3 - level0))), None)
        # the training without noise: eps3 of each port
        rows, charge, _, why = U.load(base, "gain", train["name"])
        early, why_e = load_early(base, "gain", train["name"], rows) if rows is not None else (None, why)
        for port in (1, 2):
            port3[(cell, port)] = (None, "training: " + (why or why_e)) if rows is None or early is None else eps3_of(rows, charge, early, port)

    out = []
    for p in ports:
        cell, port = p["cell"], int(p["port"])
        o, c = old[(cell, port)], cells[cell]
        r = dict(p, status3="not evaluable", reason3="")
        out.append(r)
        g, why_g = port3[(cell, port)]
        s, why_s = scan3[cell]
        if g is not None:
            r.update(eps3=g["eps3"], eps3_full_silent=g["full_silent"], eps3_early_silent=g["early_silent"], eps3_early_fired=g["early_fired"],
                     reads_fired_early=g["fired"], reads_left_out3=g["left_out"])
        if s is not None:
            r.update(eps3_scan=s["eps3_scan"], h3=s["h3"])
        if o["status"] == "not evaluable":
            r["reason3"] = "not evaluable in the certification campaign: " + o["reason"]
        elif c["h1"] == "":
            r["reason3"] = "cell not evaluable for condition 1: " + c["reason"]
        elif g is None:
            r["reason3"] = "eps3 not evaluable: " + why_g
        elif s is None:
            r["reason3"] = "eps3_scan not evaluable: " + why_s
        elif c["same_cell"] != "True":
            r["reason3"] = "the same-cell check fails"
        else:
            a3, b3, noise, level0 = float(o["a"]) + g["eps3"], float(o["B"]) + 2 * g["eps3"], float(o["noise"]), float(c["level0"])
            ell = s["h3"] + noise + A.MQ
            room = d0 / 2 - a3 - b3 - 20 / 17 * ell - 1 / 8000
            why_out = [x for x in o["reason"].split("; ") if x.startswith(("a rest state", "the latch", "the steering"))]
            if level0 - ell < 0.95:
                why_out.append("level0 - ell is below 19/20")
            if room <= 0:
                terms = {"a": a3, "B": b3, "(20/17)*ell": 20 / 17 * ell}
                why_out.append(f"room is not positive; largest term {max(terms, key=terms.get)}")
            agrees = o["count_agrees"] == "True"
            r.update(a3=a3, B3=b3, ell3=ell, room3=room, reason3="; ".join(why_out),
                     status3="outside the certified domain" if why_out else ("certified, count confirmed" if agrees else "certified, count contradicted"))
    fields = list(ports[0].keys()) + ["eps3", "eps3_full_silent", "eps3_early_silent", "eps3_early_fired", "reads_fired_early", "reads_left_out3", "eps3_scan",
                                      "a3", "B3", "h3", "ell3", "room3", "status3", "reason3"]
    with (base / "ports_amendment1.csv").open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=fields, lineterminator="\n")
        w.writeheader()
        for r in out:
            w.writerow({k: ("" if r.get(k) is None else (format(r[k], ".12g") if isinstance(r[k], float) else r[k])) for k in fields})

    # ---- report
    n = len(out)
    num = lambda r, k: None if r.get(k) in (None, "") else float(r[k])
    med = lambda v: statistics.median(v) if v else None
    big = lambda v: max(v) if v else None
    small = lambda v: min(v) if v else None
    cert = lambda r, k: r[k].startswith("certified")
    c107, c1, c2, c3 = ([r for r in out if cert(r, k)] for k in ("status_107", "status1", "status2", "status3"))
    wrong3 = [r for r in c3 if r["status3"].endswith("contradicted")]
    eps3 = [r["eps3"] for r in out if "eps3" in r]
    eps2 = [num(r, "eps_peak") for r in out if num(r, "eps_peak") is not None]
    kept, lost = [r for r in c107 if cert(r, "status3")], [r for r in c107 if not cert(r, "status3")]
    new = [r for r in c3 if not cert(r, "status_107")]
    lost_why = {}
    for r in lost:
        key = r["reason3"] if r["status3"] != "not evaluable" else "not evaluable"
        lost_why[key] = lost_why.get(key, 0) + 1
    mu_in = sum(1 for c in cells.values() if c["mu_inside"] == "True")
    br_in = sum(1 for c in cells.values() if c["bracket_inside"] == "True")
    ev = sum(1 for c in cells.values() if c["h1"] != "")
    all3 = all(r["status3"] != "not evaluable" for r in out)

    def verdict(holds, evaluable=True):
        return "not evaluable" if not evaluable else ("holds" if holds else "fails")
    V = [("U8", "the median `eps3` is between 0.0004 and 0.002", f"{fm(med(eps3))} over {len(eps3)} ports", verdict(bool(eps3) and 0.0004 <= med(eps3) <= 0.002, len(eps3) == n)),
         ("U9", "status 3 certifies 35 to 58 ports", f"{len(c3)} of {n}", verdict(35 <= len(c3) <= 58, all3)),
         ("U10", "no port certified by status 3 has its count contradicted", f"{len(wrong3)} of {len(c3)}", verdict(not wrong3, bool(c3)))]
    L = ["# Status 3 of amendment 1: report", "",
         "Written by `uncond_amend1.py report` under [`AMENDMENT_1.md`](AMENDMENT_1.md), after [`REPORT.md`](REPORT.md), which gives statuses 1 and 2 as registered in [`PREDICTION.md`](PREDICTION.md). "
         "One row per port: [`ports_amendment1.csv`](ports_amendment1.csv). The certification campaign is in [`../certification/`](../certification/REPORT.md); nothing of it is changed.", "",
         "## Summary", "",
         f"1. **Level of each cell (condition 1):** measured on each of the {len(cells)} test cells by its own leak scan ({ev} evaluable). Its `mu` is inside the envelope of the six calibration cells for {mu_in} cells; "
         f"its whole bracket is inside for {br_in}. With the level of its own cell alone (status 1), {len(c1)} ports are certified.",
         f"2. **Independent gain (condition 2):** on silent reads, the gain inferred from the peak agrees with the charge that the mirror delivers over the whole pulse; on reads with a FIRE, the early gain agrees with the charge delivered up to 0.75 unit. "
         f"After one constant per port the largest distance is `eps3`: median {fm(med(eps3))}, largest {fm(big(eps3))}. The registered measure, over the whole pulse for every read, gives `eps_peak`: median {fm(med(eps2))}, largest {fm(big(eps2))}, "
         f"because the current of the mirror changes after a FIRE.",
         f"3. **Certified with both measures (status 3):** {len(c3)} ports of {n}; the count is the predicted one on {len(c3) - len(wrong3)} of them"
         + (f" and **contradicted on {len(wrong3)}**" if wrong3 else "") + f". By the registered status 2: {len(c2)} ports.",
         f"4. **Against the certification campaign:** of its {len(c107)} ports certified under condition, {len(kept)} are certified by status 3 and {len(lost)} are not"
         + (" (" + ", ".join(f"{v}: {k}" for k, v in sorted(lost_why.items(), key=lambda kv: -kv[1])) + ")" if lost_why else "") + f"; {len(new)} ports that it did not certify are certified by status 3.",
         "5. **What stays conditional:** it is a simulation; the level of a cell is bracketed once, on port 1, and used for its two ports; `eps3` is measured without noise and applied to the noisy reads of the same port; "
         "the gain of a read with a FIRE is checked by the current up to 0.75 unit only, and from there to the end of the pulse it rests on `kappa` and `eps_kappa`; `kappa`, `d0`, `eps_kappa` and the centre `mu` come from the certification campaign; "
         "the count of a port comes from one noisy run.", "",
         "## Predictions of amendment 1", "", "| | Prediction | Measured | Verdict |", "|---|---|---|---|"]
    L += [f"| {a} | {b} | {c} | {d} |" for a, b, c, d in V]
    L += ["", "**F1, a port certified by status 3 whose count is contradicted:** " + (", ".join(f"`{r['cell']}` port {r['port']}" for r in wrong3) if wrong3 else "none") + ".",
          "", "## The two measures of the gain", "",
          "| | Registered (`eps_peak`, status 2) | Amendment 1 (`eps3`, status 3) |", "|---|---|---|",
          f"| Bound of a port | median {fm(med(eps2))}, largest {fm(big(eps2))} | smallest {fm(small(eps3))}, median {fm(med(eps3))}, largest {fm(big(eps3))} |",
          f"| Silent reads, whole pulse | median {fm(med([num(r, 'eps_silent') for r in out if num(r, 'eps_silent') is not None]))} | the same: median {fm(med([r['eps3_full_silent'] for r in out if 'eps3_full_silent' in r]))} |",
          f"| Reads with a FIRE | whole pulse: median {fm(med([num(r, 'eps_fired') for r in out if num(r, 'eps_fired') is not None]))}, largest {fm(big([num(r, 'eps_fired') for r in out if num(r, 'eps_fired') is not None]))} | "
          f"up to 0.75 unit: median {fm(med([r['eps3_early_fired'] for r in out if r.get('eps3_early_fired') is not None]))}, largest {fm(big([r['eps3_early_fired'] for r in out if r.get('eps3_early_fired') is not None]))} |",
          f"| Silent reads, up to 0.75 unit | {DASH} | median {fm(med([r['eps3_early_silent'] for r in out if 'eps3_early_silent' in r]))}, largest {fm(big([r['eps3_early_silent'] for r in out if 'eps3_early_silent' in r]))} |",
          f"| Bound of a cell in its leak scan | `eps_scan`: median {fm(med([float(c['eps_scan']) for c in cells.values() if c['eps_scan'] != '']))} | `eps3_scan`: median {fm(med([s['eps3_scan'] for s, _ in scan3.values() if s]))}, largest {fm(big([s['eps3_scan'] for s, _ in scan3.values() if s]))} |",
          f"| Reads with a FIRE earlier than 0.76, left out | {sum(int(r['reads_left_out'] or 0) for r in out)} | {sum(r.get('reads_left_out3', 0) for r in out)} |",
          "", "## The four statuses, side by side", "",
          "| | Certification campaign | Status 1: level of the cell | Status 2: and gain, as registered | Status 3: and gain, amendment 1 |", "|---|---|---|---|---|",
          f"| Room, median | {fm(med([num(r, 'room_107') for r in out if num(r, 'room_107') is not None]), '+.5f')} | {fm(med([num(r, 'room1') for r in out if num(r, 'room1') is not None]), '+.5f')} | "
          f"{fm(med([num(r, 'room2') for r in out if num(r, 'room2') is not None]), '+.5f')} | {fm(med([r['room3'] for r in out if 'room3' in r]), '+.5f')} |",
          f"| Certified | {len(c107)} | {len(c1)} | {len(c2)} | {len(c3)} |",
          f"| Certified with the count contradicted | {sum(1 for r in c107 if r['status_107'].endswith('contradicted'))} | {sum(1 for r in c1 if r['status1'].endswith('contradicted'))} | "
          f"{sum(1 for r in c2 if r['status2'].endswith('contradicted'))} | {len(wrong3)} |", ""]
    short = {"certified, count confirmed": "certified", "certified, count contradicted": "**count contradicted**", "outside the certified domain": "outside", "not evaluable": "not evaluable"}
    trans = {}
    for r in out:
        key = (short[r["status_107"]], short[r["status3"]])
        trans[key] = trans.get(key, 0) + 1
    L += ["| Certification campaign | Status 3 | Ports |", "|---|---|---|"] + [f"| {a} | {b} | {v} |" for (a, b), v in sorted(trans.items(), key=lambda kv: -kv[1])]

    def line(r):
        return (f"| `{r['cell']}` | {r['port']} | {r['m']} | {r['count']} | {'yes' if r['count_agrees'] == 'True' else 'no'} | {short[r['status_107']]} | {fm(num(r, 'room_107'), '+.5f')} | "
                f"{short[r['status1']]} | {fm(num(r, 'room1'), '+.5f')} | {short[r['status2']]} | {fm(num(r, 'room2'), '+.5f')} | {fm(r.get('eps3'))} | {fm(r.get('room3'), '+.5f')} | {short[r['status3']]} | {r['reason3'] or DASH} |")
    head = ["| Cell | Port | m | Count | Agrees | Certification campaign | Its room | Status 1 | Room 1 | Status 2 | Room 2 | `eps3` | Room 3 | Status 3 | Reason |", "|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|"]
    L += ["", f"## The {len(c107)} ports certified under condition by the certification campaign", ""] + head + [line(r) for r in c107]
    L += ["", f"## The {n} ports", ""] + head + [line(r) for r in out]
    (base / "REPORT_AMENDMENT_1.md").write_text("\n".join(L) + "\n")
    print("\n".join(L[:16 + len(V)]))
    return 0


if __name__ == "__main__":
    assert sys.argv[1] == "report"
    sys.exit(report(Path(sys.argv[2]).resolve() if len(sys.argv) > 2 else HERE))
