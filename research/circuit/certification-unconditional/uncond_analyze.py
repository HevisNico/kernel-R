"""Analysis of this campaign, by the rules of PREDICTION.md. No simulation is run.

  uncond_analyze.py preflight      check of the two preflight runs                 -> PREFLIGHT.md
  uncond_analyze.py report [BASE]  run once, after the last run is pushed          -> cells.csv, ports.csv, REPORT.md

The gains of a read are computed by the functions of ../certification/cert_analyze.py, which is not
modified. BASE is the folder that holds results/ and receives the three files; it is this folder
unless a dry run on synthetic data names another one.

A value that cannot be computed is reported as not evaluable, with its reason. Nothing is substituted.
"""
import csv
import hashlib
import json
import math
from pathlib import Path
import statistics
import sys

HERE = Path(__file__).resolve().parent
CERT = HERE.parent / "certification"
sys.path.insert(0, str(CERT))
import cert_analyze as A

MG = 0.0001                                        # margin of the charge integral
MANIFEST = json.loads((HERE / "manifest.json").read_text())
DASH = A.DASH
fm = A.fm


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def load(base, stage, name):
    """Rows, charges and metadata of a run of this campaign, or None and the reason."""
    A.HERE = base                                  # cert_analyze.load reads HERE/results/STAGE
    rows, meta, why = A.load(stage, name)
    if rows is None:
        return None, None, meta, why
    path = base / "results" / stage / f"{name}.charge.csv"
    if not path.exists():
        return None, None, meta, "charge measure missing"
    with path.open(newline="") as fh:
        charge = [{k: float(v) for k, v in r.items()} for r in csv.DictReader(fh)]
    if len(charge) != len(rows) or any(int(c["pulse"]) != int(r["pulse"]) or int(c["port"]) != int(r["port"]) for c, r in zip(charge, rows)):
        return None, None, meta, "charge measure: rows do not match"
    if not all(math.isfinite(c[k]) and c[k] > 0 for c in charge for k in ("w1", "w2")):
        return None, None, meta, "charge measure: a value is not finite or not positive"
    return rows, charge, meta, None


def compare(rows, charge, port, kappa):
    """D and eps_peak of PREDICTION.md for the single-port reads of a port in one run, or None and the reason."""
    reads = [(r, math.log(c[f"w{port}"])) for r, c in zip(rows, charge) if int(r["port"]) == port]
    silent = [(A.gain_silent(r), gi) for r, gi in reads if r["fired"] != 1]
    if not silent:
        return None, "no silent read in the run"
    if any(g is None for g, _ in silent):
        return None, "a silent read has no gain"
    d = statistics.mean(g - gi for g, gi in silent)
    dev_s = [abs(g - gi - d) for g, gi in silent]
    dev_f, left = [], 0
    for r, gi in reads:
        if r["fired"] == 1:
            z = A.gain(r, kappa)
            if z is None:
                left += 1
            else:
                dev_f.append(abs(z - gi - d))
    return dict(D=d, eps=max(dev_s + dev_f) + MG, eps_silent=max(dev_s), eps_fired=max(dev_f) if dev_f else None,
                silent=len(dev_s), fired=len(dev_f), left_out=left, count=A.count_of([r for r, _ in reads])), None


def preflight():
    L = ["# Preflight check", "", "Written by `uncond_analyze.py preflight`. It reads the two preflight runs of this campaign and the preflight of the certification campaign. No run of a test cell is read.", "",
         "| Run | Rows of this campaign (SHA-256) | Rows of the certification campaign (SHA-256) | Same |", "|---|---|---|---|"]
    kappa = json.loads((CERT / "calibration.json").read_text())["kappa"]
    same_all, tables = True, []
    for run in MANIFEST["stages"]["preflight"]:
        name = run["name"]
        mine = HERE / "results" / "preflight" / f"{name}.csv"
        theirs = CERT / "results" / "preflight" / f"{name}.csv"
        a = digest(mine) if mine.exists() else None
        b = digest(theirs)
        assert b == json.loads((CERT / "results" / "preflight" / f"{name}.json").read_text())["csv_sha256"]
        same_all &= a == b
        L.append(f"| `{name}` | `{a}` | `{b}` | {'yes' if a == b else '**no**'} |")
        rows, charge, _, why = load(HERE, "preflight", name)
        if rows is None:
            tables += ["", f"`{name}`: {why}."]
            continue
        tables += ["", f"`{name}`, nominal cell, gain from the peak or the early gain (`Z`) against the gain from the current of the mirror (`GI`):", "",
                   "| Pulse | Port | FIRE | `Z` | `GI` | `Z - GI` |", "|---|---|---|---|---|---|"]
        for r, c in zip(rows, charge):
            p = int(r["port"])
            if p in (1, 2):
                z, gi = A.gain(r, kappa), math.log(c[f"w{p}"])
                tables.append(f"| {int(r['pulse'])} | {p} | {int(r['fired'])} | {fm(z)} | {fm(gi)} | {fm(None if z is None else z - gi, '+.5f')} |")
    L += ["", "The rows are the same: the two more saved signals and the call through `uncond_run.py` change nothing." if same_all
          else "**The rows differ.** No other run is made before the cause is found and an amendment is pushed."]
    (HERE / "PREFLIGHT.md").write_text("\n".join(L + tables) + "\n")
    print("\n".join(L))
    return 0 if same_all else 1


def report(base):
    cal = json.loads((CERT / "calibration.json").read_text())
    kappa, d0, mu, h_mu = cal["kappa"], cal["d0"], cal["mu"], cal["h_mu"]
    with (CERT / "predictions.csv").open(newline="") as fh:
        pred = {(r["cell"], int(r["port"])): r for r in csv.DictReader(fh)}
    with (CERT / "ports.csv").open(newline="") as fh:
        old = {(r["cell"], int(r["port"])): r for r in csv.DictReader(fh)}
    failed_runs = []
    cells, ports = [], []
    for scan, train in zip(MANIFEST["stages"]["scan"], MANIFEST["stages"]["gain"]):
        cell = f"t{scan['seed']}"
        ls, level0 = float(pred[(cell, 1)]["static_level"]), float(pred[(cell, 1)]["level0"])
        c = dict(cell=cell, static_level=ls, level0=level0, reason="", reason2="")
        cells.append(c)
        # condition 1: the bracket of the firing level, as in the calibration of the certification campaign
        rows, charge, _, why = load(base, "scan", scan["name"])
        if rows is None:
            failed_runs.append(f"{scan['name']}: {why}")
            c["reason"] = why
        else:
            k = A.count_of(rows)
            j = next((i for i in range(k + 1, len(rows)) if rows[i]["fired"] != 1), None)
            if k >= len(rows) or j is None:
                c["reason"] = "no silent read after the first FIRE"
            else:
                before = rows[j - 1]
                z = A.gain(before, kappa)
                c.update(first_fire=k, silent_read=j)
                if z is None:
                    c["reason"] = "the read before the silent one has no gain"
                else:
                    ps = rows[j]["q_peak"]
                    base_peak = 0.1 + (before["c_pre"] - 0.1) * math.exp(-0.5)
                    pf = base_peak + math.exp(z)
                    c.update(Ps=ps, Pf=pf)
                    if pf < ps:
                        c["reason"] = "the bracket is empty: Pf < Ps"
                    else:
                        c.update(mu_cell=(ps + pf) / 2 - ls, hw_cell=(pf - ps) / 2, h1=max(abs(ps - level0), abs(pf - level0)))
                        c.update(mu_inside=abs(c["mu_cell"] - mu) <= h_mu, bracket_inside=c["h1"] <= h_mu)
                        g, why_g = compare(rows, charge, 1, kappa)
                        if g is None:
                            c["reason2"] = "scan: " + why_g
                        else:
                            pf2 = base_peak + math.exp(z + g["eps"])
                            c.update(D_scan=g["D"], eps_scan=g["eps"], scan_silent=g["silent"], scan_fired=g["fired"], scan_left_out=g["left_out"],
                                     Pf2=pf2, h2=max(abs(ps - level0), abs(pf2 - level0)))
        # condition 2: the training without noise
        rows, charge, _, why = load(base, "gain", train["name"])
        per_port = {}
        if rows is None:
            failed_runs.append(f"{train['name']}: {why}")
            c["reason2"] = (c["reason2"] + "; " if c["reason2"] else "") + "training: " + why
        else:
            for port in (1, 2):
                z0 = A.gain(A.reads_of(rows, port)[0], kappa)
                c[f"same_cell_diff{port}"] = None if z0 is None else z0 - float(pred[(cell, port)]["start_gain"])
                per_port[port] = compare(rows, charge, port, kappa)
            c["same_cell"] = c["same_cell_diff1"] is not None and abs(c["same_cell_diff1"]) <= A.MZ
            if not c["same_cell"]:
                c["reason2"] = (c["reason2"] + "; " if c["reason2"] else "") + "the same-cell check fails"
        for port in (1, 2):
            o = old[(cell, port)]
            p = dict(cell=cell, port=port, m=o["m"], count=o["count"], count_agrees=o["count_agrees"], status_107=o["status"], reason_107=o["reason"],
                     status1="not evaluable", reason1="", status2="not evaluable", reason2="")
            ports.append(p)
            g, why_g = per_port.get(port, (None, "training: " + (why or "missing")))
            if g is not None:
                p.update(count_noiseless=g["count"], D=g["D"], eps_peak=g["eps"], eps_silent=g["eps_silent"], eps_fired=g["eps_fired"],
                         reads_silent=g["silent"], reads_fired=g["fired"], reads_left_out=g["left_out"])
            if o["status"] == "not evaluable":
                p["reason1"] = p["reason2"] = "not evaluable in the certification campaign: " + o["reason"]
                continue
            a, b, noise = float(o["a"]), float(o["B"]), float(o["noise"])
            agrees = o["count_agrees"] == "True"
            carried = [x for x in o["reason"].split("; ") if x.startswith(("a rest state", "the latch", "the steering"))]
            p.update(a=a, B=b, noise=noise, ell_107=float(o["ell"]), room_107=float(o["room"]))

            def status(tag, aa, bb, h):
                ell = h + noise + A.MQ
                room = d0 / 2 - aa - bb - 20 / 17 * ell - 1 / 8000
                why_out = list(carried)
                if level0 - ell < 0.95:
                    why_out.append("level0 - ell is below 19/20")
                if room <= 0:
                    terms = {"a": aa, "B": bb, "(20/17)*ell": 20 / 17 * ell}
                    why_out.append(f"room is not positive; largest term {max(terms, key=terms.get)}")
                p.update({f"h{tag}": h, f"ell{tag}": ell, f"room{tag}": room, f"reason{tag}": "; ".join(why_out),
                          f"status{tag}": "outside the certified domain" if why_out else ("certified, count confirmed" if agrees else "certified, count contradicted")})

            if "h1" not in c:
                p["reason1"] = p["reason2"] = "cell not evaluable for condition 1: " + c["reason"]
                continue
            status("1", a, b, c["h1"])
            if g is None:
                p["reason2"] = "eps_peak not evaluable: " + why_g
            elif "h2" not in c:
                p["reason2"] = "eps_scan not evaluable: " + c["reason2"]
            elif not c.get("same_cell"):
                p["reason2"] = "the same-cell check fails"
            else:
                p.update(a2=a + g["eps"], B2=b + 2 * g["eps"])
                status("2", p["a2"], p["B2"], c["h2"])

    def write(name, rows, fields):
        with (base / name).open("w", newline="") as fh:
            w = csv.DictWriter(fh, fieldnames=fields, lineterminator="\n", extrasaction="ignore")
            w.writeheader()
            for r in rows:
                w.writerow({k: ("" if r.get(k) is None else (format(r[k], ".12g") if isinstance(r[k], float) else r[k])) for k in fields})
    write("cells.csv", cells, ["cell", "static_level", "level0", "first_fire", "silent_read", "Ps", "Pf", "mu_cell", "hw_cell", "h1", "mu_inside", "bracket_inside", "reason",
                               "D_scan", "eps_scan", "scan_silent", "scan_fired", "scan_left_out", "Pf2", "h2", "same_cell_diff1", "same_cell_diff2", "same_cell", "reason2"])
    write("ports.csv", ports, ["cell", "port", "m", "count", "count_agrees", "status_107", "reason_107", "room_107", "ell_107", "a", "B", "noise",
                               "h1", "ell1", "room1", "status1", "reason1", "count_noiseless", "D", "eps_peak", "eps_silent", "eps_fired", "reads_silent", "reads_fired",
                               "reads_left_out", "a2", "B2", "h2", "ell2", "room2", "status2", "reason2"])

    # ---- report
    n = len(ports)
    med = lambda v: statistics.median(v) if v else None
    big = lambda v: max(v) if v else None
    small = lambda v: min(v) if v else None
    cert = lambda r, tag: r[f"status{tag}"].startswith("certified")
    c107 = [r for r in ports if r["status_107"].startswith("certified")]
    c1, c2 = [r for r in ports if cert(r, "1")], [r for r in ports if cert(r, "2")]
    wrong1, wrong2 = [r for r in c1 if r["status1"].endswith("contradicted")], [r for r in c2 if r["status2"].endswith("contradicted")]
    ev = [c for c in cells if "h1" in c]
    mu_out, br_in = [c for c in ev if not c["mu_inside"]], [c for c in ev if c["bracket_inside"]]
    eps = [r["eps_peak"] for r in ports if "eps_peak" in r]
    eps_s = [r["eps_silent"] for r in ports if "eps_silent" in r]
    eps_f = [r["eps_fired"] for r in ports if r.get("eps_fired") is not None]
    eps_scan = [c["eps_scan"] for c in cells if "eps_scan" in c]
    dd = [r["D"] for r in ports if "D" in r]
    kept = [r for r in c107 if cert(r, "2")]
    lost = [r for r in c107 if not cert(r, "2")]
    new = [r for r in c2 if not r["status_107"].startswith("certified")]
    lost_why = {}
    for r in lost:
        key = r["reason2"] if r["status2"] != "not evaluable" else "not evaluable"
        lost_why[key] = lost_why.get(key, 0) + 1
    pc = lambda r: f"`{r['cell']}` port {r['port']}"

    def verdict(holds, evaluable=True):
        return "not evaluable" if not evaluable else ("holds" if holds else "fails")
    usable = len([c for c in cells if "first_fire" in c and "silent_read" in c])
    V = [("U1", "no run fails, and the 100 scans have a silent read after their first FIRE", f"{len(failed_runs)} runs without a usable result; {usable} of {len(cells)} scans with a silent read after their first FIRE",
          verdict(not failed_runs and usable == len(cells))),
         ("U2", "the `mu` of every cell is inside the envelope of the six cells", f"{len(ev) - len(mu_out)} of {len(ev)} evaluable cells inside", verdict(not mu_out, len(ev) == len(cells))),
         ("U3", "the bracket is inside the envelope for 65 to 95 cells", f"{len(br_in)} of {len(ev)} evaluable cells", verdict(65 <= len(br_in) <= 95, len(ev) == len(cells))),
         ("U4", "status 1 certifies 52 to 68 ports", f"{len(c1)} of {n}", verdict(52 <= len(c1) <= 68, all(r["status1"] != "not evaluable" for r in ports))),
         ("U5", "the median `eps_peak` is between 0.0003 and 0.004", f"{fm(med(eps))} over {len(eps)} ports", verdict(bool(eps) and 0.0003 <= med(eps) <= 0.004, len(eps) == n)),
         ("U6", "status 2 certifies 15 to 58 ports", f"{len(c2)} of {n}", verdict(15 <= len(c2) <= 58, all(r["status2"] != "not evaluable" for r in ports))),
         ("U7", "no certified port has its count contradicted", f"{len(wrong1)} of {len(c1)} by status 1, {len(wrong2)} of {len(c2)} by status 2", verdict(not wrong1 and not wrong2, bool(c1) or bool(c2)))]

    L = ["# Certification with the level of each cell and an independent measure of the gain: report", "",
         "Written by `uncond_analyze.py report` under [`PREDICTION.md`](PREDICTION.md). One row per cell: [`cells.csv`](cells.csv). One row per port: [`ports.csv`](ports.csv). "
         "The certification campaign is in [`../certification/`](../certification/REPORT.md); nothing of it is changed.", "",
         "## Summary", "",
         f"1. **Level of each cell (condition 1):** the `mu` measured on the cell is inside the envelope of the six calibration cells for {len(ev) - len(mu_out)} of the {len(cells)} test cells"
         f" ({len(cells) - len(ev)} not evaluable); the whole bracket of the level is inside for {len(br_in)}. `mu_cell` goes from {fm(small([c['mu_cell'] for c in ev]), '+.5f')} to {fm(big([c['mu_cell'] for c in ev]), '+.5f')}; "
         f"the envelope is [{mu - h_mu:+.5f}, {mu + h_mu:+.5f}].",
         f"2. **Independent gain (condition 2):** the gain inferred from the peak and the gain measured on the current of the mirror differ, after one constant per port, by at most `eps_peak`: "
         f"median {fm(med(eps))}, largest {fm(big(eps))}, over {len(eps)} ports and {sum(r.get('reads_silent', 0) for r in ports)} silent reads and {sum(r.get('reads_fired', 0) for r in ports)} reads with a FIRE.",
         f"3. **New status:** with the level of its own cell and the independent gain, {len(c2)} ports of {n} are certified; the count is the predicted one on {len(c2) - len(wrong2)} of them"
         + (f" and **contradicted on {len(wrong2)}**" if wrong2 else "") + f". With the level of the cell alone (status 1): {len(c1)} ports" + (f", **{len(wrong1)} contradicted**" if wrong1 else "") + ".",
         f"4. **Against the certification campaign:** of its {len(c107)} ports certified under condition, {len(kept)} are certified by the new status and {len(lost)} are not"
         + (" (" + ", ".join(f"{v}: {k}" for k, v in sorted(lost_why.items(), key=lambda kv: -kv[1])) + ")" if lost_why else "") + f"; {len(new)} ports that it did not certify are certified now.",
         "5. **What the new status still rests on:** a simulation; the level of a cell is bracketed once, on port 1, and used for its two ports; `eps_peak` is measured without noise and applied to the noisy reads of the same port; "
         "`kappa`, `d0`, `eps_kappa` and the centre `mu` come from the certification campaign; the count of a port comes from one noisy run.", "",
         "## Predictions", "", "| | Prediction | Measured | Verdict |", "|---|---|---|---|"]
    L += [f"| {a} | {b} | {c} | {d} |" for a, b, c, d in V]
    L += ["", "## Failures", "",
          "- **F1, a certified port whose count is contradicted:** " + (", ".join(sorted({pc(r) for r in wrong1 + wrong2})) if wrong1 or wrong2 else "none") + ".",
          "- **F2, a cell whose `mu` is outside the envelope of the six cells:** " + (", ".join(f"`{c['cell']}` ({c['mu_cell']:+.5f})" for c in mu_out) if mu_out else "none") + ".",
          "- **Runs or cells without a usable result:** " + ("; ".join(failed_runs + [f"`{c['cell']}`: {c['reason']}" for c in cells if c["reason"] and "h1" not in c and not any(c['cell'][1:] in f for f in failed_runs)]) or "none") + "."]
    L += ["", "## Condition 1: the level of each cell", "",
          "| | Certification campaign (six cells) | This campaign (each cell) |", "|---|---|---|",
          f"| Midpoint of the bracket minus the static level | `mu` = {mu:+.5f} | median {fm(med([c['mu_cell'] for c in ev]), '+.5f')}, from {fm(small([c['mu_cell'] for c in ev]), '+.5f')} to {fm(big([c['mu_cell'] for c in ev]), '+.5f')} |",
          f"| Half-width of the bracket | largest {max(d['half_width'] for d in cal['leak_scans']):.5f} | median {fm(med([c['hw_cell'] for c in ev]))}, largest {fm(big([c['hw_cell'] for c in ev]))} |",
          f"| Bound of the level around `level0` | `h_mu` = {h_mu:.5f} for every cell | `h1`: median {fm(med([c['h1'] for c in ev]))}, largest {fm(big([c['h1'] for c in ev]))}; "
          f"`h2` (with `eps_scan`): median {fm(med([c['h2'] for c in cells if 'h2' in c]))}, largest {fm(big([c['h2'] for c in cells if 'h2' in c]))} |", "",
          f"Cells whose bracket is not inside the envelope (`h1 > h_mu`): {len(ev) - len(br_in)}" + (": " + ", ".join(f"`{c['cell']}` ({c['h1']:.5f})" for c in ev if not c["bracket_inside"]) if len(ev) > len(br_in) else "") + ".",
          "", "## Condition 2: the gain measured on the current of the mirror", "",
          "| | Value |", "|---|---|",
          f"| `eps_peak` of a port (10 reads of its training without noise) | smallest {fm(small(eps))}, median {fm(med(eps))}, largest {fm(big(eps))} |",
          f"| Its part from the silent reads | median {fm(med(eps_s))}, largest {fm(big(eps_s))} |",
          f"| Its part from the reads with a FIRE | median {fm(med(eps_f))}, largest {fm(big(eps_f))}, over {len(eps_f)} ports that have one |",
          f"| `eps_scan` of a cell (40 reads of its leak scan) | median {fm(med(eps_scan))}, largest {fm(big(eps_scan))} |",
          f"| Constant `D` of a port | mean {fm(statistics.mean(dd) if dd else None, '+.5f')}, from {fm(small(dd), '+.5f')} to {fm(big(dd), '+.5f')} |",
          f"| Reads with a FIRE earlier than 0.76, left out | {sum(r.get('reads_left_out', 0) for r in ports)} in the trainings, {sum(c.get('scan_left_out', 0) for c in cells)} in the scans |",
          f"| Same-cell check, port 1 | {sum(1 for c in cells if c.get('same_cell'))} of {len(cells)} cells within {A.MZ}; largest difference {fm(big([abs(c['same_cell_diff1']) for c in cells if c.get('same_cell_diff1') is not None]))} |",
          f"| Same difference, port 2, reported | largest {fm(big([abs(c['same_cell_diff2']) for c in cells if c.get('same_cell_diff2') is not None]))} |",
          f"| Count of the training without noise equal to the predicted `m` | {sum(1 for r in ports if 'count_noiseless' in r and str(r['count_noiseless']) == r['m'])} of {sum(1 for r in ports if 'count_noiseless' in r)} ports |",
          "", "## The budget, side by side", "",
          "| Term | Certification campaign | Status 1: level of the cell | Status 2: level of the cell and independent gain |", "|---|---|---|---|",
          f"| Start distance | `a`: median {fm(med([r['a'] for r in ports if 'a' in r]))} | the same | `a + eps_peak`: median {fm(med([r['a2'] for r in ports if 'a2' in r]))} |",
          f"| Cumulated gain | `B`: median {fm(med([r['B'] for r in ports if 'B' in r]))} | the same | `B + 2*eps_peak`: median {fm(med([r['B2'] for r in ports if 'B2' in r]))} |",
          f"| Threshold `ell` | median {fm(med([r['ell_107'] for r in ports if 'ell_107' in r]))} | median {fm(med([r['ell1'] for r in ports if 'ell1' in r]))} | median {fm(med([r['ell2'] for r in ports if 'ell2' in r]))} |",
          f"| Room | median {fm(med([r['room_107'] for r in ports if 'room_107' in r]), '+.5f')}; positive on {sum(1 for r in ports if r.get('room_107', -1) > 0)} ports | "
          f"median {fm(med([r['room1'] for r in ports if 'room1' in r]), '+.5f')}; positive on {sum(1 for r in ports if r.get('room1', -1) > 0)} | "
          f"median {fm(med([r['room2'] for r in ports if 'room2' in r]), '+.5f')}; positive on {sum(1 for r in ports if r.get('room2', -1) > 0)} |",
          f"| Certified | {len(c107)} | {len(c1)} | {len(c2)} |",
          f"| Certified with the count contradicted | {sum(1 for r in c107 if r['status_107'].endswith('contradicted'))} | {len(wrong1)} | {len(wrong2)} |", ""]
    short = {"certified, count confirmed": "certified", "certified, count contradicted": "**count contradicted**", "outside the certified domain": "outside", "not evaluable": "not evaluable"}
    trans = {}
    for r in ports:
        key = (short[r["status_107"]], short[r["status2"]])
        trans[key] = trans.get(key, 0) + 1
    L += ["| Certification campaign | New status | Ports |", "|---|---|---|"] + [f"| {a} | {b} | {v} |" for (a, b), v in sorted(trans.items(), key=lambda kv: -kv[1])]

    def line(r):
        return (f"| `{r['cell']}` | {r['port']} | {r['m']} | {r['count']} | {'yes' if r['count_agrees'] == 'True' else 'no'} | {short[r['status_107']]} | {fm(r.get('room_107'), '+.5f')} | "
                f"{fm(r.get('h1'))} | {fm(r.get('room1'), '+.5f')} | {short[r['status1']]} | {fm(r.get('eps_peak'))} | {fm(r.get('room2'), '+.5f')} | {short[r['status2']]} | {r['reason2'] or DASH} |")
    head = ["| Cell | Port | m | Count | Agrees | Certification campaign | Its room | `h1` | Room 1 | Status 1 | `eps_peak` | Room 2 | New status | Reason |", "|---|---|---|---|---|---|---|---|---|---|---|---|---|---|"]
    L += ["", f"## The {len(c107)} ports certified under condition by the certification campaign", ""] + head + [line(r) for r in c107]
    L += ["", f"## The {n} ports", ""] + head + [line(r) for r in ports]
    L += ["", "## Traces", ""]
    metas = [json.loads(p.read_text()) for stage in MANIFEST["stages"] for p in sorted((base / "results" / stage).glob("*.json"))]
    now = digest(CERT / "cert_run.py")
    L += [f"- **Extraction.** The rows and the compact trace of a run are made by `../certification/cert_run.py`, SHA-256 `{now}`: "
          + ("the value of `manifest.json`, checked at each run." if now == MANIFEST["cert_run_sha256"] else "**not the value of `manifest.json`**.")
          + " The charge of each mirror is measured by `uncond_run.py` on the compact trace.",
          f"- **Traces.** The compact traces are in the private repository `HevisNico/kernel-R-circuit`, folder `08-certification-unconditional-traces/`; "
          f"{sum(1 for m in metas if m.get('trace_sha256'))} of the {len(metas)} runs with a result have the SHA-256 of their trace in their public metadata.",
          "- **Reproduction.** Every run of this campaign is without noise and made once."]
    (base / "REPORT.md").write_text("\n".join(L) + "\n")
    print("\n".join(L[:14 + len(V)]))
    return 0


if __name__ == "__main__":
    if sys.argv[1] == "preflight":
        sys.exit(preflight())
    sys.exit(report(Path(sys.argv[2]).resolve() if len(sys.argv) > 2 else HERE))
