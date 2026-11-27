"""TASK 3, the replay's reading (REPLAY_CRITERIA_2026-11-27.md and its addendum): per cell and case, the symbol and latch
of the third read (lesson slot 2), u before it, and for each comparator the signed maximum of (inp - inn) over the
decision window [T, T + 240 us] (watch_tu 12 x tu 20 us) with its time; the sampling step; the case-1 validity check
against stage D's record. Writes REPLAY_TABLE.json, REPLAY_TABLE.txt and one figure per refuted cell. Changes nothing.

Comparators (deck, comp subckt: "out is high when inp > inn"; xm1's gate is inn, xm2's gate is inp):
  port comparator xcmps of port p (x1, x2): inn = x<p>.vrefsn, inp = x<p>.vs     -> margin vs - vrefsn
  common comparator xcmpm:                 inn = vq,          inp = vrefmn      -> margin vrefmn - vq
"""
import json
import sys
from pathlib import Path

import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

D = Path(sys.argv[1])                     # the replay folder holding r_<inst>_case<k>/
WATCH_US = 240.0
CELLS = {"XOR3_27735": ("c1_0", "c1_1"), "XOR3_88529": ("c1_1", "c1_0")}


def raw(path):
    f = open(path, "rb")
    h = b""
    while True:
        line = f.readline()
        h += line
        if line.startswith(b"Binary:"):
            break
    t = h.decode(errors="replace")
    names = [x.split("\t")[2] for x in t.split("Variables:\n")[1].split("\n") if x.count("\t") >= 3]
    npts = int([x for x in t.split("\n") if x.startswith("No. Points:")][0].split(":")[1])
    return names, np.memmap(path, dtype="<f8", mode="r", offset=len(h), shape=(npts, len(names)))


def col(names, data, v):
    for k in (v, f"v({v})", v.lower(), f"v({v.lower()})"):
        if k in names:
            return np.asarray(data[:, names.index(k)])
    raise KeyError(v)


def read_of(slot, c):
    return [r for r in slot["reads"] if f"c{r['layer']}_{r['index']}" == c][0]


table, curves = {}, {}
for inst, (refuted, witness) in CELLS.items():
    for case in ("1", "2", "3"):
        f = D / f"r_{inst.split('_')[1]}_case{case}"
        if not (f / "replay.json").exists():
            continue
        rj = json.loads((f / "replay.json").read_text())
        names, data = raw(f / "replay.raw")
        t = col(names, data, "time")
        s2, d2 = rj["slots"][2], rj["stage_D_slots"][2]
        T = s2["T"] * 1e-9
        i0, i1 = np.searchsorted(t, T), np.searchsorted(t, T + WATCH_US * 1e-6)
        tw = t[i0:i1]
        dt = np.diff(tw)
        for c in (refuted, witness):
            r, rd = read_of(s2, c), read_of(d2, c)
            row = dict(instance=inst, cell=c, role="refuted" if c == refuted else "witness", case=case,
                       arrivals_from_T_us=[(a - s2["T"]) / 1000 for a in r["arrivals"]],
                       symbol="F" if r["emission"] is not None else "s",
                       latch_from_T_us=None if r["latch"] is None else (r["latch"] - s2["T"]) / 1000,
                       u_before_read_V=s2["u"][c], samples=int(len(tw)), dt_median_ns=float(np.median(dt) * 1e9),
                       dt_max_ns=float(dt.max() * 1e9), status=rj["status"], deck_identical=rj["deck_identical"])
            margins = {}
            for name, inp, inn in ((f"port 1 (x1): vs - vrefsn", f"x{c}.x1.vs", f"x{c}.x1.vrefsn"),
                                   (f"port 2 (x2): vs - vrefsn", f"x{c}.x2.vs", f"x{c}.x2.vrefsn"),
                                   (f"common (xcmpm): vrefmn - vq", f"x{c}.vrefmn", f"x{c}.vq")):
                m = (col(names, data, inp)[i0:i1] - col(names, data, inn)[i0:i1]) * 1e3
                k = int(np.argmax(m))
                margins[name] = dict(max_mV=float(m[k]), at_from_T_us=float((tw[k] - T) * 1e6))
                curves.setdefault((inst, c), {}).setdefault(case, {})[name] = ((tw - T) * 1e6, m)
            curves[(inst, c)][case]["p"] = ((tw - T) * 1e6, col(names, data, f"x{c}.p")[i0:i1])
            row["margins"] = margins
            if case == "1":                                  # the validity check, against stage D's record
                du = max(abs(a - b) for a, b in zip(s2["u"][c], d2["u"][c]))
                dl = None if (r["latch"] is None or rd["latch"] is None) else abs(r["latch"] - rd["latch"]) / 1000
                row["validity"] = dict(stage_D_symbol="F" if rd["emission"] is not None else "s",
                                       stage_D_latch_from_T_us=None if rd["latch"] is None else (rd["latch"] - d2["T"]) / 1000,
                                       latch_diff_us=dl, u_max_diff_uV=du * 1e6,
                                       ok=row["symbol"] == "F" and rd["emission"] is not None and dl is not None
                                       and dl <= 0.1 and du <= 1e-6)
            table[f"{inst} {c} case {case}"] = row

# one figure per refuted cell: the three cases overlaid, p and the three comparator margins
for inst, (refuted, witness) in CELLS.items():
    cv = curves.get((inst, refuted))
    if not cv:
        continue
    fig, ax = plt.subplots(4, 1, figsize=(11, 11), sharex=True)
    keys = ["p", "port 1 (x1): vs - vrefsn", "port 2 (x2): vs - vrefsn", "common (xcmpm): vrefmn - vq"]
    cols = {"1": "tab:green", "2": "tab:blue", "3": "tab:red"}
    labels = {"1": "case 1: 2.4/2.4 us (stage D)", "2": "case 2: 12.0/12.0 us", "3": "case 3: network times"}
    for case, d in sorted(cv.items()):
        for j, k in enumerate(keys):
            x, y = d[k]
            ax[j].plot(x, y, color=cols[case], lw=1, label=labels[case] + (f" ({table[f'{inst} {refuted} case {case}']['symbol']})" if j == 0 else ""))
    ax[0].axhline(0.9, color="k", ls="--", lw=0.8)
    for j in (1, 2, 3):
        ax[j].axhline(0, color="k", lw=0.8)
    ax[0].set_ylabel(f"v(x{refuted}.p) [V]")
    for j, k in enumerate(keys[1:], start=1):
        ax[j].set_ylabel(k + " [mV]", fontsize=8)
    ax[3].set_xlabel("time from slot 2's T [us] (the third read; window T..T+240 us)")
    ax[0].set_title(f"{inst} {refuted} (refuted cell): replay of the third read on the isolated stage-D deck, cases 1-3")
    for a in ax:
        a.grid(alpha=0.3)
        a.set_xlim(0, 60)
        a.legend(fontsize=7, loc="best")
    fig.tight_layout()
    fig.savefig(D / f"fig_replay_{inst}_{refuted}.png", dpi=130)

(D / "REPLAY_TABLE.json").write_text(json.dumps(table, indent=1) + "\n")
lines = ["instance cell role case | arrivals(us from T) | symbol latch(us) | u before (mV) | port1 max mV @us | port2 max mV @us | common max mV @us | dt med/max ns | validity"]
for k, r in table.items():
    m = r["margins"]
    g = lambda n: f"{m[n]['max_mV']:+.3f}@{m[n]['at_from_T_us']:.2f}"
    v = r.get("validity")
    lines.append(f"{r['instance']} {r['cell']} {r['role']} {r['case']} | {r['arrivals_from_T_us']} | {r['symbol']} "
                 f"{r['latch_from_T_us']} | {[round(u * 1e3, 4) for u in r['u_before_read_V']]} | "
                 f"{g('port 1 (x1): vs - vrefsn')} | {g('port 2 (x2): vs - vrefsn')} | {g('common (xcmpm): vrefmn - vq')} | "
                 f"{r['dt_median_ns']:.3f}/{r['dt_max_ns']:.1f} | "
                 + ("" if v is None else f"ok={v['ok']} (D {v['stage_D_symbol']} {v['stage_D_latch_from_T_us']}, dlatch {v['latch_diff_us']}, du {v['u_max_diff_uV']:.3f} uV)"))
(D / "REPLAY_TABLE.txt").write_text("\n".join(lines) + "\n")
print("\n".join(lines))
