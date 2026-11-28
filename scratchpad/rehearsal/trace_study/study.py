"""Read-only trace study of XOR3_27735, key 1/0/0 (layer 1, cell c1_0, group 0), 3rd symbol = lesson round 2.
Reads the restored N0 trace.raw of K03 (and of K12's DUPX), the N0 noisy_record.json and stage D's record.json.
Writes study.json, and fig_xor3_27735_key100_round2.png. Changes nothing."""
import json
import sys
from pathlib import Path

import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

ROOTS = Path(sys.argv[1])            # .../analysis/R
OUT = Path(sys.argv[2])
K03 = ROOTS / "K03/out_K03/XOR3_27735"
K12 = ROOTS / "K12/out_K12/DUPX_XOR3_27735"
SIG = ["v(xc1_0.p)", "v(xc1_0.vmem1)", "v(xc1_0.x1.sum)", "v(xc1_0.vmem2)", "v(xc1_0.x2.sum)"]


def raw(path):
    f = open(path, "rb")
    h = b""
    while True:
        line = f.readline()
        h += line
        if line.startswith(b"Binary:"):
            break
    t = h.decode()
    names = [x.split("\t")[2] for x in t.split("Variables:\n")[1].split("\n") if x.count("\t") >= 3]
    npts = int([x for x in t.split("\n") if x.startswith("No. Points:")][0].split(":")[1])
    data = np.memmap(path, dtype="<f8", mode="r", offset=len(h), shape=(npts, len(names)))
    return names, data


def window(names, data, t0, t1):
    tcol = np.asarray(data[:, 0])
    i0, i1 = np.searchsorted(tcol, t0), np.searchsorted(tcol, t1)
    out = {"time": tcol[i0:i1].copy()}
    for s in SIG:
        out[s] = np.asarray(data[i0:i1, names.index(s)]).copy()
    return out


rec = json.loads((K03 / "N0/noisy_record.json").read_text())
recD = json.loads((K03 / "D/record.json").read_text())


def lesson(r, rnd):
    x = [x for x in r["lessons"] if (x["layer"], x["cell"], x["group"], x["round"]) == (1, 0, 0, rnd)][0]
    s = r["slots"][x["slot"]]
    rd = [q for q in s["reads"] if q["layer"] == 1 and q["index"] == 0][0]
    return s, rd


names, data = raw(K03 / "N0/trace.raw")
res = dict(question="XOR3_27735 key 1/0/0 (layer 1, cell c1_0, group 0): its 3rd symbol is lesson round 2",
           words=dict(network_K03=rec["words"]["1/0/0"], stage_D_isolated=recD["words"]["1/0/0"]))
WATCH_US = 240.0                     # calendar watch_tu 12 x tu 20 us: the read's decision window from the slot's T
rows = {}
for rnd in range(5):
    s, rd = lesson(rec, rnd)
    T = s["T"] * 1e-9
    w = window(names, data, T, T + WATCH_US * 1e-6)
    dt = np.diff(w["time"])
    p = w["v(xc1_0.p)"]
    k = int(np.argmax(p))
    rows[rnd] = dict(T_ns=s["T"], arrivals_ns=rd["arrivals"], latch_ns=rd["latch"], emission_ns=rd["emission"],
                     fired=rd["emission"] is not None, u_V=s["u"]["c1_0"],
                     p_max_V=float(p[k]), p_max_at_ns=round(float(w["time"][k]) * 1e9),
                     signed_margin_V=float(p[k]) - 0.9,
                     samples=len(w["time"]), dt_median_ns=float(np.median(dt) * 1e9), dt_max_ns=float(dt.max() * 1e9))
res["network_K03_rounds"] = rows
res["stage_D_rounds"] = {}
for rnd in range(4):
    s, rd = lesson(recD, rnd)
    res["stage_D_rounds"][rnd] = dict(T_ns=s["T"], arrivals_ns=rd["arrivals"], latch_ns=rd["latch"],
                                      emission_ns=rd["emission"], fired=rd["emission"] is not None, u_V=s["u"]["c1_0"])

# K12: the same window of the duplicate's trace
n12, d12 = raw(K12 / "N0/trace.raw")
s2, rd2 = lesson(rec, 2)
T2 = s2["T"] * 1e-9
a = window(names, data, T2, T2 + WATCH_US * 1e-6)
b = window(n12, d12, T2, T2 + WATCH_US * 1e-6)
res["K12_same_window"] = dict(samples=(len(a["time"]), len(b["time"])),
                              identical=all(np.array_equal(a[k], b[k]) for k in ["time"] + SIG))

# the figure: round 2 (silent, the 3rd symbol) against round 3 (FIRE), each from its slot's T
fig, ax = plt.subplots(3, 1, figsize=(11, 9), sharex=True)
for rnd, col in ((2, "tab:red"), (3, "tab:blue")):
    s, rd = lesson(rec, rnd)
    T = s["T"] * 1e-9
    w = window(names, data, T, T + WATCH_US * 1e-6)
    x = (w["time"] - T) * 1e6
    lab = f"round {rnd} ({'s, silent' if rd['emission'] is None else 'F, fired'})"
    ax[0].plot(x, w["v(xc1_0.p)"], color=col, label=lab)
    for i, (vm, su) in enumerate((("v(xc1_0.vmem1)", "v(xc1_0.x1.sum)"), ("v(xc1_0.vmem2)", "v(xc1_0.x2.sum)"))):
        ax[1 + i].plot(x, (w[vm] - w[su]) * 1e3, color=col, label=lab)
    for a_ in rd["arrivals"]:
        for k_ in range(3):
            ax[k_].axvline((a_ - s["T"]) * 1e-3, color=col, ls=":", lw=1)
    if rd["latch"]:
        ax[0].axvline((rd["latch"] - s["T"]) * 1e-3, color=col, ls="--", lw=1)
ax[0].axhline(0.9, color="k", lw=1, ls="--", label="0.9 V: the emission rule (run.py, v(p) > 0.9)")
ax[0].set_ylabel("v(xc1_0.p) [V]")
ax[1].set_ylabel("vmem1 - x1.sum [mV]")
ax[2].set_ylabel("vmem2 - x2.sum [mV]")
ax[2].set_xlabel("time from the slot's T [us]  (dotted: the two port arrivals; dashed: the latch)")
ax[0].set_title("XOR3_27735 N0 on K03, key 1/0/0 (c1_0, group 0): lesson round 2 (3rd symbol) vs round 3")
for a_ in ax:
    a_.legend(fontsize=8, loc="best")
    a_.grid(alpha=0.3)
# the inset window around the arrivals
for a_ in ax:
    a_.set_xlim(5, 45)
fig.tight_layout()
fig.savefig(OUT / "fig_xor3_27735_key100_round2.png", dpi=130)
(OUT / "study.json").write_text(json.dumps(res, indent=1) + "\n")
print(json.dumps(res, indent=1))
