"""Read-only trace study, second part: XOR3_88529 key 1/1/0 (layer 1, cell c1_1, group 0) on K01, from its N0
extract (the full trace.raw stays on K01), against its stage-D record; and, for both refuted instances, the port
arrival times of every lesson round of the refuted key. Also checks, for XOR3_27735, that its extract equals the
full trace on the extract's vectors. Writes study2.json and fig_xor3_88529_key110_round2.png. Changes nothing."""
import json
import sys
from pathlib import Path

import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

ROOTS, OUT = Path(sys.argv[1]), Path(sys.argv[2])
WATCH_US = 240.0


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
    return names, np.memmap(path, dtype="<f8", mode="r", offset=len(h), shape=(npts, len(names)))


def window(names, data, sig, t0, t1):
    tcol = np.asarray(data[:, 0])
    i0, i1 = np.searchsorted(tcol, t0), np.searchsorted(tcol, t1)
    return {s: np.asarray(data[i0:i1, names.index(s)]).copy() for s in ["time"] + sig}


def lessons(r, cell):
    out = {}
    for x in r["lessons"]:
        if (x["layer"], x["cell"], x["group"]) == (1, cell, 0):
            s = r["slots"][x["slot"]]
            rd = [q for q in s["reads"] if q["layer"] == 1 and q["index"] == cell][0]
            out[x["round"]] = (s, rd)
    return out


def fit_slack(inst, cell):
    f = json.loads((inst / "D/fit_d.json").read_text())
    c = [c for c in f["cells"] if c["cell"] == f"c1_{cell}"][0]
    return {lv: {k: v for k, v in c["verdicts"][lv]["min_slack"].items() if "stop" in k or "anchor" in k}
            for lv in ("K0", "K3")}, c["lean_cell"]["K0"]["threshold"], c["D_mV"], c["need"], c["maxWrites"]


res = {}
for label, inst, cell, key, rawp in (
        ("XOR3_27735", ROOTS / "K03/out_K03/XOR3_27735", 0, "1/0/0", ROOTS / "K03/out_K03/XOR3_27735/N0/trace.raw"),
        ("XOR3_88529", ROOTS / "K01/out_K01/XOR3_88529", cell_ := 1, "1/1/0", OUT / "extract_88529_trace.raw")):
    rec = json.loads((inst / "N0/noisy_record.json").read_text())
    recD = json.loads((inst / "D/record.json").read_text())
    sig = [f"v(xc1_{cell}.p)", f"v(xc1_{cell}.vmem1)", f"v(xc1_{cell}.x1.sum)", f"v(xc1_{cell}.vmem2)", f"v(xc1_{cell}.x2.sum)"]
    names, data = raw(rawp)
    rows = {}
    for rnd, (s, rd) in sorted(lessons(rec, cell).items()):
        T = s["T"] * 1e-9
        w = window(names, data, sig, T, T + WATCH_US * 1e-6)
        p = w[sig[0]]
        k = int(np.argmax(p))
        dt = np.diff(w["time"])
        rows[rnd] = dict(T_ns=s["T"], arrivals_ns=rd["arrivals"], arrivals_from_T_us=[(a - s["T"]) / 1000 for a in rd["arrivals"]],
                         spacing_us=(rd["arrivals"][1] - rd["arrivals"][0]) / 1000, latch_ns=rd["latch"],
                         latch_from_T_us=None if rd["latch"] is None else (rd["latch"] - s["T"]) / 1000,
                         fired=rd["emission"] is not None, u_V=s["u"][f"c1_{cell}"], p_max_V=float(p[k]),
                         p_max_at_ns=round(float(w["time"][k]) * 1e9), signed_margin_V=float(p[k]) - 0.9,
                         samples=len(p), dt_median_ns=float(np.median(dt) * 1e9), dt_max_ns=float(dt.max() * 1e9))
    rowsD = {rnd: dict(T_ns=s["T"], arrivals_ns=rd["arrivals"], arrivals_from_T_us=[(a - s["T"]) / 1000 for a in rd["arrivals"]],
                       latch_ns=rd["latch"], latch_from_T_us=None if rd["latch"] is None else (rd["latch"] - s["T"]) / 1000,
                       fired=rd["emission"] is not None, u_V=s["u"][f"c1_{cell}"])
             for rnd, (s, rd) in sorted(lessons(recD, cell).items())}
    slack, thr, Dmv, need, mw = fit_slack(inst, cell)
    res[label] = dict(key=key, cell=f"c1_{cell}", trace=str(rawp.relative_to(rawp.parents[4])) if label == "XOR3_27735" else
                      "out_K01/XOR3_88529/N0/extract (trace.raw.part-000 + part-001, sha256 9538f0ea…, full time resolution)",
                      words=dict(network=rec["words"][key], stage_D=recD["words"][key]),
                      network_rounds=rows, stage_D_rounds=rowsD,
                      fit=dict(min_slack=slack, lean_threshold=thr, D_mV={k: float(eval(v)) if isinstance(v, str) else v
                                                                          for k, v in Dmv.items()}, need=need, maxWrites=mw))
    if label == "XOR3_88529":
        fig, ax = plt.subplots(3, 1, figsize=(11, 9), sharex=True)
        for rnd, col in ((2, "tab:red"), (3, "tab:blue")):
            s, rd = lessons(rec, cell)[rnd]
            T = s["T"] * 1e-9
            w = window(names, data, sig, T, T + WATCH_US * 1e-6)
            x = (w["time"] - T) * 1e6
            lab = f"round {rnd} ({'s, silent' if rd['emission'] is None else 'F, fired'})"
            ax[0].plot(x, w[sig[0]], color=col, label=lab)
            ax[1].plot(x, (w[sig[1]] - w[sig[2]]) * 1e3, color=col, label=lab)
            ax[2].plot(x, (w[sig[3]] - w[sig[4]]) * 1e3, color=col, label=lab)
            for a_ in rd["arrivals"]:
                for k_ in range(3):
                    ax[k_].axvline((a_ - s["T"]) / 1000, color=col, ls=":", lw=1)
            if rd["latch"]:
                ax[0].axvline((rd["latch"] - s["T"]) / 1000, color=col, ls="--", lw=1)
        ax[0].axhline(0.9, color="k", lw=1, ls="--", label="0.9 V: the emission rule (run.py, v(p) > 0.9)")
        ax[0].set_ylabel(f"v(xc1_{cell}.p) [V]")
        ax[1].set_ylabel("vmem1 - x1.sum [mV]")
        ax[2].set_ylabel("vmem2 - x2.sum [mV]")
        ax[2].set_xlabel("time from the slot's T [us]  (dotted: the two port arrivals; dashed: the latch)")
        ax[0].set_title(f"XOR3_88529 N0 on K01 (extract), key 1/1/0 (c1_1, group 0): lesson round 2 (3rd symbol) vs round 3")
        for a_ in ax:
            a_.legend(fontsize=8, loc="best")
            a_.grid(alpha=0.3)
            a_.set_xlim(5, 45)
        fig.tight_layout()
        fig.savefig(OUT / "fig_xor3_88529_key110_round2.png", dpi=130)

# XOR3_27735: its extract against the full trace, on the extract's vectors
ext = ROOTS / "K03/out_K03/XOR3_27735/N0/extract"
tmp = OUT / "extract_27735_trace.raw"
with open(tmp, "wb") as g:
    for part in ("trace.raw.part-000", "trace.raw.part-001"):
        g.write((ext / part).read_bytes())
ne, de = raw(tmp)
nf, df = raw(ROOTS / "K03/out_K03/XOR3_27735/N0/trace.raw")
same = de.shape[0] == df.shape[0] and all(np.array_equal(np.asarray(de[:, ne.index(v)]), np.asarray(df[:, nf.index(v)])) for v in ne)
res["XOR3_27735_extract_equals_full_trace"] = dict(points=(int(de.shape[0]), int(df.shape[0])), vectors=len(ne), identical=bool(same))
tmp.unlink()
(OUT / "study2.json").write_text(json.dumps(res, indent=1) + "\n")
print(json.dumps(res, indent=1))
