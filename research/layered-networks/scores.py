"""The score readout of every read, from an instrumented record (instrument.cal_run). Development only.

The mapping of CALIBRATION_PROPOSAL.md (a), campaign 6's (predict6.anchors, predict6.mapped, MAPPING_U.md), per gate:
  w_p = (u_p(0) - u_p) / D_p, the port's move from the preset in doses, u_p measured before the read's slot;
  both:   K = max(8 - s*, s*), d = round(theta / 2K), g_1 = g_2 = round(d (K - s*)),      H = ceil(h 2d);
  copy:   K = max(8 - s*, s*), d = round(theta / 2K), g_1 = round(theta - d s*),         H = ceil(h d);
  either: d = round(theta / (s*_1 + s*_2)), g_p = round(theta - d s*_p),                  H = max_p ceil(h_p d);
  help 0; Z = round(sum over the ports with an arrival of (g_p + d w_p)); theta = 100 000.
Exact Fractions, rounding to the nearest, ties to even (Python's round on a Fraction), as campaign 5's P.

Checks reported (none of them is a Lean clause yet; M3 fits the guarded tuple and budgets):
  the decoder check: a read with |Z - theta| > H whose FIRE bit disagrees with Z >= theta (predict6 point 3);
  question 1: ceil(s*) equals the first firing round of the cell's training word for that group.
"""
from fractions import Fraction as F
import json
import math
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import spec as specmod  # noqa: E402

THETA = json.loads((HERE / "calibration.json").read_text())["theta"]


def anchors(gate, scans):
    """scans: {group: (s*, h)} (Fractions). Returns dict(d, g {port: int}, H) or None."""
    if gate in ("both", "copy"):
        if 0 not in scans:
            return None
        s, h = scans[0]
        K = max(8 - s, s)
        d = round(F(THETA) / (2 * K))
        if gate == "both":
            g = round(d * (K - s))
            return dict(d=d, g={1: g, 2: g}, H=math.ceil(h * 2 * d), K=K)
        return dict(d=d, g={1: round(THETA - d * s), 2: 0}, H=math.ceil(h * d), K=K)
    if gate == "either":
        if 0 not in scans or 1 not in scans:
            return None
        (s1, h1), (s2, h2) = scans[0], scans[1]
        d = round(F(THETA) / (s1 + s2))
        return dict(d=d, g={1: round(THETA - d * s1), 2: round(THETA - d * s2)}, H=max(math.ceil(h1 * d), math.ceil(h2 * d)))
    return None


def score(an, w, ports):
    """Z of a read whose arrivals are on `ports` (1-based), w {port: Fraction}."""
    return round(sum(an["g"][p] + an["d"] * w[p] for p in ports)) if ports else 0


def decoder_ok(Z, fired, H):
    return abs(Z - THETA) <= H or fired == (Z >= THETA)


def readout(s, rec):
    """Per cell: anchors, question 1; per read: Z, w, fired, decoder. Returns a dict (JSON-ready)."""
    scans = rec["scans"] or {}
    D = {k: F(v) for k, v in (scans.get("D") or {}).items()}
    u0 = scans.get("u0") or {}
    words = rec["words"]
    out = dict(cells={}, reads=[], decoder_failures=[], undecided=0, checked=0)
    an_of = {}
    for k, nodes in enumerate(s["layers"], start=1):
        for i, n in enumerate(nodes):
            c = f"c{k}_{i}"
            res = (scans.get("cells") or {}).get(c) or []
            got = {r["group"]: (F(r["s_star"]), F(r["half_bracket"])) for r in res if r.get("ok")}
            an = anchors(n["gate"], got)
            q1 = {}
            for g in range(specmod.GROUPS[n["gate"]]):
                word = words.get(f"{k}/{i}/{g}", "")
                first = word.find("F")
                q1[g] = dict(first_firing_round=first, ceil_s_star=None if g not in got else math.ceil(got[g][0]),
                             agree=g in got and first >= 0 and math.ceil(got[g][0]) == first)
            an_of[c] = an
            out["cells"][c] = dict(gate=n["gate"], scans={str(g): [str(a), str(b)] for g, (a, b) in got.items()},
                                   anchors=None if an is None else dict(d=an["d"], g=an["g"], H=an["H"]),
                                   question_1={str(g): v for g, v in q1.items()},
                                   scan_failures=[r for r in res if not r.get("ok")])
    for idx, sl in enumerate(rec["slots"]):
        if sl["kind"] not in ("lesson", "test"):
            continue
        for r in sl["reads"]:
            c = f"c{r['layer']}_{r['index']}"
            an = an_of.get(c)
            ports = [a + 1 for a in range(2) if r["arrivals"][a] is not None]
            fired = r["emission"] is not None
            row = dict(slot=idx, kind=sl["kind"], cell=c, ports=ports, fired=fired)
            if an is None or any(f"{c}/{p}" not in D for p in ports) or c not in u0:
                row["Z"] = None
            else:
                w = {p: (F(u0[c][p - 1]) - F(sl["u"][c][p - 1])) / D[f"{c}/{p}"] for p in ports}
                Z = score(an, w, ports)
                row.update(Z=Z, w={str(p): str(v) for p, v in w.items()}, decoder=decoder_ok(Z, fired, an["H"]))
                out["checked"] += 1
                if abs(Z - THETA) <= an["H"]:
                    out["undecided"] += 1
                if not row["decoder"]:
                    out["decoder_failures"].append(row)
            out["reads"].append(row)
    return out


def main(spec_path, outdir):
    s = specmod.load(spec_path)
    rec = json.loads((Path(outdir) / "record.json").read_text())
    r = readout(s, rec)
    (Path(outdir) / "scores.json").write_text(json.dumps(r, indent=1, default=str) + "\n")
    print(json.dumps(dict(cells=r["cells"], checked=r["checked"], undecided=r["undecided"],
                          decoder_failures=r["decoder_failures"]), indent=1, default=str))


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
