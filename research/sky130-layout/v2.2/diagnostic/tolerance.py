"""Exploratory: the 16 ports of stage C with a two-sided tolerance on the rest band. No verdict changes.

  python3 -I tolerance.py        prints the table of TOLERANCE.md; no simulation is run

The rest band of the certification rule is 0.1 to 0.1001 in level units: vq between 50 uV below
its rest reference and the reference itself, with nothing allowed above. Here the band is widened
by a tolerance d on vq on both sides, 0.1 - d / 0.5 V to 0.1001 + d / 0.5 V, and the 16 ports of
stage C are read again on its committed results.

The analysis is that of stage P and stage C (../../phase1/p_analyze.py). Only the band changes,
in the three places where it is written, each changed by a replacement of text that must match
exactly once (twice in cert_analyze.py):

  cert_analyze.py, in the mirror of the campaign scripts   the count of rest states outside the band,
                                                           and the reason "a rest state is outside
                                                           the band" of a port, which status 3 carries
  rule A1 (p_analyze.rule_a1)                              the reason "rest charge"

With d = 0 the script must give the counts of ../C_REPORT.md; it checks that it does. Nothing of
the rule besides the band is changed: no room is recomputed for the wider band.
"""
import inspect
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
P1 = HERE.parent.parent / "phase1"
sys.path.insert(0, str(P1))
sys.path.insert(0, str(HERE.parent / "phase1"))
import p_analyze
import p_run

RESULTS = HERE.parent / "phase1" / "results_c"
BUILD = HERE / "build" / "tolerance"
TOLERANCES_UV = [0.0, 0.1, 1.0, 10.0]
CERT = ["0.1 <= r[\"c_pre\"] <= 0.1001", "0.1 <= x[\"c_pre\"] <= 0.1001"]
A1 = ".1 <= float(r[\"c_pre\"]) <= .1001"


def read(delta_uv):
    lo, hi = 0.1 - delta_uv * 1e-6 / 0.5, 0.1001 + delta_uv * 1e-6 / 0.5
    band = f"{lo!r} <= {{}} <= {hi!r}"
    mirror = p_run.mirror

    def patched(root, runs):
        mirror(root, runs)
        path = Path(root) / "certification" / "cert_analyze.py"
        text = path.read_text()
        for old in CERT:
            assert text.count(old) == 1, old
            text = text.replace(old, band.format(old.split(" <= ")[1]))
        path.write_text(text)

    source = inspect.getsource(p_analyze.rule_a1)
    assert source.count(A1) == 1
    space = dict(vars(p_analyze))
    exec(source.replace(A1, band.format('float(r["c_pre"])')), space)
    rule, p_analyze.rule_a1, p_run.mirror = p_analyze.rule_a1, space["rule_a1"], patched
    try:
        data = p_analyze.Data(RESULTS)
        P = p_analyze.pipeline(data, BUILD / f"d{delta_uv:g}", "stage")
        _, X = p_analyze.verdicts(data, P, p_analyze.schematic_reference())
    finally:
        p_analyze.rule_a1, p_run.mirror = rule, mirror
    out = {}
    for c, q in X["ports"]:
        s3 = P["amended"].get((c, q), {}).get("status3", "")
        a1 = P["a1"].get((c, q), {})
        out[(c, q)] = dict(by3=s3.startswith("certified"), by1=a1.get("eligible", False),
                           wrong=s3 == "certified, count contradicted" or a1.get("contradicted", False),
                           rest="rest charge" in a1.get("reasons", "").split("; "), status3=s3, reasons=a1.get("reasons", ""),
                           rooms=(a1.get("silence_room"), a1.get("fire_room")), room3=P["amended"].get((c, q), {}).get("room3", ""))
    return out, (lo, hi)


def main():
    tables = {d: read(d) for d in TOLERANCES_UV}
    base = tables[0.0][0]
    count = lambda t: (sum(p["by3"] or p["by1"] for p in t.values()), sum(p["by3"] for p in t.values()), sum(p["by1"] for p in t.values()),
                       sum(p["wrong"] for p in t.values()), sum(p["rest"] for p in t.values()))
    assert count(base) == (7, 4, 7, 0, 3), count(base)         # ../C_REPORT.md
    print("| Tolerance on `vq` | Rest band, level units | Certified, of 16 | At status 3 | By rule A1 | Contradicted | Refused for the rest state |")
    print("|---|---|---|---|---|---|---|")
    for d, (t, (lo, hi)) in tables.items():
        n, n3, n1, w, r = count(t)
        print(f"| {'none: the rule' if d == 0 else f'{d:g} µV'} | {lo:.7f} to {hi:.7f} | {n} | {n3} | {n1} | {w} | {r} |")
    print()
    print("| Port | Without tolerance | " + " | ".join(f"{d:g} µV" for d in TOLERANCES_UV[1:]) + " | Rooms of rule A1, silence and FIRE | Room at status 3 |")
    print("|---|---|" + "---|" * (len(TOLERANCES_UV) + 1))
    word = lambda p: ("certified" + (" (status 3 and A1)" if p["by3"] and p["by1"] else " (A1)" if p["by1"] else " (status 3)")
                      if p["by3"] or p["by1"] else "not certified" + (": rest state" + (" only" if p["reasons"] == "rest charge" else " and rooms") if p["rest"] else ""))
    for key in base:
        if base[key]["rest"] or any(word(tables[d][0][key]) != word(base[key]) for d in TOLERANCES_UV):
            p = base[key]
            rooms = "—" if p["rooms"][0] is None else f"{p['rooms'][0]:+.5f} and {p['rooms'][1]:+.5f}"
            print(f"| `{key[0]}` port {key[1]} | {word(p)} | " + " | ".join(word(tables[d][0][key]) for d in TOLERANCES_UV[1:])
                  + f" | {rooms} | {float(p['room3']):+.5f} |")
    print()
    print("smallest room of rule A1 among the ports certified at 10 uV:",
          min(min(p["rooms"]) for p in tables[10.0][0].values() if p["by1"]), "; the band is wider by", 2 * 10e-6 / 0.5, "level unit")


if __name__ == "__main__":
    main()
