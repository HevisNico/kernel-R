"""Campaign 6, BATCH_SPEC.md section 5: I, E and go/stop for k = 2..10 by the stopping rule, with campaign 5's frozen
split and cost code (plan.split, plan.machine_expected, c4.limit).

  etable.py C5_DIR      C5_DIR: research/learned-dnf-circuit-campaign-5 in a checkout of campaign 5's frozen code
                        (commit f805c20 or a descendant that keeps its plan.py and c4.py), run with its pinned venv
"""
import math, sys
from pathlib import Path
from fractions import Fraction as F
sys.path.insert(0, str(Path(sys.argv[1]).resolve()))
import c4, plan
RM_ON = [F("725.0"), F("733.7"), F("707.1"), F("722.0"), F("733.4"), F("705.0")]
RM_OFF = [F("580.9"), F("597.5"), F("580.0"), F("582.7"), F("603.2"), F("579.0")]
CAL = dict(on=sum(RM_ON) / 6, off=sum(RM_OFF) / 6)
NET = dict(quiet=718, untrained=132, noisy=1400)
def run(id_, mach, e):
    e = F(e)
    return dict(id=id_, machine=mach, expected_s=float(e), timeout_s=c4.limit(e))
def E_of(I, k, measures):
    na = math.ceil(I / 2)
    seeds = list(range(I)); A, B = seeds[:na], seeds[na:]
    mach = lambda x: "a" if x < na else "b"
    meas = lambda x: [run(f"{x}-{n}", mach(x), e) for n, e in measures]
    st = plan.split(meas, A, B)
    m = math.ceil(k * I / 10); ma = min((m + 1) // 2, len(A)); mb = m - ma
    net = A[:ma] + B[:mb]; ctl = net[0]
    q = lambda x: [run(f"{x}-q", mach(x), NET["quiet"])] + ([run(f"{x}-u", mach(x), NET["untrained"])] if x == ctl else [])
    st += plan.split(q, A[:ma], B[:mb])
    for j in (1, 2, 3):
        st += plan.split(lambda x, j=j: [run(f"{x}-n{j}", mach(x), NET["noisy"])], A[:ma], B[:mb])
    return sum(plan.machine_expected([r for r in s if r["machine"] == mm]) for s in st for mm in ("a", "b")), len(st)
OPTS = dict(
    A=[("on", CAL["on"]), ("off", CAL["off"])] + [(f"scan{i}", 785) for i in range(9)],
    B=[("on", CAL["on"]), ("off", CAL["off"])] + [(f"scan{i}", 785) for i in range(5)] + [("onesided-a", 250), ("onesided-b", 250)],
    C=[("on", CAL["on"]), ("off", CAL["off"])] + [(f"scan{i}", 685) for i in range(5)] + [("onesided-a", 250), ("onesided-b", 250)],
)
print("cal-on mean", float(CAL["on"]), "cal-off mean", float(CAL["off"]))
for name, ms in OPTS.items():
    print(f"option {name}: measures per instance {float(sum(F(e) for _, e in ms)):.1f} s")
    for k in range(2, 11):
        I = math.ceil(30 / k)
        E, n = E_of(I, k, ms)
        go = k >= 2 and I <= 40 and E <= 28800
        print(f"  k={k:2d} I={I:2d} net_instances={math.ceil(k*I/10)} stages={n} E={E:9.1f} {'GO' if go else 'stop'}")
