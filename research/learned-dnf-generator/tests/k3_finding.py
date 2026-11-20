"""M3 finding: the room model's both-lines condition is stricter than the kernel's.

predicted.room (C5/predicted.py:326-327) asks of c's both-lines test read: pair >= max(Z_1, Z_2) + te. The kernel's
checkFiringMask (MonotonePremiseTargets.lean:93) asks scoreAt(both) >= scoreAt(y) for each firing submask y, with no
te, plus each anchor's lower bound. So a pair in [max(Z_1, Z_2), max(Z_1, Z_2) + te) is refused by the room model and
accepted by Lean, everything else equal. No committed reference lands in that gap (tests/test_mirror.py, part 2).

This builds two such cases with campaign 5's frozen cases.py as a library, from phase 0's CALIBRATION.json only, as
cases.py builds P3p (pairs set to max + te), but with pairs at max + te - 1 (G1) and exactly max (G0), then writes a
generic-style Lean file that asserts the MIRROR's per-checker verdicts. If it compiles, Lean agrees with the mirror and
so disagrees with gate4.verdicts on those cases.

  python -I tests/k3_finding.py IMPL_ROOT OUT.lean       (needs numpy: cases.py's geometric fit)
"""
import copy
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
import emit  # noqa: E402
import legacy  # noqa: E402
import mirror  # noqa: E402
import spec  # noqa: E402


def main():
    root, out = Path(sys.argv[1]).resolve(), Path(sys.argv[2])
    c5 = root / "research/learned-dnf-circuit-campaign-5"
    gate4, P = legacy.frozen(c5)
    import cases
    t0, dose = cases.base()
    p0 = cases.predict(t0, dose)
    n = p0["needs"]
    lo = min(n["c1"], n["c2"])
    zmax = max(t0[("c", n["c1"], "port 1")]["Z"], t0[("c", n["c2"], "port 2")]["Z"])
    te = p0["budgets"]["K0"]["c"]["testing"]
    specs, verdicts, pcs, report = [], {}, {}, []
    for tag, v in (("G1", zmax + te - 1), ("G0", zmax)):
        t = copy.deepcopy(t0)
        for r in ("both", P.SKEWED):
            t[("c", lo, r)]["Z"] = v
            cases.fire_bits(t, ("c", lo, r))
        x = dict(cases.predict(t, dose), tag=tag)
        raw = legacy.spec_of(x, "k3_finding.py", c5)
        raw["lean"] = dict(style="generic", namespace="LearnedCoincidence.MonotoneDNF.PremiseCheck.K3Finding",
                           source="tests/k3_finding.py (cases.py's P3p construction, pairs below max + te)", derive=True)
        s = spec.load(raw)
        mv = mirror.verdicts(s)
        gv = gate4.verdicts(x)
        for K, (conj, pc, fails) in mv.items():
            verdicts[(tag, K)], pcs[(tag, K)] = conj, pc
            report.append(dict(case=tag, budget=K, pair=v, zmax=zmax, te_K0=te, gate4_verdict=gv[K], mirror_verdict=conj,
                               mirror_per_checker=pc, room_without_room=x["room"][K]["c"]["without_room"],
                               mirror_failing_kinds=sorted({k for _, k, _ in fails})))
        specs.append(s)
    out.write_text(emit.lean_file(specs, verdicts, "tests/k3_finding.py", per_checker=pcs))
    print(json.dumps(report, indent=1))


if __name__ == "__main__":
    main()
