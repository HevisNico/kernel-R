"""M3 of the coordinator's plan (GENERATOR_DESIGN.md 4.1, mirror cross-check).

1. The generic mirror's per-checker verdicts against the Lean-asserted ones of campaign 5's
   expected/Gate5CasesTargets.lean (13 cases x K0, K3 x 3 checkers) and expected/MirrorMutations.lean (19 mutations
   of P0 under K0 x 3 checkers). Those files are check.sh's committed references.
2. gate4.verdicts (the room model of predicted.py and gate4's timing mirror) against the mirror's conjunction, on the
   13 cases and the 6 campaign-6 instances, K0 and K3. Every difference is listed with the mirror's failing
   conditions.

  python -I tests/test_mirror.py IMPL_ROOT
"""
from fractions import Fraction as F
import json
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
sys.path.insert(0, str(HERE))
import legacy  # noqa: E402
import mirror  # noqa: E402
import spec  # noqa: E402
from test_legacy import references  # noqa: E402

NAMES = dict(valid=mirror.VALID, separation=mirror.SEP, calibration=mirror.CAL)


def lean_verdicts(path):
    """{(tag, checker): bool} from `theorem <valid|separation|calibration>_<tag> : ... = <true|false> := by decide +kernel`."""
    out = {}
    for kind, tag, v in re.findall(r"^theorem (valid|separation|calibration)_(\S+) : .* = (true|false) := by decide \+kernel$",
                                   Path(path).read_text(), flags=re.M):
        out[(tag, NAMES[kind])] = v == "true"
    return out


def mutation_spec(name, x, c5, truncate):
    """A mutation of P0 (mirror_mutations.py) as a spec under K0, with the three Lean-text patches of its
    lean_file (rail1, delay, timing2) applied to the spec instead."""
    raw = legacy.spec_of(dict(x, tag=f"M_{name}"), "mirror_mutations.py", c5, budgets=("K0",))
    if "rail1" in x:
        raw["first"]["rail"] = int(x["rail1"])
    if "delay" in x:
        raw["delay"] = [[str(F(x["delay"]))] * 2]
    if "timing2" in x:
        raw["timing"]["right"] = dict(zip(("skew", "deadline", "duration"), (str(F(v)) for v in x["timing2"])))
    if truncate:   # legacy-only option: rows beyond the Lean table sizes are dropped, as Vector.ofFn ignores them
        q1 = raw["first"]["maxWrites"]
        if len(raw["observation"]["firstTrain"]) > q1 + 1:
            truncated = len(raw["observation"]["firstTrain"]) - (q1 + 1)
            raw["observation"]["firstTrain"] = raw["observation"]["firstTrain"][:q1 + 1]
            return raw, truncated
    return raw, 0


def main():
    root = Path(sys.argv[1]).resolve()
    c5, refs = references(root)
    bad = 0
    # 1a. the cases
    want = lean_verdicts(c5 / "expected/Gate5CasesTargets.lean")
    cases = json.loads((c5 / "expected/CASES.json").read_text())["cases"]
    n = 0
    for x in cases:
        s = spec.load(legacy.spec_of(x, "CASES.json", c5))
        for K, (_, pc, fails) in mirror.verdicts(s).items():
            for c in mirror.CHECKERS:
                n += 1
                w = want[(f"{x['tag']}_{K}", c)]
                if pc[c] != w:
                    bad += 1
                    print(f"DIFF cases {x['tag']} {K} {c}: mirror {pc[c]}, Lean-asserted {w}; failing: {fails[:6]}")
    print(f"1a. Gate5CasesTargets.lean: {n - sum(1 for _ in [])} verdicts compared")
    # 1b. the mutations
    want = lean_verdicts(c5 / "expected/MirrorMutations.lean")
    muts = json.loads((c5 / "expected/MUTATIONS.json").read_text())["mutations"]
    m = 0
    for name, x in muts.items():
        try:
            raw, trunc = mutation_spec(name, x, c5, truncate=False)
            s = spec.load(raw)
        except spec.SpecError as e:
            raw, trunc = mutation_spec(name, x, c5, truncate=True)
            s = spec.load(raw)
            print(f"note: mutation {name}: refused by spec.load ({e}); compared with the legacy-only option truncate_rows ({trunc} row(s) beyond the Lean table dropped)")
        _, pc, fails = mirror.verdicts(s)["K0"]
        kinds = sorted({k for _, k, _ in fails})
        line = []
        for c in mirror.CHECKERS:
            m += 1
            w = want[(f"M_{name}", c)]
            line.append(f"{c[5:]}={'T' if pc[c] else 'F'}")
            if pc[c] != w:
                bad += 1
                print(f"DIFF mutation {name} {c}: mirror {pc[c]}, Lean-asserted {w}; failing: {fails[:6]}")
        print(f"   mutation {name:11s}: {', '.join(line)}; mirror's failing kinds: {kinds}")
    print(f"1b. MirrorMutations.lean: {m} verdicts compared")
    print(f"1. per-checker differences from the Lean-asserted references: {bad}")
    # 2. the room model against the mirror
    gate4, _ = legacy.frozen(c5)
    diffs = 0
    for name, xs, source, _ in refs:
        for x in xs:
            s = spec.load(legacy.spec_of(x, source, c5))
            gv = gate4.verdicts(x)
            for K, (conj, pc, fails) in mirror.verdicts(s).items():
                if gv[K] != conj:
                    diffs += 1
                    kinds = {}
                    for ch, kind, where in fails:
                        kinds.setdefault((ch, kind), []).append(where)
                    print(f"2. room model vs mirror: {name} {x['tag']} {K}: gate4.verdicts {gv[K]}, mirror {conj}; "
                          f"per checker {pc}; mirror's failing conditions: " +
                          "; ".join(f"{ch}/{k}: {ws[:3]}{' ...' if len(ws) > 3 else ''}" for (ch, k), ws in kinds.items()))
    print(f"2. room model vs mirror: {diffs} difference(s)")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
