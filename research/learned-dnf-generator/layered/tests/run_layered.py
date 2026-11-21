"""Step 2 of the layered phase: writes the Lean files of tests 4(b), 4(c) and the controls of
LAYERED_GENERATOR_DESIGN.md, with the mirror's per-checker verdicts asserted, and REPORT.json.

  python -I tests/run_layered.py OUT_DIR

  Synth_<net>.lean   the nine networks of 2.2, each at residual rules zero, plus, minus, seeded:7 (tags <net>_<rule>);
                     per spec the four checker theorems, checks_*, outputs_* and function_* (the stated function)
  Mut_<base>.lean    the mutations of lmutate.py on AND3a, OR3a and MAJa (seeded:7 bases); every one asserts its
                     per-checker values, at least one false. Mutations that cannot be built on a base are reported
  Control_pass.lean, Control_fail.lean, Flip_*.lean   the flip controls (tests/flip_check.py of the two-layer
                     generator checks them line by line)
  REPORT.json        every verdict, failing kind, physical report, and the missing-row refusal
"""
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent.parent / "tests"))
import lemit  # noqa: E402
import lmirror  # noqa: E402
import lmutate  # noqa: E402
import lspec  # noqa: E402
import lsynth  # noqa: E402
from networks import NETWORKS  # noqa: E402
from run_synth import flips  # noqa: E402   (the two-layer generator's flip writer; it matches `= true|false := by decide +kernel`)

RULES = ("zero", "plus", "minus", "seeded:7")
BASES = ("AND3a", "OR3a", "MAJa")


def write(path, raws):
    specs, pcs, rep = [], {}, []
    for raw in raws:
        s = lspec.load(raw)
        conj, pc, fails = lmirror.verdicts(s)
        specs.append(s)
        pcs[s["tag"]] = pc
        rep.append(dict(file=path.name, tag=s["tag"], widths=s["widths"], mirror=conj, per_checker=pc,
                        failing_kinds=sorted({k for _, k, _ in fails}), physical=s["physical"]))
    path.write_text(lemit.lean_file(specs, pcs, f"tests/run_layered.py ({path.stem})"))
    return rep


def main():
    od = Path(sys.argv[1])
    od.mkdir(parents=True, exist_ok=True)
    report = dict(cases=[], mutations=[], not_applicable=[], controls=[])
    bases = {}
    for tag, (net, f) in NETWORKS.items():
        raws = []
        for rule in RULES:
            raw = lsynth.observation(lsynth.design(f"{tag}_{rule.replace(':', '')}", 3, net, f), rule)
            raws.append(raw)
            if rule == "seeded:7":
                bases[tag] = raw
        report["cases"] += write(od / f"Synth_{tag}.lean", raws)
    for b in BASES:
        raws, kinds = [], {}
        for name in lmutate.KIND:
            try:
                raws.append(lmutate.mutate(bases[b], name))
                kinds[raws[-1]["tag"]] = (name, lmutate.KIND[name])
            except lmutate.NotApplicable as e:
                report["not_applicable"].append(dict(base=b, mutation=name, why=str(e)))
        for r in write(od / f"Mut_{b}.lean", raws):
            name, want = kinds[r["tag"]]
            r.update(mutation=name, intended_kinds=sorted(want), only_its_kind=bool(r["failing_kinds"]) and set(r["failing_kinds"]) <= want)
            report["mutations"].append(r)
    net, f = NETWORKS["AND3a"]
    passing = lsynth.observation(lsynth.design("C0", 3, net, f), "zero")
    write(od / "Control_pass.lean", [passing])
    failing = lmutate.mutate(passing, "residual")
    failing["tag"] = "C1"
    write(od / "Control_fail.lean", [failing])
    report["controls"] = flips(od / "Control_pass.lean", od, "Flip_pass_") + flips(od / "Control_fail.lean", od, "Flip_fail_")
    bad = lsynth.observation(lsynth.design("C2", 3, net, f), "zero")
    bad["training"][1][0][0] = bad["training"][1][0][0][:-1]
    try:
        lspec.load(bad)
        report["missing_row_refused"] = False
    except lspec.SpecError as e:
        report["missing_row_refused"] = str(e)
    (od / "REPORT.json").write_text(json.dumps(report, indent=1) + "\n")
    print(f"cases: {len(report['cases'])} specs, all mirror-true: {all(r['mirror'] for r in report['cases'])}")
    print(f"mutations: {len(report['mutations'])}, all mirror-false: {not any(r['mirror'] for r in report['mutations'])}, "
          f"all only their kind: {all(r['only_its_kind'] for r in report['mutations'])}; not applicable: "
          + "; ".join(f"{x['base']}/{x['mutation']}: {x['why']}" for x in report["not_applicable"]))
    print(f"controls: {len(report['controls'])} flipped files; missing row refused: {report['missing_row_refused']}")


if __name__ == "__main__":
    main()
