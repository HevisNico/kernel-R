"""Partial Lean check of fit.py's mirror (M3): every fitted cell as a Lean `Cell` literal at K0 and K3, with
`Checker.cellValid` (sound and complete for Cell.Valid, LayeredMonotoneCheckerProofs.lean) and each group's
`Cell.stop` stated at the Python mirror's values, by decide +kernel. The calibration checkers on the traces are M4.

  leanfit.py SPEC OUT     writes OUT/Fit<TAG>.lean and OUT/leanfit.json
"""
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import fit as fitmod  # noqa: E402
import lean as leanmod  # noqa: E402
import spec as specmod  # noqa: E402

CFG = json.loads((HERE / "config.json").read_text())


def emit(s, r):
    o = ["import LayeredMonotoneCheckerProofs", "", f"namespace LearnedCoincidence.Layered.Fit{s['tag']}", "",
         "set_option maxRecDepth 100000", ""]
    for c in r["cells"]:
        if not c["measured"]:
            o.append(f"-- {c['cell']}: not measured ({'; '.join(c['why_not_measured'])})")
            continue
        for K in ("K0", "K3"):
            p = c["lean_cell"][K]
            name = f"{c['cell']}_{K}"
            o.append(f"def {name} : Cell := {{ gate := .{p['gate']}, initialGain := fun a => if a.val = 0 then "
                     f"{p['gain']['1']} else {p['gain']['2']}, help := {p['help']}, threshold := {p['threshold']}, "
                     f"trainError := {p['trainError']}, testError := {p['testError']}, dose := {p['dose']}, "
                     f"maxWrites := {p['maxWrites']}, rail := {p['rail']} }}")
            v = c["verdicts"][K]["valid"]
            o.append(f"theorem {name}_valid : Checker.cellValid {name} = {'true' if v else 'false'} := by decide +kernel")
            for g in range(specmod.GROUPS[p["gate"]]):
                st = fitmod.stop(dict(p, gain={1: p["gain"]["1"], 2: p["gain"]["2"]}), g)
                o.append(f"theorem {name}_stop{g} : {name}.stop {g} = {st} := by decide +kernel")
        o.append("")
    o += [f"end LearnedCoincidence.Layered.Fit{s['tag']}", ""]
    return "\n".join(o)


def main(spec_path, out):
    out = Path(out).resolve()
    s = specmod.load(spec_path)
    r = json.loads((out / "fit.json").read_text())
    path = out / f"Fit{s['tag']}.lean"
    path.write_text(emit(s, r))
    leanmod.build_modules(CFG, HERE / "build")
    res = dict(file=path.name, **leanmod.check(CFG, path, HERE / "build"))
    (out / "leanfit.json").write_text(json.dumps(res, indent=1) + "\n")
    print(json.dumps({k: v for k, v in res.items() if k != "output" or not res["accepted"]}, indent=1))
    return res["accepted"]


if __name__ == "__main__":
    sys.exit(0 if main(sys.argv[1], sys.argv[2]) else 1)
