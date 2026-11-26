"""Re-gating of the development instances under the one-port rule (DECISIONS_3.md, condition 2). Development only.

  regate3.py OUTROOT [rule=one-port|max]

For 9801 NOT1, 9802 ANDOR3, 9803 XOR3, with copies of their records (no pushed folder is written into):
  D       the stage-D record (dev/stage_d_*): stage_d.predict under the rule (prediction.json, fit_d.json, with
          `testError_rule` added), and every measured cell as a Lean `Cell` at K0 and K3 with `Checker.cellValid` and each
          group's `Cell.stop` stated at the mirror's values, checked by `decide +kernel` (leanfit.emit, unchanged);
  insitu  the in-situ record of the same instance and seed (dev/cal5_not1, dev/cal5_andor3, dev/cal6_xor3: training,
          tests and scans in one session): leancal.py (no front end, and NOT1 as before) or leancal2.py (XOR3: closed
          by `layered_inverters_chained`) under the rule: the calibrated cascade, the scored traces and the recognition
          theorem at K0 and K3, checked by the kernel.
The kernel agrees with the mirror when every generated file is accepted (each theorem states the mirror's value).
Writes OUTROOT/REGATE3.json.
"""
import json
from pathlib import Path
import shutil
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import fit3  # noqa: E402
import lean as leanmod  # noqa: E402
import leanfit  # noqa: E402
import seal as sealmod  # noqa: E402
import spec as specmod  # noqa: E402
import stage_d  # noqa: E402

CFG = json.loads((HERE / "config.json").read_text())
INSTANCES = [
    dict(spec="specs/not1.json", seed=9801, D="dev/stage_d_not1", inv="assumed", insitu="dev/cal5_not1", cal="leancal"),
    dict(spec="specs/andor3.json", seed=9802, D="dev/stage_d_andor3", inv=None, insitu="dev/cal5_andor3", cal="leancal"),
    dict(spec="specs/xor3.json", seed=9803, D="dev/stage_d_xor3", inv="inverters/inverter_gate.json", insitu="dev/cal6_xor3",
         cal="leancal2"),
]


def copy(src, dst, names):
    dst.mkdir(parents=True, exist_ok=True)
    for n in names:
        if (src / n).exists():
            (dst / n).parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(src / n, dst / n)


def stage_d_part(x, out, rule):
    d = out / "D"
    copy(HERE / x["D"], d, ["record.json", "overlay_d.json", "inverters/inverter_gate.json", "inverters/SHA256SUMS"])
    inv = None if x["inv"] is None else (x["inv"] if x["inv"] == "assumed" else str(d / x["inv"]))
    with fit3.rule(rule):
        p = stage_d.predict(HERE / x["spec"], d, inv)
    p["testError_rule"] = rule
    p["format"] = "layered-stage-d-prediction/2"
    (d / "prediction.json").write_bytes(stage_d.canon(p))
    s = specmod.load(HERE / x["spec"])
    fitd = json.loads((d / "fit_d.json").read_text())
    path = d / f"Fit{s['tag']}.lean"
    path.write_text(leanfit.emit(s, fitd))
    leanmod.build_modules(CFG, HERE / "build")
    r = leanmod.check(CFG, path, HERE / "build")
    cells = {}
    for cf in fitd["cells"]:
        cells[cf["cell"]] = None if not cf["measured"] else {
            K: dict(mirror_valid=cf["verdicts"][K]["valid"], verdict=cf["verdicts"][K]["ok"],
                    failing=cf["verdicts"][K]["failing"], testError=cf["budgets"][K]["testError"],
                    rule=cf.get("testError_rule", "fit.py")) for K in ("K0", "K3")}
    return dict(eligible_K0=p["eligible_K0"], room_K3=p["room_K3"], inverter_gate=p["inverter_gate"]["source"],
                prediction_sha256=sealmod.sha(stage_d.canon(p)), cells=cells, lean_file=path.name,
                kernel_accepted=r["accepted"], kernel_output=None if r["accepted"] else r.get("output", "")[-3000:])


def insitu_part(x, out, rule):
    d = out / "insitu"
    copy(HERE / x["insitu"], d, ["record.json", "overlay.json"])
    mod = __import__(x["cal"])
    with fit3.rule(rule):
        ok = mod.main(HERE / x["spec"], d)
    res = json.loads((d / f"{x['cal']}.json").read_text())
    if not res.get("emitted"):
        return dict(emitted=False, why=res.get("why"))
    files = {K: dict(file=v["file"], kernel_accepted=v["accepted"], recognition_theorem=v["recognition_theorem"],
                     mirror_false=[k for k, b in v["mirror"].items() if not b])
             for K, v in res["files"].items()}
    return dict(emitted=True, all_accepted=bool(ok), files=files)


def main(root, *rest):
    rule = dict(a.split("=", 1) for a in rest).get("rule", "one-port")
    root = Path(root).resolve()
    out = {}
    for x in INSTANCES:
        s = specmod.load(HERE / x["spec"])
        o = root / f"{s['tag']}_{x['seed']}"
        out[o.name] = dict(rule=rule, stage_d=stage_d_part(x, o, rule), insitu=insitu_part(x, o, rule))
        print(o.name, json.dumps(out[o.name], indent=1, default=str))
    (root / "REGATE3.json").write_text(json.dumps(out, indent=1, sort_keys=True, default=str) + "\n")


if __name__ == "__main__":
    main(*sys.argv[1:])
