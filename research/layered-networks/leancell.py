"""The kernel on the R cells of sealed predictions (the owner's item K, relayed 2026-11-26). Development only; it
runs no simulation and changes no sealed file.

For every prediction.json given and every measured cell, at K0 and K3, the sealed `lean_cell` becomes a Lean `Cell`
literal. Each clause of fit.cell_valid, the Python mirror of Cell.Valid (LayeredMonotoneTarget.lean), becomes one
theorem by `decide +kernel`, stating the mirror's value of that clause (true when its slack is > 0):
- dose > 0;
- per group: 0 < stop ≤ maxWrites, `stop g = <mirror's stop>`, the early silences k < stop, the stop margin;
- per port: the rail;
- the silent masks and the anchors.

Two theorems come on top: `Checker.cellValid C = <mirror's valid>` (the library's Boolean, sound and complete for
Cell.Valid by LayeredMonotoneCheckerProofs.lean, so it also covers any clause the mirror might lack), and the sealed
failing list must equal the mirror's failing list recomputed here (in Python: the sealed record against fit.py).

The kernel's verdict per clause is read from Lean's errors: a theorem that does not check is a disagreement at its
line. One file per prediction.

  leancell.py OUTDIR BUILD MANIFEST.json      MANIFEST: [{"label": ..., "prediction": path}, ...]
  writes OUTDIR/<label>.lean, OUTDIR/<label>.log and OUTDIR/LEANCELL.json; BUILD holds the compiled library modules
"""
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import fit as fitmod  # noqa: E402
import spec as specmod  # noqa: E402

FIN = "(%d : Fin 2)"


def pat(x):
    """A Pattern 2 literal for the ports in x (1-based)."""
    a, b = (1 in x), (2 in x)
    return f"(fun a : Fin 2 => if a.val = 0 then {str(a).lower()} else {str(b).lower()})"


def mirror(lc):
    p = dict(lc, gain={1: int(lc["gain"]["1"]), 2: int(lc["gain"]["2"])})
    valid, clauses = fitmod.cell_valid(p)
    stops = {g: fitmod.stop(p, g) for g in range(specmod.GROUPS[p["gate"]])}
    return p, valid, clauses, stops


def lean_of(name, clause, p, stops):
    """The Lean proposition of one fit.cell_valid clause."""
    C = name
    if clause == "dose > 0":
        return f"0 < {C}.dose"
    m = re.match(r"g(\d): (.*)", clause)
    if m:
        g, rest = int(m.group(1)), m.group(2)
        if rest.startswith("0 < stop"):
            return f"0 < {C}.stop {FIN % g} ∧ {C}.stop {FIN % g} ≤ {C}.maxWrites"
        k = re.match(r"early silence k=(\d+)", rest)
        if k:
            return f"{C}.groupScore {FIN % g} {k.group(1)} + {C}.trainError < {C}.threshold"
        if rest == "stop margin":
            return f"{C}.threshold + {C}.trainError ≤ {C}.groupScore {FIN % g} ({C}.stop {FIN % g})"
    m = re.match(r"rail port (\d)", clause)
    if m:
        return f"{C}.gain {C}.expectedWrites {FIN % (int(m.group(1)) - 1)} < {C}.rail"
    m = re.match(r"silent mask (\(.*\))", clause)
    if m:
        x = eval(m.group(1))                              # a tuple literal written by fit.cell_valid
        return f"{C}.score {C}.expectedWrites {pat(x)} + {C}.testError < {C}.threshold"
    m = re.match(r"anchor (\(.*\))", clause)
    if m:
        y = eval(m.group(1))
        return f"{C}.threshold + {C}.testError ≤ {C}.score {C}.expectedWrites {pat(y)}"
    raise ValueError(clause)


def emit(label, pred):
    o = ["import LayeredMonotoneCheckerProofs", "", f"namespace LearnedCoincidence.Layered.Kc_{label}", "",
         "set_option maxRecDepth 100000", ""]
    rows, line_of = [], {}
    for c in pred.get("cells", []):
        if not c.get("measured"):
            continue
        for K in ("K0", "K3"):
            lc = c["lean_cell"][K]
            p, valid, clauses, stops = mirror(lc)
            name = f"{c['cell']}_{K}"
            o.append(f"def {name} : Cell := {{ gate := .{p['gate']}, initialGain := fun a => if a.val = 0 then "
                     f"{p['gain'][1]} else {p['gain'][2]}, help := {p['help']}, threshold := {p['threshold']}, "
                     f"trainError := {p['trainError']}, testError := {p['testError']}, dose := {p['dose']}, "
                     f"maxWrites := {p['maxWrites']}, rail := {p['rail']} }}")
            sealed = sorted(x.split(" (slack")[0] for x in (c.get(K) or {}).get("failing") or [])
            recomputed = sorted(nm for nm, sl in clauses if sl <= 0)
            stmts = [("cellValid", f"Checker.cellValid {name} = {'true' if valid else 'false'}", valid)]
            stmts += [(f"stop g{g}", f"{name}.stop {FIN % g} = {st}", True) for g, st in stops.items()]
            stmts += [(nm, f"decide ({lean_of(name, nm, p, stops)}) = {'true' if sl > 0 else 'false'}", sl > 0)
                      for nm, sl in clauses]
            for j, (nm, st, val) in enumerate(stmts):
                o.append(f"theorem {name}_t{j} : {st} := by decide +kernel")
                line_of[len(o)] = (c["cell"], K, nm)
                rows.append(dict(cell=c["cell"], level=K, clause=nm, mirror=val))
            rows.append(dict(cell=c["cell"], level=K, clause="sealed failing = recomputed mirror failing",
                             mirror=sealed == recomputed, python_only=True, sealed=sealed, recomputed=recomputed))
        o.append("")
    o += [f"end LearnedCoincidence.Layered.Kc_{label}", ""]
    return "\n".join(o), rows, line_of


def main(outdir, build, manifest):
    out = Path(outdir).resolve()
    out.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, LEAN_PATH=str(Path(build).resolve()))
    report = []
    for m in json.loads(Path(manifest).read_text()):
        label = re.sub(r"[^A-Za-z0-9_]", "_", m["label"])
        pred = json.loads(Path(m["prediction"]).read_text())
        text, rows, line_of = emit(label, pred)
        f = out / f"{label}.lean"
        f.write_text(text)
        t0 = time.time()
        p = subprocess.run(["lean", "-DwarningAsError=true", str(f)], cwd=out, env=env, capture_output=True, text=True,
                           timeout=3600)
        secs = round(time.time() - t0, 2)
        log = p.stdout + p.stderr
        (out / f"{label}.log").write_text(log)
        bad_lines = {int(x) for x in re.findall(rf"{re.escape(f.name)}:(\d+):\d+: error", log)}
        unplaced = sorted(n for n in bad_lines if n not in line_of)
        disagree = sorted({line_of[n] for n in bad_lines if n in line_of})
        kernel_rows = [r for r in rows if not r.get("python_only")]
        report.append(dict(
            label=m["label"], prediction=str(m["prediction"]), seconds=secs, lean_rc=p.returncode,
            cells=sorted({r["cell"] for r in rows}), theorems=len(kernel_rows),
            kernel_agrees_everywhere=p.returncode == 0 and not bad_lines,
            disagreements=[dict(cell=c, level=k, clause=n) for c, k, n in disagree], unplaced_error_lines=unplaced,
            sealed_failing_equals_mirror=all(r["mirror"] for r in rows if r.get("python_only")),
            mirror_failing={f"{r['cell']} {r['level']}": r["recomputed"] for r in rows if r.get("python_only")},
            eligible_K0=pred.get("eligible_K0"), room_K3=pred.get("room_K3")))
        print(json.dumps({k: report[-1][k] for k in ("label", "seconds", "theorems", "kernel_agrees_everywhere",
                                                     "sealed_failing_equals_mirror")}), flush=True)
    summary = dict(format="layered-leancell/1", predictions=len(report),
                   theorems=sum(r["theorems"] for r in report),
                   all_agree=all(r["kernel_agrees_everywhere"] and r["sealed_failing_equals_mirror"] for r in report),
                   seconds_total=round(sum(r["seconds"] for r in report), 1), runs=report)
    (out / "LEANCELL.json").write_text(json.dumps(summary, indent=1, sort_keys=True) + "\n")
    return summary["all_agree"]


if __name__ == "__main__":
    sys.exit(0 if main(*sys.argv[1:]) else 1)
