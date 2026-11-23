"""The direct comparison of CAMPAIGN_PLAN_DRAFT.md §2: a sealed stage-D prediction against one stage-N network
record, letter by letter and output by output. Development only.

  compare_d.py SEALDIR SPEC STAGE_N [noiseless|noisy|auto] [OUT.json]
  STAGE_N: a record file (record.json, or noise2.py's noisy_record.json), or a folder holding record.json

- The seal is verified first (seal.load); a broken seal refuses the comparison.
- The stage-N record is OUT/record.json in the format of instrument.cal_run / run.train_and_test: `words`
  {"layer/cell/group": word}, `tests` (slot indices, info.pattern) and the slots' reads. Its tag and seed must be the
  prediction's.
- The kind of run (the noise module's fields, noise2.py): `noisy` when `noise_seed` is an integer (10 S + round) and
  `noise_scale` is not 0; `noiseless` when `noise_seed` is null or absent, or the scale is 0 (the zero-amplitude
  identity check). It can be stated, and a stated kind that contradicts the record is refused.
- **A comparison is made only where a prediction exists**: eligible at K0 for a run without noise, room at K3 for a
  noisy run. Then every letter of every predicted word, every predicted cell FIRE bit and every output on every input
  pattern, and every both cell in a shift slot (kind `skew`, if the record has any), is compared; a word of the wrong
  length, or a missing word or pattern, is a difference. Verdict `agrees` with zero differences, else `refuted`, with
  every difference listed.
- **Elsewhere**, the verdict is `observed only (no prediction)`: the observed words and outputs are reported as they
  are, with the reason, and nothing is compared; it counts for no claim and no refutation.
"""
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import seal as sealmod  # noqa: E402
import spec as specmod  # noqa: E402

FORMAT = "layered-stage-d-comparison/1"


def run_kind(rec):
    if rec.get("noise_seed") is None:
        return "noiseless"
    return "noiseless" if float(rec.get("noise_scale", 1.0)) == 0 else "noisy"


def observed(s, rec):
    """Observed words, per-pattern cell FIRE bits and outputs, and the shift slots' both cells."""
    cells, outputs = {}, {}
    top = len(s["layers"])
    for idx in rec.get("tests", []):
        sl = rec["slots"][idx]
        key = str(specmod.code(tuple(bool(b) for b in sl["info"]["pattern"])))
        bits = {f"c{r['layer']}_{r['index']}": r["emission"] is not None for r in sl["reads"]}
        cells[key] = bits
        outputs[key] = bits.get(f"c{top}_0")
    skew = []
    for i, sl in enumerate(rec["slots"]):
        if sl.get("kind") == "skew":
            c = (sl.get("info") or {}).get("cell")
            r = next((r for r in sl["reads"] if f"c{r['layer']}_{r['index']}" == c), None)
            skew.append(dict(slot=i, cell=c, fired=None if r is None else r["emission"] is not None))
    return dict(words=dict(rec.get("words", {})), cells=cells, outputs=outputs, skew=skew)


def differences(pred, obs):
    d = []
    for key in sorted(set(pred["words"]) | set(obs["words"])):
        p, o = pred["words"].get(key), obs["words"].get(key)
        if p is None or o is None:
            d.append(dict(what="word", key=key, predicted=p, observed=o, why="missing"))
            continue
        for j in range(max(len(p), len(o))):
            a = p[j] if j < len(p) else None
            b = o[j] if j < len(o) else None
            if a != b:
                d.append(dict(what="letter", key=key, position=j, predicted=a, observed=b))
    for key in sorted(set(pred["outputs"]) | set(obs["outputs"]), key=int):
        if pred["outputs"].get(key) != obs["outputs"].get(key):
            d.append(dict(what="output", pattern=key, predicted=pred["outputs"].get(key), observed=obs["outputs"].get(key)))
        pc, oc = pred["cells"].get(key, {}), obs["cells"].get(key, {})
        for c in sorted(set(pc) | set(oc)):
            if pc.get(c) != oc.get(c):
                d.append(dict(what="cell", pattern=key, cell=c, predicted=pc.get(c), observed=oc.get(c)))
    for x in obs["skew"]:
        if x["cell"] in pred.get("skew_silent", []) and x["fired"] is not False:
            d.append(dict(what="skew", slot=x["slot"], cell=x["cell"], predicted=False, observed=x["fired"]))
    return d


def compare(sealdir, spec_path, outdir, kind="auto"):
    s = specmod.load(spec_path)
    path = Path(outdir)
    rec = json.loads((path / "record.json" if path.is_dir() else path).read_text())
    pred = sealmod.load(sealdir, rec["tag"], rec["seed"])
    rk = run_kind(rec)
    if kind != "auto" and kind != rk:
        raise SystemExit(f"refused: the run is stated {kind} but its record reads {rk}")
    obs = observed(s, rec)
    res = dict(format=FORMAT, tag=rec["tag"], seed=rec["seed"], run_kind=rk, stage_n_status=rec.get("status"),
               noise_seed=rec.get("noise_seed"), noise_round=rec.get("round"), observed=obs)
    if pred is None:
        res.update(verdict="observed only (no prediction)", why="no sealed prediction for this instance")
        return res
    assert pred["tag"] == s["tag"], "the spec is not the prediction's"
    res["prediction_sha256"] = sealmod.sha(sealmod.canon(pred))
    res["inverter_gate"] = pred["inverter_gate"]["source"]
    applies = pred["applies"]["noisy" if rk == "noisy" else "noiseless"]
    if not applies or pred["prediction"] is None:
        why = "not eligible at K0" if not pred["eligible_K0"] else "no room at K3"
        res.update(verdict="observed only (no prediction)", why=why)
        return res
    if rec.get("status") != "done":
        res.update(verdict="run failed", why=rec.get("status"),
                   note="counted under its first failing clause (plan §9); not compared")
        return res
    diffs = differences(pred["prediction"], obs)
    n_letters = sum(len(w) for w in pred["prediction"]["words"].values())
    res.update(verdict="agrees" if not diffs else "refuted", differences=diffs,
               compared=dict(words=len(pred["prediction"]["words"]), letters=n_letters,
                             outputs=len(pred["prediction"]["outputs"]),
                             cell_bits=sum(len(v) for v in pred["prediction"]["cells"].values()),
                             skew_slots=sum(1 for x in obs["skew"] if x["cell"] in pred["prediction"].get("skew_silent", []))))
    return res


if __name__ == "__main__":
    a = sys.argv[1:]
    if len(a) < 3:
        sys.exit(__doc__)
    r = compare(a[0], a[1], a[2], a[3] if len(a) > 3 else "auto")
    text = json.dumps(r, indent=1, sort_keys=True) + "\n"
    if len(a) > 4:
        Path(a[4]).write_text(text)
    print(json.dumps({k: r[k] for k in r if k not in ("observed",)}, indent=1, sort_keys=True))
