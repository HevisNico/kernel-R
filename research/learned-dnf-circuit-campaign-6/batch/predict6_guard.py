"""Campaign 6's development batch: the guard of STOPPING_RULE_AMENDMENT_1.md (the owner's ruling): an instance on which
the batch's prediction code raises an error is not eligible. New code; predict6.py and every file of the marker are
unchanged, and nothing else is changed.

  predict6_guard.py predict BATCH_DIR OUT_DIR        predict6.py predict, with the guard below

The guard wraps only the call of campaign 5's frozen `P.instance` that `predict6.predict_instance` makes, for each
instance and for the duration of this run (`mock.patch.object`, restored on exit). If that call raises, the instance
gets, in place of P.instance's result:

  measured = True             (section 3 found it measured: the call is made only after measure_instance passed)
  eligible = False, why_not_eligible = ["the frozen prediction code failed (<type>: <message>)"]
  prediction_failed = the same text

It has no `budgets` and no `observation`, so the rest of predict6 handles it unchanged: `augmented` returns it as it is,
`gate_each` writes no Lean file for it and sets gate_K0 = False, and report6 lists it under not_eligible with that
reason and leaves it out of k. No fallback fit is made and nothing is skipped: every instance on which P.instance does
not raise gets exactly predict6's result.
"""
import json
from pathlib import Path
import sys
from unittest import mock

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import predict6                                         # noqa: E402
P = predict6.P
FROZEN_INSTANCE = P.instance


def reason(e):
    return f"the frozen prediction code failed ({type(e).__name__}: {e})"


def guarded_instance(seed, *args, **kwargs):
    """P.instance, unchanged; on any exception, the not-eligible record of the amendment."""
    try:
        return FROZEN_INSTANCE(seed, *args, **kwargs)
    except Exception as e:                              # noqa: BLE001  (the amendment: any error of the prediction code)
        why = reason(e)
        return dict(seed=seed, measured=True, eligible=False, why_not_eligible=[why], prediction_failed=why)


def predict_batch(batch_dir, out_dir, check=True):
    with mock.patch.object(P, "instance", guarded_instance):
        return predict6.predict_batch(batch_dir, out_dir, check)


if __name__ == "__main__":
    import batch6
    import c4
    batch6.require_debug()
    a = sys.argv[1:]
    print(c4.require_pinned())
    if not (len(a) == 3 and a[0] == "predict"):
        raise SystemExit("predict6_guard.py predict BATCH_DIR OUT_DIR")
    xs = predict_batch(a[1], a[2])
    print(json.dumps(dict(measured=[x["seed"] for x in xs if x.get("measured")], eligible=[x["seed"] for x in xs if x.get("gate_K0")],
                          prediction_failed=[x["seed"] for x in xs if x.get("prediction_failed")])))
