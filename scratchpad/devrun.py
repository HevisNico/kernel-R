import json, sys, time
from pathlib import Path
sys.path.insert(0, sys.argv[1] + "/tests")
import test_campaign as T
w = T.Work(sys.argv[2])
home = dict(root=Path(sys.argv[3]), remote=Path(sys.argv[4]))
out = {}
for name in sys.argv[5:]:
    t0 = time.time()
    f = getattr(T, "case_" + name)
    try:
        ok, d = f(w, home["root"] if name in ("analysis_refuses_test_root", "analysis_forged_pins") else home)[:2]
    except Exception as e:
        import traceback; ok, d = False, dict(error=traceback.format_exc()[-1500:])
    out[name] = dict(ok=ok, seconds=round(time.time() - t0), detail=d)
    print(name, "PASS" if ok else "FAIL", round(time.time() - t0), flush=True)
Path(sys.argv[2], "DEV.json").write_text(json.dumps(out, indent=1, default=str))
