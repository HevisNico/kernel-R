import json, shutil, sys, tempfile, time
from pathlib import Path
sys.path.insert(0, sys.argv[1] + "/tests")
import test_analysis_defects as T
with tempfile.TemporaryDirectory() as t:
    t = Path(t)
    for defect, name, fn, asserts in T.CASES:
        if defect != "L": continue
        w = t / name; w.mkdir(); t0 = time.time()
        try:
            ok, obs = fn(w, None)
        except Exception as e:
            import traceback; traceback.print_exc(); ok, obs = False, dict(setup_error=repr(e))
        print(f"{'PASS' if ok else 'FAIL'} {name} {time.time()-t0:.0f}s {json.dumps({k: obs.get(k) for k in ("changed","exit","reached","raised_in","message","reached_own_check","control_passed","setup_error","commit_made","pushed_to_twin","parsed","unknown_placeholders")})[:600]}", flush=True)
        if not ok and 'stdout' in obs: print('   OUT', obs['stdout'][-400:].replace('\n',' | '), 'ERR', obs['stderr'][-600:].replace('\n',' | '))
        shutil.rmtree(w, ignore_errors=True)
