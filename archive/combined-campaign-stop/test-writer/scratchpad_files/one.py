import json, sys, tempfile
from pathlib import Path
sys.path.insert(0, sys.argv[1] + "/tests")
import test_analysis_defects as T
names = sys.argv[2].split(",")
with tempfile.TemporaryDirectory() as t:
    t = Path(t)
    for d, n, fn, _ in T.CASES:
        if n in names:
            w = t / n; w.mkdir(); ok, obs = fn(w, None)
            print(ok, n, json.dumps(obs)[:700])
