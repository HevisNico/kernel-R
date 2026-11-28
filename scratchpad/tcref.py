import sys, json, importlib.util
from pathlib import Path
tc, wd, root = sys.argv[1:4]
spec = importlib.util.spec_from_file_location("tc", tc); m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
w = m.Work(wd)
ok, d = m.case_analysis_refuses_test_root(w, root)
print("analysis_refuses", "PASS" if ok else "FAIL"); print(json.dumps(d, indent=1))
