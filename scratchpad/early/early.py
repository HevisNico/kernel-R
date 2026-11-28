import importlib.util, json, subprocess, sys, tempfile
from pathlib import Path
def load(p, n):
    s = importlib.util.spec_from_file_location(n, p); m = importlib.util.module_from_spec(s); s.loader.exec_module(m); return m
S = Path(sys.argv[1])
FIX = load(S / "fixwt/research/layered-networks/sealpush.py", "sp_fixed")
OLD = load(S / "dev/research/layered-networks/sealpush.py", "sp_old")
remote = "https://github.com/HevisNico/kernel-R"
out = {}
for k in ("02", "03", "05", "06"):
    b = f"evidence/devtest-seals2-K{k}"
    ls = subprocess.run(["git", "ls-remote", remote, f"refs/heads/{b}"], capture_output=True, text=True).stdout.strip()
    if not ls:
        out[b] = dict(exists=False); continue
    with tempfile.TemporaryDirectory() as w:
        lines = OLD.log_lines(remote, b, w)
    raw = json.loads(subprocess.run(["gh", "api", "-X", "GET", "repos/HevisNico/kernel-R/activity", "-f", f"ref=refs/heads/{b}",
                                     "--paginate"], capture_output=True, text=True, check=True).stdout.replace("][", ","))
    types = {x["after"]: x["activity_type"] for x in raw}
    old, new = OLD.times(remote, b, "github"), FIX.times(remote, b, "github")
    out[b] = dict(exists=True, tip=ls.split()[0], seals=[dict(instance=x["instance"], commit=x["commit"],
        activity_type=types.get(x["commit"]), unfixed_time=old.get(x["commit"]), fixed_time=new.get(x["commit"])) for x in lines],
        activity_items=[dict(activity_type=x["activity_type"], before=x["before"], after=x["after"], timestamp=x["timestamp"]) for x in raw])
json.dump(out, open(S / "early/EARLY_GITHUB_TIMES.json", "w"), indent=1, sort_keys=True)
for b, v in out.items():
    print(b, "absent" if not v["exists"] else "")
    for s in v.get("seals", []):
        print("  ", s["instance"], s["commit"][:8], s["activity_type"], "unfixed:", s["unfixed_time"], "fixed:", s["fixed_time"])
