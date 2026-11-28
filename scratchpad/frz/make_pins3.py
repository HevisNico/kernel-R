"""Regenerate FREEZE_PINS.json for the tree at TOP (format layered-freeze-pins/1), against the dff747c4 pins."""
import hashlib, json, subprocess, sys
from pathlib import Path
top = Path(sys.argv[1]); closure = json.loads(Path(sys.argv[2]).read_text())["files"]
LN = "research/layered-networks/"
old = json.loads(subprocess.run(["git", "-C", str(top), "show", "dff747c4:" + LN + "FREEZE_PINS.json"], capture_output=True, check=True).stdout)
oldfiles = {p for fs in old["groups"].values() for p in fs}
G_OLD = {k: v for k, v in old["groups"].items()}
def g(name):
    return [k for k in G_OLD if k.startswith(name)][0]
camp = [LN + "campaign.py", LN + "analysis.py", LN + "campaign_template.json"]
kernel = list(G_OLD[g("the kernel at stage D")])
config = list(G_OLD[g("configuration and specs")])
skip = set(camp) | set(kernel) | set(config) | {LN + "FREEZE_PINS.json", "requirements.txt", LN + "EXCLUDED.json", LN + "EXCLUDED_PRINT.txt"}
code = sorted(set(f for f in closure if f not in skip) | {LN + "noise4_gate/sitecustomize.py"})
groups = {
 "campaign: the driver, the analysis and the template (MUST_BE_PINNED)": camp,
 "code the campaign runs, imports or reads (closure of campaign.py, analysis.py, plan_split3, draw_seeds, beacon_verify, beacon_chain, d4_regate, leancell and tests/check_duplicate; noise4_gate/sitecustomize.py, which indeck_noise4 puts on the path)": code,
 "the seed draw's exclusion list": [LN + "EXCLUDED.json", LN + "EXCLUDED_PRINT.txt"],
 "configuration and specs read by that code": config,
 "the kernel at stage D (stage_d6, leancell) and the Lean sources of the CheckerProofs closure not pinned above": kernel,
 "Lean gate (per-instance gate and its proof)": list(G_OLD[g("Lean gate")]),
 "inverter kit (research/inverter-instances d599300d)": list(G_OLD[g("inverter kit")]),
 "freeze reports (read-only answers and data the freeze relies on)": list(G_OLD[g("freeze reports")]),
 "reports of 2026-11-26 (read-only)": list(G_OLD[g("reports of 2026-11-26")]),
}
sha = lambda p: hashlib.sha256((top / p).read_bytes()).hexdigest()
out_groups = {k: {p: sha(p) for p in sorted(v)} for k, v in groups.items()}
new = {p for fs in out_groups.values() for p in fs}
assert len(new) == sum(len(v) for v in out_groups.values()), "a file in two groups"
oldsha = {p: h for fs in old["groups"].values() for p, h in fs.items()}
tools = dict(old["tools"])
tools["kernel_library"] = ("LayeredMonotoneCheckerProofs and its 11 imports, built per machine by campaign.py (build_kernel) and by "
                           "analysis.py from the sources pinned here (campaign.KERNEL_SOURCES)")
d = dict(format=old["format"], base=sys.argv[4],
         count=len(new), groups=out_groups, tools=tools,
         against_dff747c4=dict(added=sorted(new - oldfiles), removed=sorted(oldfiles - new),
                               changed=sorted(p for p in new & oldfiles if oldsha[p] != out_groups[[k for k in out_groups if p in out_groups[k]][0]][p]),
                               tools_changed=sorted(k for k in tools if tools[k] != old["tools"].get(k))))
Path(sys.argv[3]).write_text(json.dumps(d, indent=1, sort_keys=True) + "\n")
print(len(new), json.dumps(d["against_dff747c4"], indent=0))
