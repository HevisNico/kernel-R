import json, sys, subprocess, tempfile, os, hashlib, re
L = "/home/user/review_clone/research/layered-networks"; sys.path.insert(0, L)
import analysis as A, campaign as CP
RW = "/home/user/rescan_work"
SB = open(f"{RW}/EXCLUDED_SECOND_SCAN.json", "rb").read(); HS = hashlib.sha256(SB).hexdigest()
LS = open(f"{RW}/SCAN_LSREMOTE.txt", "rb").read()
F = "7fa3693ea85a85dde8490e0efdb9eafa80ff7189"
pins = {p: h for fs in json.loads(CP.PINS.read_text())["groups"].values() for p, h in fs.items()}
DS, AN = pins["research/layered-networks/draw_seeds.py"], pins["research/layered-networks/analysis.py"]
B = A.VERIFY_BRANCH
def inputs(**o):
    d = dict(format="layered-scan-verify-inputs/2", freeze_commit=F, draw_seeds_py_sha256=DS, analysis_py_sha256=AN,
             scan_to_verify_sha256=HS, reproduced_scan_sha256=HS, verify_lsremote_sha256=hashlib.sha256(o.pop("vl", LS)).hexdigest(),
             scan_lsremote_sha256=hashlib.sha256(o.pop("sl", LS)).hexdigest(), git_version="git version 2.43.0", python_version="3.13.18")
    d.update(o); return "".join(f"{k} {v}\n" for k, v in d.items() if v is not None)
def honest(**o):
    vl, sl = o.pop("VL", LS), o.pop("SL", LS)
    return {"VERIFY.txt": o.pop("V", f"the scan is reproduced scan_sha256 {HS} VS {HS}\n"),
            "VERIFY_INPUTS.txt": o.pop("I", inputs(vl=vl, sl=sl)), "VERIFY_LSREMOTE.txt": vl, "SCAN_LSREMOTE.txt": sl}
ENV = dict(os.environ, GIT_AUTHOR_NAME="t", GIT_AUTHOR_EMAIL="t@t", GIT_COMMITTER_NAME="t", GIT_COMMITTER_EMAIL="t@t")
def twin(files, activity="ok"):
    d = tempfile.mkdtemp(); bare = f"{d}/twin.git"; w = f"{d}/w"
    subprocess.run(["git", "init", "-q", "--bare", bare], check=True); subprocess.run(["git", "init", "-q", w], check=True)
    subprocess.run(["git", "-C", w, "checkout", "-q", "--orphan", B], check=True)
    for n, t in files.items():
        if t is None: continue
        open(f"{w}/{n}", "wb").write(t if isinstance(t, bytes) else t.encode())
    subprocess.run(["git", "-C", w, "add", "-A"], check=True); subprocess.run(["git", "-C", w, "commit", "-q", "-m", "r"], check=True, env=ENV)
    subprocess.run(["git", "-C", w, "push", "-q", bare, f"HEAD:refs/heads/{B}"], check=True, capture_output=True)
    c = subprocess.run(["git", "-C", w, "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
    os.makedirs(f"{bare}/ACTIVITY")
    bc = dict(activity_type="branch_creation", after=c, before="0" * 40, ref=f"refs/heads/{B}", timestamp="2026-11-29T10:00:00Z")
    acts = dict(ok=[bc],
                force_away_back=[bc, dict(bc, activity_type="force_push", after="d" * 40, before=c, timestamp="2026-11-29T10:01:00Z"),
                                 dict(bc, activity_type="force_push", after=c, before="d" * 40, timestamp="2026-11-29T10:02:00Z")],
                delete_recreate=[bc, dict(bc, activity_type="branch_deletion", after="0" * 40, before=c, timestamp="2026-11-29T10:01:00Z"),
                                 dict(bc, timestamp="2026-11-29T10:02:00Z")],
                none=[])[activity]
    open(f"{bare}/ACTIVITY/{A.safe(B)}.json", "w").write(json.dumps(acts))
    return bare
res = {}
def run(name, files, activity="ok", hs=HS, sb=SB, f=F):
    bare = twin(files, activity)
    try:
        c, s, v = A.scan_verify_record(bare, hs, sb, f)
        t = A.record_created(bare, c, tempfile.mkdtemp())
        res[name] = "ACCEPTED"
    except A.Refused as e: res[name] = "refused: " + str(e)[:170]
    except Exception as e: res[name] = f"EXCEPTION {type(e).__name__}: {e}"[:170]
    return bare
HONEST = run("honest", honest())
run("1_success_line_only", {"VERIFY.txt": f"the scan is reproduced scan_sha256 {HS} VS {HS}\n"})
run("2a_other_freeze_wellformed", honest(I=inputs(freeze_commit="e" * 40)))
run("2b_empty_freeze_in_record", honest(I=inputs(freeze_commit="")))
run("2c_expected_freeze_empty", honest(), f="")
run("2d_expected_freeze_other", honest(), f="e" * 40)
lines = LS.decode().splitlines(); t0, r0 = lines[3].split()
bad = "\n".join(lines[:3] + [("f" * 40) + "\t" + r0] + lines[4:]) + "\n"
run("3a_wrong_sha_in_VERIFY_LSREMOTE", honest(VL=bad.encode()))
run("3b_wrong_sha_in_SCAN_LSREMOTE", honest(SL=bad.encode()))
run("4a_problem_line_first", honest(V=f"PROBLEM: x\nthe scan is reproduced scan_sha256 {HS} VS {HS}\n"))
run("4b_problem_line_after", honest(V=f"the scan is reproduced scan_sha256 {HS} VS {HS}\nPROBLEM: x\n"))
run("4c_indented_problem", honest(V=f"  PROBLEM: x\nthe scan is reproduced scan_sha256 {HS} VS {HS}\n"))
run("4d_lowercase_problem", honest(V=f"problem: x\nthe scan is reproduced scan_sha256 {HS} VS {HS}\n"))
run("5a_force_away_and_back", honest(), activity="force_away_back")
run("5b_delete_and_recreate", honest(), activity="delete_recreate")
run("5c_no_activity", honest(), activity="none")
run("6a_inputs_pins_other", honest(I=inputs(analysis_py_sha256="0" * 64)))
run("6b_scan_bytes_not_hs", honest(), sb=SB + b" ")
run("6c_hs_other_consistent_record", honest(), hs="1" * 64)
run("8a_versions_missing", honest(I=inputs(git_version=None)))
run("8b_versions_empty", honest(I=inputs(python_version="")))
run("8c_format_v1", honest(I=inputs(format="layered-scan-verify-inputs/1")))
run("extra_file_in_record", dict(honest(), **{"EXTRA.txt": "x"}))
print(json.dumps(res, indent=1))
open("/home/user/review_work/HONEST_TWIN", "w").write(HONEST)
