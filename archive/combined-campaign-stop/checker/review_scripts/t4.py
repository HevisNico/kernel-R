import json, sys, subprocess, tempfile, os, hashlib
L = "/home/user/review_clone/research/layered-networks"; sys.path.insert(0, L)
import analysis as A
res = {}
B = A.VERIFY_BRANCH
HS = "a" * 64; OTHER = "b" * 64
OKL = f"the scan is reproduced scan_sha256 {HS} VS {HS}\n"
def repo(commits, branch=B):
    d = tempfile.mkdtemp(); bare = f"{d}/r.git"; w = f"{d}/w"
    subprocess.run(["git", "init", "-q", "--bare", bare], check=True)
    subprocess.run(["git", "init", "-q", w], check=True)
    env = dict(os.environ, GIT_AUTHOR_NAME="t", GIT_AUTHOR_EMAIL="t@t", GIT_COMMITTER_NAME="t", GIT_COMMITTER_EMAIL="t@t")
    subprocess.run(["git", "-C", w, "checkout", "-q", "--orphan", branch], check=True)
    for files in commits:
        for n, t in files.items():
            open(f"{w}/{n}", "w").write(t)
        subprocess.run(["git", "-C", w, "add", "-A"], check=True)
        subprocess.run(["git", "-C", w, "commit", "-q", "-m", "x"], check=True, env=env)
    if commits:
        subprocess.run(["git", "-C", w, "push", "-q", bare, f"HEAD:refs/heads/{branch}"], check=True)
    return bare
def sv(name, bare, hs=HS):
    try: res[name] = ["ACCEPTED", A.scan_verify_record(bare, hs)[1][:8]]
    except A.Refused as e: res[name] = "refused: " + str(e)[:150]
    except Exception as e: res[name] = f"EXCEPTION {type(e).__name__}: {e}"[:150]
sv("honest", repo([{"VERIFY.txt": OKL}]))
sv("absent", repo([]))
sv("other_branch_name_only", repo([{"VERIFY.txt": OKL}], branch="evidence/other"))
sv("two_commits", repo([{"VERIFY.txt": OKL}, {"VERIFY.txt": OKL + "\n"}]))
sv("failed_verdict", repo([{"VERIFY.txt": f"PROBLEM: x\nTHE SCAN IS NOT REPRODUCED: no announce, push nothing scan_sha256 {HS} VS {OTHER}\n"}]))
sv("other_hash", repo([{"VERIFY.txt": f"the scan is reproduced scan_sha256 {OTHER} VS {OTHER}\n"}]))
sv("vs_differs", repo([{"VERIFY.txt": f"the scan is reproduced scan_sha256 {HS} VS {OTHER}\n"}]))
sv("no_verify_file", repo([{"OTHER.txt": "x"}]))
sv("garbage_last_line", repo([{"VERIFY.txt": OKL + "trailing words\n"}]))
sv("problem_lines_then_success", repo([{"VERIFY.txt": "PROBLEM: branch x missing\n" + OKL}]))
sv("success_text_prefix_variant", repo([{"VERIFY.txt": "xx the scan is reproduced scan_sha256 " + HS + " VS " + HS + "\n"}]))
sv("uppercase_hash", repo([{"VERIFY.txt": OKL.replace("a", "A")}]))
sv("unreachable_remote", "/nonexistent/repo.git")
# announce_time(what=) single-use and creation-before-announce
def at(name, items, commit="c" * 40):
    try: res[name] = ["ACCEPTED", A.announce_time(items, commit, B, what="the scan verify record")]
    except A.Refused as e: res[name] = "refused: " + str(e)[:150]
c = "c" * 40
bc = dict(activity_type="branch_creation", after=c, before="0" * 40, timestamp="2026-11-29T10:00:00Z")
at("act_ok", [bc])
at("act_force_push", [bc, dict(activity_type="force_push", after="d" * 40, timestamp="2026-11-29T10:05:00Z")])
at("act_deletion", [bc, dict(activity_type="branch_deletion", after="0" * 40, timestamp="2026-11-29T10:05:00Z")])
at("act_second_push", [bc, dict(activity_type="push", after="d" * 40, timestamp="2026-11-29T10:05:00Z")])
at("act_oldest_not_creation", [dict(activity_type="push", after=c, timestamp="2026-11-29T09:00:00Z"), bc])
at("act_creation_other_commit", [dict(bc, after="e" * 40)])
at("act_empty", [])
# N1, N2
RW = "/home/user/rescan_work"; sb = open(f"{RW}/EXCLUDED_SECOND_SCAN.json", "rb").read(); scan = json.loads(sb)
import copy, draw_seeds as D
s = copy.deepcopy(scan); s["refs"]["HEAD"]["tip"] = "0" * 40
try: A.check_scan(D.canon(s), "S"); res["N1_head_other_tip"] = "ACCEPTED"
except A.Refused as e: res["N1_head_other_tip"] = "refused: " + str(e)[:120]
def pa(name, txt):
    try: A.parse_announce(txt.encode()); res[name] = "ACCEPTED"
    except A.Refused as e: res[name] = "refused: " + str(e)[:120]
pa("N2_scan_sha_zz", f"format layered-draw-announce/2\nmode campaign\nexcluded_sha256 {HS}\nsecond_scan_sha256 zz\nsizes NOT1=60 ANDOR3=32 XOR3=37\n")
pa("N2_excl_upper", f"format layered-draw-announce/1\nmode rehearsal\nexcluded_sha256 {'A'*64}\nsizes NOT1=6 ANDOR3=6 XOR3=6\n")
pa("N2_ok_v2", f"format layered-draw-announce/2\nmode campaign\nexcluded_sha256 {HS}\nsecond_scan_sha256 {HS}\nsizes NOT1=60 ANDOR3=32 XOR3=37\n")
pa("N2_rehearsal1_published", open("/home/user/review_work/r1ann.txt").read() if os.path.exists("/home/user/review_work/r1ann.txt") else "")
print(json.dumps(res, indent=1))
