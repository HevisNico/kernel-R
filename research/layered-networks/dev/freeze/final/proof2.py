"""The freeze proof, mechanical: every [block NAME] ... [end] of FREEZE.txt, extracted from the clone and run verbatim,
in the order ORDER gives, in one bash shell, in a fresh working folder.

  python3 proof2.py WORK COMMIT PYTHON

WORK must not exist. COMMIT is cloned from GitHub by branch name (research/layered-campaign-dev). Only two kinds of
change are made to a block, and each is listed line by line in WORK/log/TWINS.md and printed before the block runs:
  - a placeholder <...> filled in (the clone's path; H from step (3)'s printed line);
  - an offline twin for what this proof may not or cannot do on GitHub: no push to GitHub (each push goes to a local
    bare repository, github_twin.git, standing in for GitHub), the reads of the branches only that twin holds, drand
    (unreachable from here: the published quicknet round 1000000 stands in for the rounds), and the GitHub announce
    reads of analysis.py (announce_on_github, check_draw and check_rehearsal_seeds in strict mode), replaced by their
    offline modes on the twin's announce. git ls-remote on GitHub is run as written: it is a read GitHub answers.
Nothing is pushed to GitHub.
"""
import datetime
import json
from pathlib import Path
import re
import subprocess
import sys
import os
import textwrap

W, COMMIT, PY = Path(sys.argv[1]).resolve(), sys.argv[2], sys.argv[3]
if W.exists():
    sys.exit(f"{W} exists")
(W / "log").mkdir(parents=True)
(W / "work").mkdir()
LOG = W / "log"
GH = "https://github.com/HevisNico/kernel-R"


def sh(cmd, **k):
    return subprocess.run(cmd, shell=True, check=True, capture_output=True, text=True, **k).stdout


# 0. the clean clone of the candidate
SRC = os.environ.get("PROOF_CLONE_FROM", GH)   # a dry run before the push may clone a local repository
sh(f"git init -q {W}/kernel-R && cd {W}/kernel-R && git remote add origin {SRC} && "
   f"for b in research/layered-campaign-dev research/inverter-instances research/layered-networks main; do "
   f"git fetch -q origin refs/heads/$b:refs/remotes/origin/$b || exit 1; done && "
   f"git merge-base --is-ancestor {COMMIT} origin/research/layered-campaign-dev && "
   f"git checkout -q -B research/layered-campaign-dev {COMMIT}")
L = W / "kernel-R" / "research" / "layered-networks"
PDK = os.environ.get("PROOF_PDK", "/home/user/kernel-R/research/circuit/pdk")   # the SKY130 PDK at 1232782c, linked as on the machines
os.symlink(os.path.realpath(PDK), W / "kernel-R" / "research" / "circuit" / "pdk")
t = json.loads((L / "campaign_template.json").read_text())
sh(f"cd {W}/kernel-R && git worktree add -q --detach {W}/kit {t['kit_commit']} && "
   f"git worktree add -q --detach {W}/noise {t['noise_commit']}")
clone = dict(source=SRC, head=sh(f"git -C {W}/kernel-R rev-parse HEAD").strip(),
             status_lines=len(sh(f"git -C {W}/kernel-R status --porcelain --untracked-files=all").splitlines()),
             worktrees=sh(f"git -C {W}/kernel-R worktree list"))
(LOG / "00_clone.txt").write_text(json.dumps(clone, indent=1) + "\n")

# the blocks, extracted mechanically
text = (L / "FREEZE.txt").read_text().split("\n")
blocks, k = {}, 0
while k < len(text):
    m = re.fullmatch(r"\s*\[block ([a-z0-9-]+)\]\s*", text[k])
    if m:
        j = next(i for i in range(k + 1, len(text)) if text[i].strip() == "[end]")
        assert m.group(1) not in blocks, m.group(1)
        blocks[m.group(1)] = textwrap.dedent("\n".join(text[k + 1:j])) + "\n"
        k = j
    k += 1
(LOG / "blocks_extracted.json").write_text(json.dumps(blocks, indent=1) + "\n")

# the stand-in round (published quicknet round 1000000) and its announce time, 600 s before it
sys.path.insert(0, str(L))
import beacon_chain, beacon_verify  # noqa: E402
R1M = dict(round=1000000, randomness="b22aad4794f7451896f7a371aa46106fd84d919f3f569acd5b2fddf1d1440af3",
           signature="83ad29e4c409f9470fc2ef02f90214df49e02b441a1a241a82d622d9f608ef98fd8b11a029f1bee9d9e83b45088abe72")
assert beacon_verify.verify(beacon_chain.QUICKNET, R1M)["ok"]
(W / "STANDIN_ROUND_1000000.json").write_text(json.dumps(R1M))
T1M = datetime.datetime.fromtimestamp(beacon_verify.round_time(beacon_chain.QUICKNET, 1000000) - beacon_verify.DELAY_S,
                                      datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
sh(f"git init -q --bare {W}/github_twin.git")
sh(f"git init -q {W}/r1fetch && git -C {W}/r1fetch fetch -q {GH} refs/heads/evidence/combined-rehearsal-draw && "
   f"git -C {W}/r1fetch show FETCH_HEAD:DRAW_ANNOUNCE.txt > {W}/REHEARSAL1_DRAW_ANNOUNCE.txt")   # rehearsal 1, as published
sh(f"git init -q {W}/someclone && git -C {W}/someclone -c user.name=x -c user.email=x@invalid commit -q --allow-empty -m x")   # a git clone to start a block from (a negative case)
TWIN = f"{W}/github_twin.git"

PUSH = f"git push -q {GH} HEAD:refs/heads/"
TWINS = {   # (block, written line or fragment) -> replacement; each must occur exactly once in its block
    "announce": [(PUSH + "$B", f"git push -q {TWIN} HEAD:refs/heads/$B",
                  "no push to GitHub: the push goes to the local twin"),
                 (f"A.scan_verify_record('{GH}', '$HS')", f"A.scan_verify_record('{TWIN}', '$HS')",
                  "the published scan verify record is read from the twin, where step 08b pushed it")],
    "draw": [("c, text, t = A.announce_on_github('$B', tempfile.mkdtemp()); print(c, t)",
              f"import subprocess; c = subprocess.run(['git', '--git-dir', '{TWIN}', 'rev-parse', 'refs/heads/$B'], "
              f"capture_output=True, text=True, check=True).stdout.strip(); t = '{T1M}'; print(c, t)",
              "the announce commit read from the twin; its push time is the stand-in's (600 s before round 1000000)"),
             ("curl -sf https://api.drand.sh/$CH/public/$ROUND > ROUND_RAW.json || curl -sf https://api2.drand.sh/$CH/public/$ROUND > ROUND_RAW.json",
              f"cp {W}/STANDIN_ROUND_1000000.json ROUND_RAW.json",
              "drand is unreachable here: the published round 1000000 as drand serves it"),
             ("A.check_draw(dict(draw='DRAW.json', excluded='$X'), '$M', tempfile.mkdtemp(), '$F')",
              "A.check_draw(dict(draw='DRAW.json', excluded='$X', announce='../announce_$M/DRAW_ANNOUNCE.txt'), '$M', "
              "tempfile.mkdtemp(), '$F', offline=True)",
              "the GitHub read of the announce replaced by its offline mode on the twin's announce file"),
             (PUSH + "$R", f"git push -q {TWIN} HEAD:refs/heads/$R", "no push to GitHub: the push goes to the local twin")],
    "rehearsal-draw": [(f"git fetch -q {GH} refs/heads/evidence/combined-rehearsal2-draw-result",
                        f"git fetch -q {TWIN} refs/heads/evidence/combined-rehearsal2-draw-result",
                        "rehearsal 2's result branch exists only on the twin (rehearsal 1's two fetches stay on GitHub)")],
    "check-list": [("A.check_draw(dict(draw='DRAW_REHEARSAL.json', excluded='EXCLUDED_REHEARSAL2.json'), 'rehearsal', tempfile.mkdtemp(), '$F')",
                    "A.check_draw(dict(draw='DRAW_REHEARSAL.json', excluded='EXCLUDED_REHEARSAL2.json', "
                    "announce='announce_rehearsal/DRAW_ANNOUNCE.txt'), 'rehearsal', tempfile.mkdtemp(), '$F', offline=True)",
                    "the GitHub read of the rehearsal's announce replaced by its offline mode on the twin's announce file"),
                   ("A.check_rehearsal_seeds(dict(rehearsal_draw='DRAW_REHEARSAL.json', rehearsal_excluded='EXCLUDED_REHEARSAL2.json',",
                    "A.check_rehearsal_seeds(dict(rehearsal_draw='DRAW_REHEARSAL.json', rehearsal_excluded='EXCLUDED_REHEARSAL2.json', "
                    f"rehearsal_announce='announce_rehearsal/DRAW_ANNOUNCE.txt', rehearsal1_announce='{W}/REHEARSAL1_DRAW_ANNOUNCE.txt',",
                    "the announce files for check_rehearsal_seeds offline: rehearsal 2's from the twin, rehearsal 1's as "
                    "published (its announce commit 9c3ec1e1 on GitHub, fetched by proof2)"),
                   ("dict(announce=dict(push_utc=now)), tempfile.mkdtemp(), '$F', True, 'campaign',",
                    "dict(announce=dict(push_utc=now)), tempfile.mkdtemp(), '$F', False, 'campaign',",
                    "strict=False: check_rehearsal_seeds checks both rehearsal draws offline (rehearsal 2 is on the twin "
                    "only); rehearsal 1 is also checked from GitHub, verbatim, by the block's own check_draw with past=")],
    "vars": [("L=<a clean clone of research/layered-campaign-freeze, with research/circuit/pdk linked to the SKY130 PDK at 1232782c as on the machines>/research/layered-networks",
              f"L={L}", "placeholder: the freeze branch does not exist yet; the clean clone of the candidate"),
             ("PY=<the pinned Python 3.13.18 (numpy 2.3.5, py_ecc 8.0.0), the one envcheck_layered4.py passed with on this machine>",
              f"PY={PY}", "placeholder: the pinned venv's Python")],
    "vars-rehearsal": [('H=<the 64 hex characters that ORDER 2 step (r3) printed after "sha256">',
                        f"H=$(grep -o 'sha256 [0-9a-f]\\{{64\\}}' {LOG}/01c_check-rehearsal2-list.out | tail -1 | cut -c8-)",
                        "placeholder: H read from step (r3)'s printed line (log/01c_check-rehearsal2-list.out)")],
    "vars-campaign": [('H=<the 64 hex characters that ORDER 3 step (3) printed after "sha256">',
                       f"H=$(grep -o ' sha256 [0-9a-f]\\{{64\\}}' {LOG}/08_check-list.out | tail -1 | cut -c9-)",
                       "placeholder: H read from step (3)'s printed line (log/08_check-list.out)"),
                      ('HS=<the 64 hex characters that ORDER 3 step (3) printed after "scan_sha256">',
                       f"HS=$(grep -o 'scan_sha256 [0-9a-f]\\{{64\\}}' {LOG}/08_check-list.out | tail -1 | cut -c13-)",
                       "placeholder: HS read from step (3)'s printed line (log/08_check-list.out)"),
                      ('VS=<the 64 hex characters that ORDER 3 step (3b), [block verify-scan] on the SECOND machine, printed after "VS">',
                       f"VS=$(grep -o ' VS [0-9a-f]\\{{64\\}}' {LOG}/08b_verify-scan.out | tail -1 | cut -c5-)",
                       "placeholder: VS read from step (3b)'s printed line (log/08b_verify-scan.out); the second machine "
                       "is the folder verify/ of this proof, with its own [block second-scan]")],
    "verify-scan": [(PUSH + "$V", f"git push -q {TWIN} HEAD:refs/heads/$V",
                     "no push to GitHub: the verify record goes to the local twin")],
    # [block check-rehearsal2-list]'s analysis.check_rehearsal_seeds call (rehearsal mode, strict) needs no twin: it
    # checks rehearsal 1 only, on GitHub, as the block's own check_draw with past= does (proof2 runs that verbatim).
    # [block check-list]'s call keeps its three twins (listed above); its new second_scan= argument is the scan's file.
}
twins_md = ["# Changes made to the blocks of FREEZE.txt (placeholders and offline twins), line by line", ""]
ready = {}
for name, b in blocks.items():
    for old, new, why in TWINS.get(name, []):
        assert b.count(old) == 1, (name, old)
        b = b.replace(old, new)
        twins_md += [f"- block **{name}** ({why}):", f"  - written: `{old}`", f"  - run:     `{new}`"]
    ready[name] = b
(LOG / "TWINS.md").write_text("\n".join(twins_md) + "\n")

# the order (ORDER 2, 3, 4) and the owner's negative case
GHPAT = "refs/heads/evidence/combined-*"     # the remote refs a block could create; compared before and after


def run_steps(steps, work, log, head=()):
    """Run the steps in one bash shell, in order. steps: dicts num, name, kind ("pass" or "neg"), body, made (neg:
    the folder whose repository must hold no commit), where (neg: the folder to run from). Returns (rc, summary).
    A "pass" step must give rc 0; the run stops at the first that does not. A "neg" step must refuse: its block
    exits non-zero, makes no commit, and changes neither the twin's refs nor GitHub's evidence/combined-* refs."""
    log.mkdir(parents=True, exist_ok=True)
    snap = (f"git --git-dir {TWIN} for-each-ref --format='%(refname) %(objectname)' > {log}/.twin_$1; "
            f"git ls-remote {GH} '{GHPAT}' > {log}/.gh_$1")
    run = ["set -u", f"cd {work}", f"snap() {{ {snap}; }}", *head]
    for s in steps:
        tag = f"{s['num']}_{s['name']}"
        if s["kind"] == "neg":
            body = (f"snap before\nmkdir -p {s['where']}\ncd {s['where']}\n{s.get('setup', '')}{s['body']}"
                    'echo "rc of the block=$?"\n'
                    f"git -C {s['made']} rev-parse -q --verify HEAD >/dev/null 2>&1 && echo 'NEGCHECK commit=yes' || echo 'NEGCHECK commit=no'\n"
                    f"cd {work}\nsnap after\n"
                    f"cmp -s {log}/.twin_before {log}/.twin_after && echo 'NEGCHECK twin=same' || echo 'NEGCHECK twin=changed'\n"
                    f"cmp -s {log}/.gh_before {log}/.gh_after && echo 'NEGCHECK github=same' || echo 'NEGCHECK github=changed'\n")
        else:
            body = s["body"]
        (log / f"{tag}.block.sh").write_text(body)
        run += [f'echo "### {s["num"]} {s["name"]} ({s["kind"]})"',
                f". {log}/{tag}.block.sh > {log}/{tag}.out 2>&1; echo \"rc=$?\" >> {log}/{tag}.out", f"tail -4 {log}/{tag}.out"]
        if s["kind"] == "pass":
            run += [f'grep -qx "rc=0" {log}/{tag}.out || {{ echo "STOPPED: step {s["num"]} {s["name"]} failed"; exit 1; }}']
    (log / "RUN.sh").write_text("\n".join(run) + "\n")
    out = subprocess.run(["bash", str(log / "RUN.sh")], capture_output=True, text=True)
    (log / "RUN.out").write_text(out.stdout + out.stderr)
    res = []
    for s in steps:
        f = log / f"{s['num']}_{s['name']}.out"
        o = f.read_text() if f.exists() else None
        if o is None:
            res.append(dict(step=s["num"], name=s["name"], kind=s["kind"], result="FAILED", why="not run (the run stopped before it)"))
            continue
        rcs = re.findall(r"^rc=(\d+)$", o, re.M)
        if s["kind"] == "pass":
            ok = bool(rcs) and rcs[-1] == "0"
            res.append(dict(step=s["num"], name=s["name"], kind="pass", result="PASSED" if ok else "FAILED",
                            why=None if ok else f"rc {rcs[-1] if rcs else 'none'}"))
        else:
            brc = re.findall(r"^rc of the block=(\d+)$", o, re.M)
            checks = dict(re.findall(r"^NEGCHECK (\w+)=(\w+)$", o, re.M))
            bad = ([f"the block exited {brc[-1] if brc else 'none'}"] if not brc or brc[-1] == "0" else []) + \
                  (["a commit was made"] if checks.get("commit") != "no" else []) + \
                  (["the twin changed"] if checks.get("twin") != "same" else []) + \
                  (["GitHub's refs changed"] if checks.get("github") != "same" else [])
            res.append(dict(step=s["num"], name=s["name"], kind="neg", result="FAILED" if bad else "REFUSED AS EXPECTED",
                            why="; ".join(bad) or f"block rc {brc[-1]}, no commit, twin and GitHub unchanged"))
    fails = [r for r in res if r["result"] == "FAILED"]
    rc = 1 if fails or out.returncode != 0 else 0
    return rc, dict(passed=sum(r["result"] == "PASSED" for r in res),
                    refused_as_expected=sum(r["result"] == "REFUSED AS EXPECTED" for r in res),
                    failed=len(fails), runner_exit=out.returncode, exit_code=rc, steps=res)


def ident_body(twin, owner_repo, n_refs):
    """every ref of the twin: one commit, author and committer equal main's (the owner), compared, never printed;
    exactly n_refs refs. Fails (rc 1) otherwise."""
    return ('O="$(git -C ' + str(owner_repo) + " log -1 --format='%an %ae' origin/main)\"\n"
            'echo "the global identity is the owner\'s: $([ "$(git config --global user.name) $(git config --global user.email)" = "$O" ] && echo yes || echo no)"\n'
            f"N=0\nfor r in $(git --git-dir {twin} for-each-ref --format='%(refname)'); do\n"
            f"  a=\"$(git --git-dir {twin} log -1 --format='%an %ae' $r)\"; c=\"$(git --git-dir {twin} log -1 --format='%cn %ce' $r)\"; n=$(git --git-dir {twin} rev-list --count $r)\n"
            "  if [ \"$a\" = \"$O\" ] && [ \"$c\" = \"$O\" ] && [ \"$n\" = 1 ]; then echo \"$r: one commit, the owner's\"; else echo \"$r: NOT one commit of the owner's\"; N=1; fi\n"
            f"done\n[ $(git --git-dir {twin} for-each-ref | wc -l) = {n_refs} ] || {{ echo 'the twin does not hold exactly {n_refs} refs'; N=1; }}\n( exit $N )\n")


def clean_body(repo):
    """the clone clean: git status --porcelain lists nothing but the PDK link the proof made. Fails (rc 1) otherwise."""
    return (f"x=$(git -C {repo} status --porcelain --untracked-files=all | grep -vx '?? research/circuit/pdk' || true)\n"
            'if [ -z "$x" ]; then echo "the clone is clean (only the PDK link)"; else echo "THE CLONE IS NOT CLEAN:"; echo "$x"; fi\n'
            '( exit $([ -z "$x" ] && echo 0 || echo 1) )\n')


# the runner's self-test: five dummy runs that must fail the proof, one that must pass it. Each runs in its own
# folder; the identity case uses its own bare twin (selftest/twin.git); nothing is pushed anywhere else.
st = W / "selftest"
(st / "work").mkdir(parents=True)
CASES = [
    ("a required block that exits 1", 1, [dict(num="1", name="ok", kind="pass", body="true\n"),
                                           dict(num="2", name="fails", kind="pass", body="( exit 1 )\n")]),
    ("a negative block that succeeds", 1, [dict(num="1", name="neg-succeeds", kind="neg", body="( exit 0 )\n",
                                                made="nothing", where=f"{st}/work/n1")]),
    ("a negative block that commits (then exits 1)", 1,
     [dict(num="1", name="neg-commits", kind="neg", made="r", where=f"{st}/work/n2",
           body="( set -e\n  mkdir r\n  cd r\n  git init -q\n  git -c user.name=x -c user.email=x@invalid commit -q --allow-empty -m x\n  exit 1 )\n")]),
    ("a twin ref committed under another identity", 1, None),
    ("a dirty clone", 1, None),
    ("a passing block and a refusing negative block", 0, [dict(num="1", name="ok", kind="pass", body="true\n"),
                                                          dict(num="2", name="neg-refuses", kind="neg", body="( exit 1 )\n",
                                                               made="nothing", where=f"{st}/work/n3")]),
]
stwin = st / "twin.git"
sh(f"git init -q --bare {stwin} && git init -q {st}/other && git -C {st}/other -c user.name='someone else' "
   f"-c user.email=someone-else@invalid commit -q --allow-empty -m x && git -C {st}/other push -q {stwin} HEAD:refs/heads/evidence/x")
sh(f"git init -q {st}/dirty && git -C {st}/dirty -c user.name=x -c user.email=x@invalid commit -q --allow-empty -m x && touch {st}/dirty/stray.json")
CASES[3] = (CASES[3][0], 1, [dict(num="1", name="identity", kind="pass", body=ident_body(stwin, W / "kernel-R", 1))])
CASES[4] = (CASES[4][0], 1, [dict(num="1", name="clean", kind="pass", body=clean_body(st / "dirty"))])
selftest = []
for k, (what, want, steps) in enumerate(CASES, start=1):
    rc, summ = run_steps(steps, st / "work", st / f"case{k}")
    selftest.append(dict(case=what, want_exit_nonzero=bool(want), exit_code=rc, ok=(rc != 0) == bool(want), summary=summ))
(LOG / "SELFTEST.json").write_text(json.dumps(selftest, indent=1) + "\n")
print("runner self-test:", [(x["case"], x["exit_code"], "ok" if x["ok"] else "WRONG") for x in selftest])
if not all(x["ok"] for x in selftest):
    print("THE RUNNER'S SELF-TEST FAILED: no proof run")
    sys.exit(2)

# the real run: the order of ORDER 2, 3, 4, with the negative cases
(W / "gitconfig_global_other").write_text("[user]\n\tname = someone else\n\temail = someone-else@invalid\n")
B = lambda n: ready[n]
STEPS = [dict(num="01", name="vars", kind="pass", body=B("vars")),
         dict(num="01a", name="rehearsal1-files", kind="pass", body=B("rehearsal1-files")),
         dict(num="01b", name="rehearsal2-list", kind="pass", body=B("rehearsal2-list")),
         dict(num="01c", name="check-rehearsal2-list", kind="pass", body=B("check-rehearsal2-list")),
         dict(num="02", name="vars-rehearsal", kind="pass", body=B("vars-rehearsal")),
         dict(num="03", name="announce", kind="pass", body=B("announce")),
         dict(num="04", name="draw", kind="pass", body=B("draw")),
         dict(num="04a", name="NEG-announce-exists", kind="neg", setup=f"cp {W}/work/EXCLUDED_REHEARSAL2.json .\nmkdir announce_$M\n", body=B("announce"),
              made="announce_$M", where=f"{W}/work/neg_announce"),
         dict(num="04b", name="NEG-draw-exists", kind="neg", setup=f"cp {W}/work/EXCLUDED_REHEARSAL2.json .\nmkdir draw_$M\n", body=B("draw"),
              made="draw_$M", where=f"{W}/work/neg_draw"),
         dict(num="04c", name="NEG-inside-clone", kind="neg", setup=f"cp {W}/work/EXCLUDED_REHEARSAL2.json .\n", body=B("announce"), made="announce_$M",
              where=f"{W}/someclone/sub"),
         dict(num="04d", name="NEG-scan-missing-branch", kind="neg", made="scanrepo", where=f"{W}/work/neg_scan",
              body=B("second-scan").replace(
                  "git ls-remote --heads origin > ../SCAN_LSREMOTE.txt",
                  "{ printf '0000000000000000000000000000000000000000\\trefs/heads/no-such-branch-for-the-proof\\n'; "
                  "git ls-remote --heads origin; } > ../SCAN_LSREMOTE.txt", 1)),
         dict(num="05", name="second-scan", kind="pass", body=B("second-scan")),
         dict(num="06", name="rehearsal-draw", kind="pass", body=B("rehearsal-draw")),
         dict(num="07", name="list", kind="pass", body=B("list")),
         dict(num="08", name="check-list", kind="pass", body=B("check-list")),
         # ORDER 3 (3b): the second machine, as a separate folder with its own [block second-scan] (a second full scan)
         dict(num="08a", name="verify-second-scan", kind="pass",
              body=f"( mkdir {W}/verify && cd {W}/verify && cp {W}/work/EXCLUDED_SECOND_SCAN.json SCAN_TO_VERIFY.json\n"
                   + B("second-scan") + ")\n"),
         dict(num="08b", name="verify-scan", kind="pass", body=f"( cd {W}/verify\n" + B("verify-scan") + ")\n"),
         dict(num="09", name="vars-campaign", kind="pass", body=B("vars-campaign")),
         dict(num="09a", name="NEG-vs-not-hs", kind="neg",
              setup=f"cp {W}/work/EXCLUDED_SECOND.json {W}/work/EXCLUDED_SECOND_SCAN.json .\nVS_KEPT=$VS\nVS={'0' * 64}\n",
              body=B("announce") + "RC=$?\nVS=$VS_KEPT\n( exit $RC )\n", made="announce_$M", where=f"{W}/work/neg_vs"),
         dict(num="10", name="NEG-old-list", kind="neg", setup="X_KEPT=$X\nX=$L/EXCLUDED.json\n",
              body=B("announce") + "RC=$?\nX=$X_KEPT\n( exit $RC )\n", made="announce_$M", where=f"{W}/work/neg_oldlist"),
         dict(num="11", name="announce", kind="pass", body=B("announce")),
         dict(num="12", name="draw", kind="pass", body=B("draw")),
         dict(num="13", name="owner-identity", kind="pass", body=ident_body(TWIN, W / "kernel-R", 5)),   # rehearsal 2 and campaign: announce + result each; the verify record
         dict(num="14", name="clone-clean", kind="pass", body=clean_body(W / "kernel-R"))]
rc, summary = run_steps(STEPS, W / "work", LOG, head=[f"export GIT_CONFIG_GLOBAL={W}/gitconfig_global_other",
                                                    'echo "global identity during the run: $(git config --global user.name)"'])
summary.update(commit=COMMIT, clone=clone, selftest_ok=True)
(LOG / "SUMMARY.json").write_text(json.dumps(summary, indent=1) + "\n")
print(f"passed {summary['passed']}, refused as expected {summary['refused_as_expected']}, failed {summary['failed']}; exit code {rc}")
for r in summary["steps"]:
    print(f"  {r['step']:>3} {r['name']:<22} {r['result']}" + (f"  ({r['why']})" if r["result"] == "FAILED" else ""))
sys.exit(rc)
