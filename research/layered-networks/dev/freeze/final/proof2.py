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
TWIN = f"{W}/github_twin.git"

PUSH = f"git push -q {GH} HEAD:refs/heads/"
TWINS = {   # (block, written line or fragment) -> replacement; each must occur exactly once in its block
    "announce": [(PUSH + "$B", f"git push -q {TWIN} HEAD:refs/heads/$B",
                  "no push to GitHub: the push goes to the local twin")],
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
    "rehearsal-draw": [(f"git fetch -q {GH} refs/heads/evidence/combined-rehearsal-draw-result",
                        f"git fetch -q {TWIN} refs/heads/evidence/combined-rehearsal-draw-result",
                        "the result branch exists only on the twin")],
    "check-list": [("A.check_draw(dict(draw='DRAW_REHEARSAL.json', excluded='$L/EXCLUDED.json'), 'rehearsal', tempfile.mkdtemp(), '$F')",
                    "A.check_draw(dict(draw='DRAW_REHEARSAL.json', excluded='$L/EXCLUDED.json', "
                    "announce='announce_rehearsal/DRAW_ANNOUNCE.txt'), 'rehearsal', tempfile.mkdtemp(), '$F', offline=True)",
                    "the GitHub read of the rehearsal's announce replaced by its offline mode on the twin's announce file"),
                   ("A.check_rehearsal_seeds(dict(rehearsal_draw='DRAW_REHEARSAL.json', excluded='EXCLUDED_SECOND.json'),",
                    "A.check_rehearsal_seeds(dict(rehearsal_draw='DRAW_REHEARSAL.json', excluded='EXCLUDED_SECOND.json', "
                    "rehearsal_announce='announce_rehearsal/DRAW_ANNOUNCE.txt'),",
                    "the same, for check_rehearsal_seeds (its announce file)"),
                   ("dict(announce=dict(push_utc=now)), tempfile.mkdtemp(), '$F', True)",
                    "dict(announce=dict(push_utc=now)), tempfile.mkdtemp(), '$F', False)",
                    "strict=False: check_rehearsal_seeds checks the rehearsal draw offline (its only use of the flag)")],
    "vars": [("L=<a clean clone of research/layered-campaign-freeze, with research/circuit/pdk linked to the SKY130 PDK at 1232782c as on the machines>/research/layered-networks",
              f"L={L}", "placeholder: the freeze branch does not exist yet; the clean clone of the candidate"),
             ("PY=<the pinned Python 3.13.18 (numpy 2.3.5, py_ecc 8.0.0), the one envcheck_layered4.py passed with on this machine>",
              f"PY={PY}", "placeholder: the pinned venv's Python")],
    "vars-campaign": [('H=<the 64 hex characters that ORDER 3 step (3) printed after "sha256">',
                       f"H=$(grep -o 'sha256 [0-9a-f]\\{{64\\}}' {LOG}/08_check-list.out | tail -1 | cut -c8-)",
                       "placeholder: H read from step (3)'s printed line (log/08_check-list.out)")],
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
STEPS = [("01", "vars", "."), ("02", "vars-rehearsal", "."), ("03", "announce", "."), ("04", "draw", "."),
         ("05", "second-scan", "."), ("06", "rehearsal-draw", "."), ("07", "list", "."), ("08", "check-list", "."),
         ("09", "vars-campaign", "."),
         ("10", "NEGATIVE: the freeze's old list as X, with H kept from (3)", "neg"),
         ("11", "announce", "."), ("12", "draw", ".")]
# the owner's negative case for the identity: a global git identity that is NOT the owner's, for the whole run
(W / "gitconfig_global_other").write_text("[user]\n\tname = someone else\n\temail = someone-else@invalid\n")
run = ["set -u", f"cd {W}/work", f"export GIT_CONFIG_GLOBAL={W}/gitconfig_global_other",
       'echo "global identity during the run: $(git config --global user.name)"']
for num, name, where in STEPS:
    if name.startswith("NEGATIVE"):
        body = ('mkdir neg && cd neg\nX_KEPT=$X\nX=$L/EXCLUDED.json\n' + ready["announce"] +
                'echo "rc of the block=$?"\nX=$X_KEPT\n'
                'git -C announce_campaign rev-parse -q --verify HEAD >/dev/null && echo "A COMMIT WAS MADE" || echo "no commit made"\n'
                f'git --git-dir {TWIN} rev-parse -q --verify refs/heads/$B >/dev/null && echo "$B ON THE TWIN" || echo "$B not pushed"\n'
                'cd ..\n')
        tag = "10_negative"
    else:
        body, tag = ready[name], f"{num}_{name}"
    (LOG / f"{tag}.block.sh").write_text(body)
    run += [f'echo "### {num} {name}"', f". {LOG}/{tag}.block.sh > {LOG}/{tag}.out 2>&1; echo \"rc=$?\" >> {LOG}/{tag}.out",
            f"tail -3 {LOG}/{tag}.out"]
    if not name.startswith("NEGATIVE"):     # FREEZE.txt: stop at the first block that fails
        run += [f'grep -qx "rc=0" {LOG}/{tag}.out || {{ echo "STOPPED: block {name} (step {num}) failed"; exit 1; }}']
run += [f'echo "### the twin\'s branches and their commit counts"',
        f"for r in $(git --git-dir {TWIN} for-each-ref --format='%(refname)'); do echo $r $(git --git-dir {TWIN} rev-list --count $r); done",
        f"git -C {W}/kernel-R status --porcelain --untracked-files=all | wc -l",
        'echo "### every commit on the twin: author and committer equal main\'s (the owner), compared, never printed"',
        f'O="$(git -C {W}/kernel-R log -1 --format=\'%an %ae\' origin/main)"',
        f"for r in $(git --git-dir {TWIN} for-each-ref --format='%(refname)'); do "
        f"a=\"$(git --git-dir {TWIN} log -1 --format='%an %ae' $r)\"; c=\"$(git --git-dir {TWIN} log -1 --format='%cn %ce' $r)\"; "
        f"[ \"$a\" = \"$O\" ] && [ \"$c\" = \"$O\" ] && echo \"$r: the owner's\" || echo \"$r: NOT THE OWNER'S\"; done",
        'echo "global identity is the owner\'s: $([ "$(git config --global user.name) $(git config --global user.email)" = "$O" ] && echo yes || echo no)"']
(LOG / "RUN.sh").write_text("\n".join(run) + "\n")
out = subprocess.run(["bash", str(LOG / "RUN.sh")], capture_output=True, text=True)
(LOG / "RUN.out").write_text(out.stdout + out.stderr)
print(out.stdout + out.stderr)
