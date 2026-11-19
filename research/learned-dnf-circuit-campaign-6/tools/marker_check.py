"""Campaign 6: the check of a stage's manifest against the campaign marker (option A, the coordinators' ruling of
2026-11-19). A fixed script OUTSIDE stages6.frozen(), pushed alone and reviewed before any use. It is run before each
stage's launch; a refusal means no launch for that stage, and its output is committed with the stage's evidence.

  marker_check.py STAGE MANIFEST.json MARKER_COMMIT [REPO]      writes MARKER_CHECK_<STAGE>.txt next to the manifest

Since CAMPAIGN_MARKER_2.json (7eda858, frozen commit 6f29fe6), which supersedes CAMPAIGN_MARKER.json (b88144f): each
stage's kit protocol is its own stage file stages/STAGE_<S>.md, so each stage has its own claim ref (the first
rehearsal's shared claim key, README incident 2). It passes only if all of these hold:
1. the marker at MARKER_COMMIT (research/learned-dnf-circuit-campaign-6/CAMPAIGN_MARKER_2.json) has the pinned SHA-256
   (MARKER_SHA256, the marker approved by both coordinators), MARKER_COMMIT descends from the commit that introduced it
   (MARKER_INTRODUCED, 7eda858), that commit descends from PREDICTION.md's commit df1a3cb (checked), and REPO's tree
   holds the same marker (a missing one refuses);
2. the manifest's source_commit descends from MARKER_COMMIT;
3. the manifest's source_sha256 holds EXACTLY the marker's frozen paths, each with the marker's SHA-256, plus only the
   stage's declared data files: stages/STAGE_<S>.md and stages/RUNS_<S>.json (required); for M2, M3, RM2, RM3
   stages/INPUTS_<S>.json (required); for Q and the N stages, stages/PREDICTIONS.json and stages/Gate6_*.lean
   (allowed). A top-level STAGE_<S>.md (the superseded layout) refuses, and so does any other path or a missing one;
4. every hash of source_sha256 equals the file at the manifest's source_commit;
5. the kit's protocol fields: protocol_path is stages/STAGE_<S>.md, protocol_sha256 is its SHA-256 at protocol_commit,
   protocol_commit is the only commit in source_commit's history that adds it and descends from MARKER_INTRODUCED, and
   source_commit descends from protocol_commit and differs from it;
6. the stage file passes c6.stage_check (safeguard i: PREDICTION.md, and amendment 1 for M2, M3, RM2, RM3, by their
   SHA-256), and names the same stage; the manifest's campaign_id names it;
7. REPO's working tree is clean (`git status --porcelain` empty), and every frozen path, the stage file and the run list
   are identical in REPO's tree and at source_commit (`git diff --quiet SOURCE_COMMIT -- PATHS`), so that the c6 import
   and the stage check read the source commit's files; the report records REPO's HEAD.
It refuses under python -O (the asserts of c6.stage_check would vanish), and any exception of the stage check is a
refusal, so a refusal always leaves its MARKER_CHECK file. The report records this script's own SHA-256.
"""
import fnmatch
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
BASE = "research/learned-dnf-circuit-campaign-6"
STAGES = f"{BASE}/stages"
MARKER = f"{BASE}/CAMPAIGN_MARKER_2.json"
MARKER_SHA256 = "2084a1c14f6679d6b3dd79564c13044870e152a56713ecc2b549f8e9ab154c68"
MARKER_INTRODUCED = "7eda858a2ad0c999c37efd198161f4ab8df50e3a"
PROTOCOL_COMMIT = "df1a3cbcf73ed0ad71e04ded987f756a466e3902"            # PREDICTION.md
INPUT_STAGES = ("M2", "M3", "RM2", "RM3")
NETWORK_STAGES = ("Q", "N1", "N2", "N3", "N")


def git(repo, *args):
    return subprocess.run(["git", "-C", str(repo), *args], check=True, capture_output=True).stdout


def is_ancestor(repo, a, b):
    try:
        git(repo, "merge-base", "--is-ancestor", a, b)
        return True
    except subprocess.CalledProcessError:
        return False


def stage_file(stage):
    return f"{STAGES}/STAGE_{stage}.md"


def runs_file(stage):
    return f"{STAGES}/RUNS_{stage}.json"


def declared_data(stage, paths):
    """The stage's declared data files among `paths`: (required, allowed)."""
    required = {stage_file(stage), runs_file(stage)}
    allowed = set()
    if stage in INPUT_STAGES:
        required |= {f"{STAGES}/INPUTS_{stage}.json"}
    if stage in NETWORK_STAGES:
        allowed |= {p for p in paths if p == f"{STAGES}/PREDICTIONS.json" or fnmatch.fnmatch(p, f"{STAGES}/Gate6_*.lean")}
    return required, allowed | required


def check(stage, manifest_path, marker_commit, repo):
    """Returns (passed, lines)."""
    repo = Path(repo)
    lines, ok = [], True

    def fail(msg):
        nonlocal ok
        ok = False
        lines.append("REFUSED: " + msg)

    m = json.loads(Path(manifest_path).read_text())
    src_commit = m["source_commit"]
    # 1. the marker
    if is_ancestor(repo, PROTOCOL_COMMIT, MARKER_INTRODUCED):
        lines.append(f"MARKER_INTRODUCED {MARKER_INTRODUCED} descends from PREDICTION.md's commit {PROTOCOL_COMMIT}")
    else:
        fail(f"MARKER_INTRODUCED {MARKER_INTRODUCED} does not descend from PREDICTION.md's commit {PROTOCOL_COMMIT}")
    if is_ancestor(repo, MARKER_INTRODUCED, marker_commit):
        lines.append(f"MARKER_COMMIT {marker_commit} descends from {MARKER_INTRODUCED}, which introduced the marker")
    else:
        fail(f"MARKER_COMMIT {marker_commit} does not descend from {MARKER_INTRODUCED}, which introduced the marker")
    try:
        mk_text = git(repo, "show", f"{marker_commit}:{MARKER}")
    except subprocess.CalledProcessError:
        fail(f"no marker {MARKER} at MARKER_COMMIT {marker_commit}")
        return ok, lines
    mk_sha = hashlib.sha256(mk_text).hexdigest()
    lines.append(f"marker {MARKER} at {marker_commit}: sha256 {mk_sha}")
    if mk_sha != MARKER_SHA256:
        fail(f"the marker at MARKER_COMMIT has sha256 {mk_sha}, not the pinned {MARKER_SHA256}")
        return ok, lines
    marker = json.loads(mk_text)
    if not (repo / MARKER).is_file():
        fail(f"the marker {MARKER} is missing from REPO's tree")
    elif (repo / MARKER).read_bytes() != mk_text:
        fail("the marker in REPO's tree differs from the marker at MARKER_COMMIT")
    # 2. the source commit after the marker
    if is_ancestor(repo, marker_commit, src_commit):
        lines.append(f"source_commit {src_commit} descends from the marker's commit")
    else:
        fail(f"source_commit {src_commit} does not descend from the marker's commit {marker_commit}")
    src = m["source_sha256"]
    frozen = marker["files"]
    # 7. REPO's tree is the source commit's
    tree_ok = True
    head = git(repo, "rev-parse", "HEAD").decode().strip()
    lines.append(f"REPO {repo} at HEAD {head}")
    status = git(repo, "status", "--porcelain").decode()
    if status.strip():
        tree_ok = False
        fail("REPO's working tree is not clean (git status --porcelain): " + " | ".join(status.splitlines()[:10]))
    tree_paths = sorted(set(frozen) | {stage_file(stage), runs_file(stage)})
    try:
        git(repo, "diff", "--quiet", src_commit, "--", *tree_paths)
        lines.append(f"REPO's tree equals source_commit on the {len(frozen)} frozen paths, the stage file and the run list")
    except subprocess.CalledProcessError:
        tree_ok = False
        fail(f"REPO's tree differs from source_commit {src_commit} on the frozen paths, the stage file or the run list")
    # 3. exactly the frozen paths and the declared data
    required, allowed = declared_data(stage, src)
    for p, h in sorted(frozen.items()):
        if p not in src:
            fail(f"frozen path missing from source_sha256: {p}")
        elif src[p] != h:
            fail(f"frozen path with another hash than the marker's: {p}")
    for p in sorted(required - set(src)):
        fail(f"declared data file missing from source_sha256: {p}")
    if f"{BASE}/STAGE_{stage}.md" in src:
        fail(f"a top-level {BASE}/STAGE_{stage}.md (the superseded layout) is presented instead of {stage_file(stage)}")
    for p in sorted(set(src) - set(frozen) - allowed):
        fail(f"path not allowed in source_sha256 (neither frozen nor a declared data file of {stage}): {p}")
    # 4. every hash at the source commit
    for p, h in sorted(src.items()):
        try:
            got = hashlib.sha256(git(repo, "show", f"{src_commit}:{p}")).hexdigest()
        except subprocess.CalledProcessError:
            fail(f"absent at source_commit: {p}")
            continue
        if got != h:
            fail(f"hash differs at source_commit: {p}")
    # 5. the kit's protocol fields
    pc = m.get("protocol_commit", "")
    proto_ok = True
    if m.get("protocol_path") != stage_file(stage):
        proto_ok = False
        fail(f"protocol_path {m.get('protocol_path')} is not the stage file {stage_file(stage)}")
    elif not re.fullmatch("[0-9a-f]{40}", pc):
        proto_ok = False
        fail(f"protocol_commit {pc!r} is not an exact commit")
    else:
        try:
            got = hashlib.sha256(git(repo, "show", f"{pc}:{stage_file(stage)}")).hexdigest()
            if got != m.get("protocol_sha256"):
                proto_ok = False
                fail(f"protocol_sha256 {m.get('protocol_sha256')} is not the stage file's SHA-256 {got} at protocol_commit")
        except subprocess.CalledProcessError:
            proto_ok = False
            fail(f"the stage file is absent at protocol_commit {pc}")
        adders = git(repo, "log", "--diff-filter=A", "--format=%H", src_commit, "--", stage_file(stage)).decode().split()
        if adders != [pc]:
            proto_ok = False
            fail(f"protocol_commit {pc} is not the only commit adding the stage file in source_commit's history: {adders}")
        if not is_ancestor(repo, MARKER_INTRODUCED, pc):
            proto_ok = False
            fail(f"protocol_commit {pc} does not descend from marker 2's commit {MARKER_INTRODUCED}")
        if pc == src_commit:
            proto_ok = False
            fail("source_commit must differ from protocol_commit (the stage file is pushed alone before it)")
        elif not is_ancestor(repo, pc, src_commit):
            proto_ok = False
            fail(f"source_commit {src_commit} does not descend from protocol_commit {pc}")
        if proto_ok:
            lines.append(f"protocol: {stage_file(stage)} at {pc}, sha256 {m.get('protocol_sha256')}; the only commit adding it; "
                         f"after marker 2; before source_commit")
    if not m.get("campaign_id", "").endswith("-" + stage.lower()):
        fail(f"the manifest's campaign_id {m.get('campaign_id')} does not name stage {stage}")
    # 6. safeguard i
    if not __debug__:
        fail("run under python -O: c6.stage_check's asserts are stripped, so the stage file is not checked")
    elif not tree_ok:
        fail("the stage check is not run: REPO's tree is not the source commit's")
    else:
        try:
            sys.path.insert(0, str(repo / BASE / "campaign6"))
            import c6
            st = c6.stage_check(repo / stage_file(stage))
            if st["stage"] != stage:
                fail(f"the stage file names stage {st['stage']}, not {stage}")
            else:
                lines.append(f"stage file passes c6.stage_check: {json.dumps(st, sort_keys=True)}")
        except Exception as e:
            fail(f"the stage file does not pass c6.stage_check: {type(e).__name__}: {e}")
    lines.append(f"source_sha256: {len(src)} paths ({len(frozen)} frozen, {len(set(src) - set(frozen))} data)")
    return ok, lines


def main(argv=None):
    a = sys.argv[1:] if argv is None else argv
    stage, manifest, marker_commit = a[0], Path(a[1]), a[2]
    repo = Path(a[3]) if len(a) > 3 else HERE.parent.parent.parent
    ok, lines = check(stage, manifest, marker_commit, repo)
    own = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    text = "\n".join([f"marker_check.py sha256 {own}", f"stage {stage}", f"manifest {manifest.name} sha256 {hashlib.sha256(manifest.read_bytes()).hexdigest()}"]
                     + lines + [f"VERDICT: {'PASSED' if ok else 'REFUSED'}", ""])
    (manifest.parent / f"MARKER_CHECK_{stage}.txt").write_text(text)
    print(text, end="")
    raise SystemExit(0 if ok else 1)


if __name__ == "__main__":
    main()
