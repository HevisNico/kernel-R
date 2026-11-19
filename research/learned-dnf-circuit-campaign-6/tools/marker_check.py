"""Campaign 6: the check of a stage's manifest against the campaign marker (option A, the coordinators' ruling of
2026-11-19). A fixed script OUTSIDE stages6.frozen(), pushed alone and reviewed before any use. It is run before each
stage's launch; a refusal means no launch for that stage, and its output is committed with the stage's evidence.

  marker_check.py STAGE MANIFEST.json MARKER_COMMIT [REPO]      writes MARKER_CHECK_<STAGE>.txt next to the manifest

It passes only if all of these hold:
1. the marker at MARKER_COMMIT (research/learned-dnf-circuit-campaign-6/CAMPAIGN_MARKER.json) is the one in the repository;
2. the manifest's source_commit descends from MARKER_COMMIT;
3. the manifest's source_sha256 holds EXACTLY the marker's frozen paths, each with the marker's SHA-256, plus only the
   stage's declared data files: its stage file (required); for M2, M3, RM2, RM3 its inputs file (required, one); for
   Q and the N stages, PREDICTED.json and the gate's Lean files (allowed). Any other path, or a missing one, refuses;
4. every hash of source_sha256 equals the file at the manifest's source_commit;
5. the stage file passes c6.stage_check (safeguard i), and names the same stage; the manifest's campaign_id names it.
The report records this script's own SHA-256.
"""
import fnmatch
import hashlib
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
BASE = "research/learned-dnf-circuit-campaign-6"
MARKER = f"{BASE}/CAMPAIGN_MARKER.json"
INPUT_STAGES = ("M2", "M3", "RM2", "RM3")
NETWORK_STAGES = ("Q", "N1", "N2", "N3", "N")


def git(repo, *args):
    return subprocess.run(["git", "-C", str(repo), *args], check=True, capture_output=True).stdout


def declared_data(stage, paths):
    """The stage's declared data files among `paths`: (required, allowed)."""
    required = {f"{BASE}/STAGE_{stage}.md"}
    allowed = set()
    if stage in INPUT_STAGES:
        inputs = [p for p in paths if fnmatch.fnmatch(p, f"{BASE}/INPUTS_{stage}.json")]
        required |= {f"{BASE}/INPUTS_{stage}.json"}
        allowed |= set(inputs)
    if stage in NETWORK_STAGES:
        allowed |= {p for p in paths if p == f"{BASE}/PREDICTED.json" or fnmatch.fnmatch(p, f"{BASE}/gate/Gate6_*.lean")}
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
    mk_text = git(repo, "show", f"{marker_commit}:{MARKER}")
    marker = json.loads(mk_text)
    lines.append(f"marker {MARKER} at {marker_commit}: sha256 {hashlib.sha256(mk_text).hexdigest()}")
    if (repo / MARKER).exists() and (repo / MARKER).read_bytes() != mk_text:
        fail("the marker in the repository differs from the marker at MARKER_COMMIT")
    try:
        git(repo, "merge-base", "--is-ancestor", marker_commit, src_commit)
        lines.append(f"source_commit {src_commit} descends from the marker's commit")
    except subprocess.CalledProcessError:
        fail(f"source_commit {src_commit} does not descend from the marker's commit {marker_commit}")
    src = m["source_sha256"]
    frozen = marker["files"]
    required, allowed = declared_data(stage, src)
    for p, h in sorted(frozen.items()):
        if p not in src:
            fail(f"frozen path missing from source_sha256: {p}")
        elif src[p] != h:
            fail(f"frozen path with another hash than the marker's: {p}")
    for p in sorted(required - set(src)):
        fail(f"declared data file missing from source_sha256: {p}")
    for p in sorted(set(src) - set(frozen) - allowed):
        fail(f"path not allowed in source_sha256 (neither frozen nor a declared data file of {stage}): {p}")
    for p, h in sorted(src.items()):
        try:
            got = hashlib.sha256(git(repo, "show", f"{src_commit}:{p}")).hexdigest()
        except subprocess.CalledProcessError:
            fail(f"absent at source_commit: {p}")
            continue
        if got != h:
            fail(f"hash differs at source_commit: {p}")
    if not m.get("campaign_id", "").endswith("-" + stage.lower()):
        fail(f"the manifest's campaign_id {m.get('campaign_id')} does not name stage {stage}")
    sys.path.insert(0, str(repo / BASE / "campaign6"))
    import c6
    try:
        st = c6.stage_check(repo / f"{BASE}/STAGE_{stage}.md")
        if st["stage"] != stage:
            fail(f"the stage file names stage {st['stage']}, not {stage}")
        else:
            lines.append(f"stage file passes c6.stage_check: {json.dumps(st, sort_keys=True)}")
    except (AssertionError, FileNotFoundError, KeyError, ValueError) as e:
        fail(f"the stage file does not pass c6.stage_check: {e}")
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
