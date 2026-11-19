"""Campaign 6: the check of a stage's manifest against the campaign marker (option A, the coordinators' ruling of
2026-11-19). A fixed script OUTSIDE stages6.frozen(), pushed alone and reviewed before any use. It is run before each
stage's launch; a refusal means no launch for that stage, and its output is committed with the stage's evidence.

  marker_check.py STAGE ATTEMPT MANIFEST.json MARKER_COMMIT [REPO]      writes MARKER_CHECK_<STAGE>.txt next to the manifest

CANDIDATE for the commit after CAMPAIGN_MARKER_3.json (the audit of 2026-11-19): the attempt's layout stages/<ATTEMPT>/;
the manifest and the report outside REPO (F1); REPO's head within the kit's allowed changes after the source commit
(F2); the prediction record (PREDICTED.json for Q and the N stages, PREDICTED_RN.json for RN) bound, byte-identical to
its own earlier commit that adds only it and its gate files, with a gate file exactly for each measured instance
that has an observation (the frozen predict6.gate_each writes no other), unchanged at the source commit (findings 10,
11; the coordinator's review M1 and N5).

Each stage's kit protocol is its own stage file stages/<ATTEMPT>/STAGE_<S>.md, so each stage and attempt has its own
claim ref (README incidents 2 and 10). It passes only if all of these hold:
1. the marker at MARKER_COMMIT (MARKER, the campaign marker this script is pinned to) has the pinned SHA-256
   (MARKER_SHA256, the marker approved by both coordinators), MARKER_COMMIT descends from the commit that introduced it
   (MARKER_INTRODUCED), that commit descends from PREDICTION.md's commit df1a3cb (checked), and REPO's tree holds the
   same marker (a missing one refuses);
2. the manifest's source_commit descends from MARKER_COMMIT;
3. the manifest's source_sha256 holds EXACTLY the marker's frozen paths, each with the marker's SHA-256, plus only the
   stage's declared data files, all under stages/<ATTEMPT>/: STAGE_<S>.md and RUNS_<S>.json; INPUTS_<S>.json for M2, M3,
   RM2, RM3; the prediction record PREDICTED.json for Q and the N stages, PREDICTED_RN.json for RN. A stage file outside
   an attempt's folder (the superseded layouts) refuses, and so does any other path or a missing one;
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
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
BASE = "research/learned-dnf-circuit-campaign-6"
STAGES = f"{BASE}/stages"
MARKER = f"{BASE}/CAMPAIGN_MARKER_3.json"
MARKER_SHA256 = "5a92a6498e7c605c2a537a97c7be454434f0d4eff7990f4d2a10d338643ee65b"
MARKER_INTRODUCED = "2e00835dec24edd8cb9abc41dbdc0a993463854d"
ATTEMPT_RE = r"[a-z0-9][a-z0-9-]{0,31}"
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


def adir(attempt):
    assert re.fullmatch(ATTEMPT_RE, attempt), f"{attempt!r} is not a valid attempt id"
    return f"{STAGES}/{attempt}"


def stage_file(stage, attempt):
    return f"{adir(attempt)}/STAGE_{stage}.md"


def runs_file(stage, attempt):
    return f"{adir(attempt)}/RUNS_{stage}.json"


def record_file(stage, attempt):
    """The prediction record a stage's runs come from: PREDICTED_RN.json for RN, PREDICTED.json for Q and N."""
    if stage == "RN":
        return f"{adir(attempt)}/PREDICTED_RN.json"
    if stage in NETWORK_STAGES:
        return f"{adir(attempt)}/PREDICTED.json"
    return None


def declared_data(stage, attempt, paths):
    """The stage's declared data files: (required, allowed). Exactly what stages6.manifest binds."""
    required = {stage_file(stage, attempt), runs_file(stage, attempt)}
    if stage in INPUT_STAGES:
        required |= {f"{adir(attempt)}/INPUTS_{stage}.json"}
    if record_file(stage, attempt):
        required |= {record_file(stage, attempt)}
    return required, required


def check(stage, attempt, manifest_path, marker_commit, repo):
    """Returns (passed, lines)."""
    repo = Path(repo)
    lines, ok = [], True

    def fail(msg):
        nonlocal ok
        ok = False
        lines.append("REFUSED: " + msg)

    if not re.fullmatch(ATTEMPT_RE, attempt):
        fail(f"{attempt!r} is not a valid attempt id")
        return ok, lines
    if Path(manifest_path).resolve().is_relative_to(repo.resolve()):          # F1
        fail(f"the manifest {manifest_path} is inside REPO; it and this report must stay outside the checkout")
        return ok, lines
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
    after = set(git(repo, "diff", "--name-only", src_commit, head).decode().split())                     # F2
    kit_allowed = {f"{adir(attempt)}/CAMPAIGN_{stage}.json", m.get("marker_path"), m.get("inventory_a_path"), m.get("inventory_b_path")}
    if after - kit_allowed:
        fail(f"REPO's head changes more than the kit allows after the source commit (its launch would refuse): {sorted(after - kit_allowed)}")
    status = git(repo, "status", "--porcelain").decode()
    if status.strip():
        tree_ok = False
        fail("REPO's working tree is not clean (git status --porcelain): " + " | ".join(status.splitlines()[:10]))
    tree_paths = sorted(set(frozen) | {stage_file(stage, attempt), runs_file(stage, attempt)})
    try:
        git(repo, "diff", "--quiet", src_commit, "--", *tree_paths)
        lines.append(f"REPO's tree equals source_commit on the {len(frozen)} frozen paths, the stage file and the run list")
    except subprocess.CalledProcessError:
        tree_ok = False
        fail(f"REPO's tree differs from source_commit {src_commit} on the frozen paths, the stage file or the run list")
    # 3. exactly the frozen paths and the declared data
    required, allowed = declared_data(stage, attempt, src)
    for p, h in sorted(frozen.items()):
        if p not in src:
            fail(f"frozen path missing from source_sha256: {p}")
        elif src[p] != h:
            fail(f"frozen path with another hash than the marker's: {p}")
    for p in sorted(required - set(src)):
        fail(f"declared data file missing from source_sha256: {p}")
    for p in sorted(src):
        if re.fullmatch(rf"{re.escape(BASE)}/(stages/)?STAGE_{stage}\.md", p):
            fail(f"a stage file outside an attempt's folder (the superseded layout): {p}")
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
    if m.get("protocol_path") != stage_file(stage, attempt):
        proto_ok = False
        fail(f"protocol_path {m.get('protocol_path')} is not the stage file {stage_file(stage, attempt)}")
    elif not re.fullmatch("[0-9a-f]{40}", pc):
        proto_ok = False
        fail(f"protocol_commit {pc!r} is not an exact commit")
    else:
        try:
            got = hashlib.sha256(git(repo, "show", f"{pc}:{stage_file(stage, attempt)}")).hexdigest()
            if got != m.get("protocol_sha256"):
                proto_ok = False
                fail(f"protocol_sha256 {m.get('protocol_sha256')} is not the stage file's SHA-256 {got} at protocol_commit")
        except subprocess.CalledProcessError:
            proto_ok = False
            fail(f"the stage file is absent at protocol_commit {pc}")
        adders = git(repo, "log", "--diff-filter=A", "--format=%H", src_commit, "--", stage_file(stage, attempt)).decode().split()
        if adders != [pc]:
            proto_ok = False
            fail(f"protocol_commit {pc} is not the only commit adding the stage file in source_commit's history: {adders}")
        if not is_ancestor(repo, MARKER_INTRODUCED, pc):
            proto_ok = False
            fail(f"protocol_commit {pc} does not descend from the marker's introducing commit {MARKER_INTRODUCED}")
        if pc == src_commit:
            proto_ok = False
            fail("source_commit must differ from protocol_commit (the stage file is pushed alone before it)")
        elif not is_ancestor(repo, pc, src_commit):
            proto_ok = False
            fail(f"source_commit {src_commit} does not descend from protocol_commit {pc}")
        if proto_ok:
            lines.append(f"protocol: {stage_file(stage, attempt)} at {pc}, sha256 {m.get('protocol_sha256')}; the only commit adding it; "
                         f"after the marker; before source_commit")
    # the prediction record: its own earlier commit, adding only it and its gate files (finding 11)
    rec = record_file(stage, attempt)
    if rec is not None and rec in src:
        adders = git(repo, "log", "--diff-filter=A", "--format=%H", src_commit, "--", rec).decode().split()
        if len(adders) != 1 or adders[0] == src_commit:
            fail(f"{rec} must be added by exactly one commit before the source commit: {adders}")
        else:
            rc = adders[0]
            added = set(git(repo, "show", "--name-only", "--format=", rc).decode().split())
            extra_files = {p for p in added if p != rec and not re.fullmatch(rf"{re.escape(adir(attempt))}/(Gate6_\d+\.lean|check_\d+\.log)", p)}
            if extra_files:
                fail(f"the record's commit {rc} adds more than the record and its gate files: {sorted(extra_files)}")
            at_rc = hashlib.sha256(git(repo, "show", f"{rc}:{rec}")).hexdigest()
            if at_rc != src.get(rec):
                fail(f"{rec} differs between its own commit {rc} and the manifest")
            try:
                record = json.loads(git(repo, "show", f"{rc}:{rec}"))
                # the frozen gate_each (batch/predict6.py) writes a gate file exactly for each measured instance with an
                # observation; a measured instance without one (needs above 7, or a prediction that raised) has none
                gated = {x["seed"] for x in record["instances"] if x.get("measured") and "observation" in x}
                have = {int(g) for g in re.findall(rf"^{re.escape(adir(attempt))}/Gate6_(\d+)\.lean$", "\n".join(sorted(added)), re.M)}
                if gated - have:
                    fail(f"the record's commit {rc} has no gate file for measured instances with an observation {sorted(gated - have)}")
                if have - gated:
                    fail(f"the record's commit {rc} has gate files for instances that have none in the record (not measured, or no observation): {sorted(have - gated)}")
            except (ValueError, KeyError) as e:
                fail(f"{rec} at {rc} is not a prediction record: {e}")
            gate_paths = sorted(p for p in added if p != rec)
            if gate_paths:
                try:
                    git(repo, "diff", "--quiet", rc, src_commit, "--", *gate_paths)                       # N5
                except subprocess.CalledProcessError:
                    fail(f"the gate files or check logs of the record's commit {rc} differ at the source commit {src_commit}")
            if ok:
                lines.append(f"record {rec}: commit {rc}, sha256 {at_rc}, with its gate files ({len(gate_paths)} files, unchanged at the "
                             f"source commit); byte-identical in the manifest")
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
            st = c6.stage_check(repo / stage_file(stage, attempt))
            if (st["stage"], st.get("attempt")) != (stage, attempt):
                fail(f"the stage file names stage {st['stage']}, attempt {st.get('attempt')}, not {stage}, {attempt}")
            else:
                lines.append(f"stage file passes c6.stage_check: {json.dumps(st, sort_keys=True)}")
        except Exception as e:
            fail(f"the stage file does not pass c6.stage_check: {type(e).__name__}: {e}")
    lines.append(f"source_sha256: {len(src)} paths ({len(frozen)} frozen, {len(set(src) - set(frozen))} data)")
    return ok, lines


def main(argv=None):
    a = sys.argv[1:] if argv is None else argv
    stage, attempt, manifest, marker_commit = a[0], a[1], Path(a[2]), a[3]
    repo = Path(a[4]) if len(a) > 4 else HERE.parent.parent.parent
    ok, lines = check(stage, attempt, manifest, marker_commit, repo)
    own = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    text = "\n".join([f"marker_check.py sha256 {own}", f"stage {stage}", f"manifest {manifest.name} sha256 {hashlib.sha256(manifest.read_bytes()).hexdigest()}"]
                     + lines + [f"VERDICT: {'PASSED' if ok else 'REFUSED'}", ""])
    (manifest.parent / f"MARKER_CHECK_{stage}.txt").write_text(text)
    print(text, end="")
    raise SystemExit(0 if ok else 1)


if __name__ == "__main__":
    main()
