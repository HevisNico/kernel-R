"""campaign_run13.py with the kernel at stage D, the trace extract and keep_raw as plan_split2 states it (the owner's
decisions, relayed 2026-11-26). Development only. campaign_run13.py and the earlier drivers are kept as they are.

**The template.** TEMPLATE_CAMPAIGN_2.json, pinned here by its sha256 (TEMPLATE_SHA256) and in FREEZE_PINS_3.json. The
template check is campaign_run13's, against this template:
- a missing or different shared key is refused, and so is a key outside the template and the per-machine keys;
- the trees are given by commit, and the K3 budget by sha256;
- a rehearsal `template=FILE` may differ in seal_push.remote alone.

The old template (TEMPLATE_CAMPAIGN.json) and any plan made from it are refused: stage_d_script stage_d5.py, and no
`kernel` or `trace_extract` key.

**The kernel (stage_d6.py).**
- Before any step, the Lean library (LayeredMonotoneCheckerProofs and its 11 imports) is built once per machine into
  OUTROOT/kernel_build, from the stage-D tree's research/learned-coincidence. It takes about 42 s.
- The 12 sources must have the sha256 of KERNEL_SOURCES, or the run is refused. OUTROOT/kernel_build/KERNEL_BUILD.json
  records them, the lean binary's sha256 and the build time. A resumed run reuses the build when the sources match.
- stage_d6 is given the build in LAYERED_KERNEL_BUILD. A kernel–mirror disagreement fails step D, so the instance is not
  completed; the clause is in D/prediction.json `kernel.disagreements`.

**The trace extract (trace_extract.py).**
- In every N round of every instance (not the U control, not the duplicates DUP_/DUPX_, whose raws are kept anyway),
  the extract is written to N<n>/extract/ before the round's trace.raw may be deleted. Extracts over 50 MB are split
  into parts with PARTS.txt.
- A failed extract keeps the whole trace and writes N<n>/extract_failed.json.

**keep_raw, as plan_split2.py's docstring says.** For an instance named in PLAN keep_raw (the original of a remote
duplicate), only N0's trace.raw is kept, as the remote duplicate compares N0 only. Its N1–N3 raws follow the rule of
every other instance: they are deleted when their comparison agrees. campaign_run13 kept every round.

  campaign_run14.py launch PLAN.json OUTROOT [jobs=4] [template=FILE]
  campaign_run14.py run    PLAN.json OUTROOT [jobs=4] [template=FILE]     (what launch starts)
  campaign_run14.py check  PLAN.json [template=FILE]                      the check alone, as JSON; exit 1 if refused
  campaign_run14.py wait | status ...                                     as campaign_run13.py
"""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import campaign_run as CR  # noqa: E402
import campaign_run2 as C2  # noqa: E402
import campaign_run5 as C5  # noqa: E402
import campaign_run9 as C9  # noqa: E402
import campaign_run12 as C12  # noqa: E402
import campaign_run13 as C13  # noqa: E402
import stage_d6  # noqa: E402
import trace_extract  # noqa: E402

TEMPLATE = HERE / "TEMPLATE_CAMPAIGN_2.json"
TEMPLATE_SHA256 = "c1219a547fecf70b0b478cb62fa51938dfac444bc42762c7df34cae4c1fd5784"
KERNEL_SOURCES = {
    "Target.lean": "da5db52c5f04caa7599360a1538a8de8d5d396a8fcc91c550702cba7715fc7e5",
    "TwoLayerTarget.lean": "eed817c647d8db83c4a2015ec89d756eaeb000acdb18a8b4922737604a8eccf6",
    "MonotoneTarget.lean": "779797babfdaebf5bd4aeddf0128f7703093fa3b5c5cac762565f914f7f016e0",
    "MonotoneSupport.lean": "52156bbeb384840c67a3323c8335d7f1d7497cdd0b544e4addec0e56543a1678",
    "MonotoneOneSidedTarget.lean": "a44f60699aba2563c0ea4ab6e139bac71ab095e54a58673829335d93d567c8f3",
    "LayeredMonotoneTarget.lean": "521fdfee3f06893a879a1990b6d0e319536039cfe6d2acb7a47254e573fb6dec",
    "MonotonePremiseTargets.lean": "674e6783c0e4cba994d628f58e5ee66f8199010c5d5c25fb2f04c9393d27f30f",
    "LayeredMonotoneCheckerTargets.lean": "81c29cdf0c953a6ae7ef424c25dfde858a52f6c40dfe65cd29c9cb9c3f4d1fe8",
    "MonotonePremiseSoundness.lean": "57653f1f9644f5722038478a3d8837aec048b48f9042f90f874d74693d03d40f",
    "MonotonePremiseCompletenessTargets.lean": "e18070717f4d142d37ce10c4a3b78fa76699d1e35aeab7abea794044e5f69b5a",
    "MonotonePremiseCompleteness.lean": "6820f1b6f015e257d8b248e30ac361bfc9868dea5e529b64e36874f0608443a4",
    "LayeredMonotoneCheckerProofs.lean": "4dedf666f31dde8c9476c73bfd0fc5472850c5defc13e25e4dd8a0c696201657",
}
Refused = C13.Refused


def load_template(path=None):
    saved = C13.TEMPLATE, C13.TEMPLATE_SHA256
    C13.TEMPLATE, C13.TEMPLATE_SHA256 = TEMPLATE, TEMPLATE_SHA256
    try:
        t, tc = C13.load_template(path)
    finally:
        C13.TEMPLATE, C13.TEMPLATE_SHA256 = saved
    tc["driver"] = "campaign_run14.py"
    return t, tc


def check(plan_path, template_path=None):
    template, tc = load_template(template_path)
    b = Path(plan_path).read_bytes()
    plan = json.loads(b)
    bad = C13.check_plan(plan, template)
    if bad:
        raise Refused("refused: the plan differs from the template: " + "; ".join(bad))
    trees = C13.resolve_trees(plan, template)
    tc.update(plan_input_sha256=C13.sha_bytes(b), trees=trees, k3_budget_sha256=template["k3_budget_sha256"], ok=True)
    return plan, b, dict(plan, **trees), tc


# ------------------------------------------------------------------------------------------------ the kernel library

def build_kernel(root):
    src = stage_d6.LEAN_DIR
    have = {f"{m}.lean": CR.sha(src / f"{m}.lean") for m in stage_d6.CLOSURE}
    bad = sorted(k for k in KERNEL_SOURCES if have.get(k) != KERNEL_SOURCES[k])
    if bad or set(have) != set(KERNEL_SOURCES):
        raise Refused(f"refused: the kernel's Lean sources differ from the pinned ones: {bad}")
    build = Path(root) / "kernel_build"
    meta_f = build / "KERNEL_BUILD.json"
    lean = shutil.which("lean")
    lean_sha = CR.sha(Path(os.path.realpath(lean))) if lean else None
    if meta_f.exists():
        meta = json.loads(meta_f.read_text())
        if meta.get("sources_sha256") == KERNEL_SOURCES and (build / "LayeredMonotoneCheckerProofs.olean").exists():
            return build, meta
        shutil.rmtree(build)
    build.mkdir(parents=True)
    t0 = time.time()
    env = dict(os.environ, LEAN_PATH=str(build))
    for m in stage_d6.CLOSURE:
        p = subprocess.run(["lean", "-o", str(build / f"{m}.olean"), f"{m}.lean"], cwd=src, env=env, capture_output=True,
                           text=True, timeout=3600)
        if p.returncode:
            raise Refused(f"refused: the kernel library does not build ({m}): {(p.stdout + p.stderr)[-1500:]}")
    meta = dict(format="layered-kernel-build/1", sources_sha256=KERNEL_SOURCES, lean_binary_sha256=lean_sha,
                modules=stage_d6.CLOSURE, seconds=round(time.time() - t0, 1))
    meta_f.write_text(json.dumps(meta, indent=1, sort_keys=True) + "\n")
    return build, meta


# ------------------------------------------------------------------------------------------------ extract and keep_raw

_c9_drop_raw = C9.drop_raw
_cr_drop_raw = C5._drop_raw


def is_round(folder):
    return folder.name[:1] == "N" and folder.name[1:].isdigit()


def drop_raw(folder):
    folder = Path(folder)
    inst = folder.parent.name
    plain = not inst.startswith(("DUP_", "DUPX_", "U_"))
    if plain and is_round(folder) and (folder / "trace.raw").exists() and not (folder / "extract" / "extract.json").exists():
        try:
            trace_extract.extract(folder)
        except (SystemExit, Exception) as e:              # the whole trace is then kept
            (folder / "extract_failed.json").write_text(json.dumps(dict(ok=False, why=str(e)), indent=1) + "\n")
            return
    if plain and is_round(folder) and inst in C5.STATE["keep"] and folder.name != "N0":
        comp = folder / "comparison.json"                 # keep_raw keeps N0 only (plan_split2.py's docstring)
        if comp.exists() and json.loads(comp.read_text()).get("verdict") == "agrees":
            _cr_drop_raw(folder)
        return
    return _c9_drop_raw(folder)


# ------------------------------------------------------------------------------------------------ run and launch

def cmd_run(plan_path, root, *rest):
    tpl, rest = C13.opts(rest)
    plan, b, resolved, tc = check(plan_path, tpl)
    root = Path(root).resolve()
    root.mkdir(parents=True, exist_ok=True)
    C13.write_once(root / "PLAN_INPUT.json", b)
    C13.write_once(root / "TEMPLATE_CHECK.json", (json.dumps(tc, indent=1, sort_keys=True) + "\n").encode())
    rp = root / "PLAN_RESOLVED.json"
    C13.write_once(rp, (json.dumps(resolved, indent=1, sort_keys=True) + "\n").encode())
    build, _ = build_kernel(root)
    os.environ["LAYERED_KERNEL_BUILD"] = str(build)
    C9.drop_raw = drop_raw
    try:
        return C12.cmd_run(str(rp), str(root), *rest)
    finally:
        C9.drop_raw = _c9_drop_raw


def cmd_launch(plan_path, root, *rest):
    tpl, _ = C13.opts(rest)
    check(plan_path, tpl)                                    # refused before anything is written
    C12.refuse_unless_env()
    root = Path(root).resolve()
    n = subprocess.run(["pgrep", "-c", "ngspice"], capture_output=True, text=True).stdout.strip()
    if n not in ("", "0"):
        raise Refused(f"refused: {n} ngspice process(es) running")
    if root.exists() and any(root.iterdir()):
        raise Refused(f"refused: {root} exists and is not empty (no run folders before a launch)")
    plan = json.loads(Path(plan_path).read_text())
    root.mkdir(parents=True, exist_ok=True)
    (root / "INVENTORY_START").write_text(C2.inventory(plan))
    log = (root / "driver.log").open("w")
    p = subprocess.Popen(["nohup", CR.PY, "-B", str(HERE / "campaign_run14.py"), "run", str(Path(plan_path).resolve()),
                          str(root), *rest], stdout=log, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL,
                         start_new_session=True, cwd=HERE)
    (root / "DRIVER_PID").write_text(f"{p.pid}\n")
    print(f"launched pid {p.pid}")
    return True


def cmd_check(plan_path, *rest):
    tpl, _ = C13.opts(rest)
    try:
        _, _, _, tc = check(plan_path, tpl)
    except Refused as e:
        print(json.dumps(dict(ok=False, why=str(e))))
        return False
    print(json.dumps(tc, sort_keys=True))
    return True


if __name__ == "__main__":
    c, *a = sys.argv[1:] or ["help"]
    if c == "run":
        sys.exit(0 if cmd_run(*a) else 1)
    elif c == "launch":
        sys.exit(0 if cmd_launch(*a) else 1)
    elif c == "check":
        sys.exit(0 if cmd_check(*a) else 1)
    elif c == "wait":
        sys.exit(0 if C2.cmd_wait(*a) else 3)
    elif c == "status":
        C2.cmd_status(*a)
    else:
        sys.exit(__doc__)
