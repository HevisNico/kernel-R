"""Tests of campaign_run17.py through cmd_run, the real path (ngspice, Lean 4.35.0 and the pinned environment on PATH;
about 30 min).

  python -B tests/test_campaign_run17.py SEAL_LOG_WITH_HOME
SEAL_LOG_WITH_HOME is a bare seal log whose branch evidence/combined-seals-K02 has NOT1_6212's SEALS.txt line (the
end-to-end check's seallog.git).

The plans are plan_split3's, on NOT1 6212, 6213, 6217, 6218, 6219, 6220 with m = 8. Each case runs the driver's cmd_run
in a subprocess, on a fresh root and a fresh bare seal log. campaign_run5's free-space reading is real until the
instance's N0 is done; from then on it reads 1 GB, below the 20 GB guard. So the chain runs for real up to N0, and the
guard decides what follows.
1. **campaign_run16 fails** (K01, NOT1_6220): RecursionError in job_errors, and no C0. This would have caught D4.
2. **campaign_run17 on K01** (NOT1_6220, audited):
   - C0 runs (done) and is logged in GUARD_EXEMPT.json;
   - the N0 raw is deleted after its extract;
   - N1 is held: no status entry, listed in stopped_for_disk;
   - no job error.
3. **campaign_run17 on K02** (NOT1_6212, U of NOT1, keep_raw): C0 runs; the N0 raw is kept; U is held (held_for_disk,
   nothing written); no job error.
4. **campaign_run17 on K07** (the duplicate of NOT1_6212 only), with the reading at 1 GB from the start: the duplicate
   finds its home's line in SEAL_LOG_WITH_HOME at once, then is held, not completed (held_for_disk); its N0 is not
   run.
"""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parents[1]
SEAL_HOME = Path(sys.argv[1]) if len(sys.argv) > 1 else None
DRAW = {"format": "layered-draw/1", "groups": {"NOT1": [6212, 6213, 6217, 6218, 6219, 6220]}}

DRIVE = r'''
import shutil, sys
from pathlib import Path
sys.path.insert(0, {here!r})
import campaign_run5 as C5
ROOT, MODE = Path({root!r}), {mode!r}
class Shim:
    def __getattr__(self, k):
        return getattr(shutil, k)
    @staticmethod
    def disk_usage(p):
        u = shutil.disk_usage(p)
        low = MODE == "always" or any(ROOT.glob("*/N0/noisy_record.json"))
        return type(u)(u.total, u.total - 10**9, 10**9) if low else u
C5.shutil = Shim()
import {mod} as D
print("RC", D.cmd_run({plan!r}, {root!r}, "jobs=4", "template=" + {tpl!r}))
'''


def plans_for(d, template_name, remote):
    sys.path.insert(0, str(HERE))
    import plan_split3 as PS3
    pin = json.loads((HERE / template_name).read_text())
    tpl = d / f"T_{template_name}_{Path(remote).name}"
    t = dict(pin, seal_push=dict(pin["seal_push"], remote=str(remote)))
    tpl.write_text(json.dumps(t))
    plans, _ = PS3.split(DRAW, t, 8)
    return {f"K{k + 1:02d}": p for k, p in enumerate(plans)}, tpl


def drive(d, mod, template_name, machine, mode="after_N0", remote=None):
    if remote is None:
        remote = d / f"log_{mod}_{machine}.git"
        subprocess.run(["git", "init", "-q", "--bare", str(remote)], check=True)
    plans, tpl = plans_for(d, template_name, remote)
    pf = d / f"PLAN_{mod}_{machine}.json"
    pf.write_text(json.dumps(plans[machine], indent=1, sort_keys=True))
    root = d / f"root_{mod}_{machine}"
    code = DRIVE.format(here=str(HERE), mod=mod, plan=str(pf), root=str(root), tpl=str(tpl), mode=mode)
    p = subprocess.run([sys.executable, "-B", "-c", code], cwd=HERE, capture_output=True, text=True, timeout=5400)
    r = json.loads((root / "RESULT.json").read_text()) if (root / "RESULT.json").exists() else None
    assert r is not None, (p.stdout[-800:], p.stderr[-2500:])
    return root, r


def status(root, inst):
    return json.loads((root / inst / "status.json").read_text())["steps"]


def test_campaign_run16_recursion():
    with tempfile.TemporaryDirectory() as d:
        root, r = drive(Path(d), "campaign_run16", "TEMPLATE_CAMPAIGN_4.json", "K01")
        print(" campaign_run16 K01:", r["job_errors"])
        assert any("RecursionError" in e["error"] for e in r["job_errors"]) and "C0" not in status(root, "NOT1_6220")


def test_campaign_run17_c_exempt_n_held():
    with tempfile.TemporaryDirectory() as d:
        root, r = drive(Path(d), "campaign_run17", "TEMPLATE_CAMPAIGN_5.json", "K01")
        st, n0 = status(root, "NOT1_6220"), root / "NOT1_6220" / "N0"
        ex = json.loads((root / "GUARD_EXEMPT.json").read_text())
        held = [(h["instance"], h["step"]) for h in r["stopped_for_disk"]]
        print(" campaign_run17 K01: C0", st.get("C0", {}).get("status"), "| exempt", [e["step"] for e in ex],
              "| N0 raw deleted", not (n0 / "trace.raw").exists(), "| extract", (n0 / "extract" / "extract.json").exists(),
              "| held", held, "| errors", r["job_errors"])
        assert r["job_errors"] == [] and st["C0"]["status"] == "done" and [e["step"] for e in ex] == ["C0"]
        assert not (n0 / "trace.raw").exists() and (n0 / "extract" / "extract.json").exists()
        assert "N1" not in st and ("NOT1_6220", "N1") in held


def test_campaign_run17_u_held():
    with tempfile.TemporaryDirectory() as d:
        root, r = drive(Path(d), "campaign_run17", "TEMPLATE_CAMPAIGN_5.json", "K02")
        st, u = status(root, "NOT1_6212"), r["controls"]["U"]
        print(" campaign_run17 K02: C0", st.get("C0", {}).get("status"), "| N0 raw kept",
              (root / "NOT1_6212" / "N0" / "trace.raw").exists(), "| U", u, "| errors", r["job_errors"])
        assert r["job_errors"] == [] and st["C0"]["status"] == "done" and (root / "NOT1_6212" / "N0" / "trace.raw").exists()
        assert len(u) == 1 and u[0].get("held_for_disk") and u[0]["ok"] is None
        assert not (root / "U_NOT1_6212" / "untrained.json").exists()


def test_campaign_run17_duplicate_held():
    if SEAL_HOME is None:
        print(" skipped (no seal log with the home's line given)")
        return
    with tempfile.TemporaryDirectory() as d:
        root, r = drive(Path(d), "campaign_run17", "TEMPLATE_CAMPAIGN_5.json", "K07", mode="always", remote=SEAL_HOME)
        dup = r["remote_duplicates"]
        w = json.loads((root / "DUPX_NOT1_6212" / "seal_wait.json").read_text())
        print(" campaign_run17 K07:", dup, "| wait attempts", len(w["attempts"]), "found", w["found"])
        assert len(dup) == 1 and dup[0]["not_completed"] and dup[0].get("held_for_disk")
        assert w["found"] and not (root / "DUPX_NOT1_6212" / "N0").exists()


def test_templates_and_binding():
    sys.path.insert(0, str(HERE))
    import campaign_run16 as C16
    import campaign_run17 as C17
    t, tc = C17.load_template()
    assert tc["template_sha256"] == C17.TEMPLATE_SHA256 and t["driver"] == "campaign_run17.py" and t["disk_launch_gb"] == 40
    for old in ("TEMPLATE_CAMPAIGN.json", "TEMPLATE_CAMPAIGN_2.json", "TEMPLATE_CAMPAIGN_3.json", "TEMPLATE_CAMPAIGN_4.json"):
        try:
            C17.load_template(HERE / old)
            raise AssertionError(f"{old} accepted")
        except C17.Refused:
            pass
    t4, _ = C16.load_template()
    p5 = dict(t, groups={}, U_groups=[], remote_duplicates=[], controls={}, keep_raw=[],
              seal_push=dict(t["seal_push"], branch="evidence/combined-seals-K01"))
    assert any("key driver is not allowed" in b for b in C16.C13.check_plan(p5, t4))
    assert C17._C5.__mro__[1].__module__ == "campaign_run4" and C17._PARENT_STEP is C17._C5.__mro__[1].step


if __name__ == "__main__":
    os.environ.setdefault("LAYERED_ENV_SHA256", "test")
    n = 0
    for k, f in list(globals().items()):
        if k.startswith("test_"):
            f()
            n += 1
            print("ok", k, flush=True)
    print(f"{n} tests passed")
