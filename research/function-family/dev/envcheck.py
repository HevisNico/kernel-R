"""Development only: the environment check each machine of the top-up runs before any run (MACHINE_PLAN.md 3).
It runs no simulation. It writes ENV_<MACHINE>.json and exits non-zero if any check fails.

  envcheck.py MACHINE NGSPICE PDK WHEEL OUT_JSON

Checks, each recorded with what was seen:
  1. this interpreter is CPython 3.12.3 whose executable has the pinned SHA-256 (c4.PINNED's python_sha256);
  2. numpy is 2.3.5, installed in a venv that is NOT at c4.PINNED_VENV (TOPUP_RULES.md 0: the pinned RECORD hash cannot
     be rebuilt; outside the pinned path require_pinned checks the versions only);
  3. WHEEL is the official numpy 2.3.5 cp312 manylinux wheel, SHA-256 WHEEL_SHA256 below;
  4. numpy's installed RECORD has exactly the wheel's RECORD entries, byte for byte, plus only the installer lines
     (INSTALLER, REQUESTED and the two bin scripts), and every file on disk matches its RECORD hash;
  5. NGSPICE has the pinned SHA-256 and reports ngspice-42;
  6. PDK is a clean git checkout at the pinned commit 1232782c1b9fab3aacda74d67ce7c92bf7da8105.
The pinned numpy RECORD SHA-256 (064003bd…) and this venv's are both recorded.
"""
import base64
import hashlib
import importlib.metadata
import json
import os
import platform
from pathlib import Path
import subprocess
import sys
import zipfile

PYTHON_SHA256 = "e50d468e8b0adfb05733f5b87b3cff34829c4a8c1aea50c865aa8bdfe4bb150f"
NGSPICE_SHA256 = "820658317b0b54035208da41936fd6871ce924036e5ea4113a4168b821b7fc45"
PDK_COMMIT = "1232782c1b9fab3aacda74d67ce7c92bf7da8105"
WHEEL_SHA256 = "0d8163f43acde9a73c2a33605353a4f1bc4798745a8b1d73183b28e5b435ae28"
PINNED_RECORD_SHA256 = "064003bdb6f9f7bb06e46e07cc3398cbfdc3c114dfe55b89d239e564917be2fb"
PINNED_VENV = "/home/user/owner-prep/venv312"
INSTALLER_LINES = {"../../../bin/f2py", "../../../bin/numpy-config", "numpy-2.3.5.dist-info/INSTALLER", "numpy-2.3.5.dist-info/REQUESTED"}


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def record_lines(text):
    return {l.split(",")[0]: l.split(",", 1)[1] for l in text.splitlines() if l.strip()}


def numpy_checks(wheel):
    import numpy
    dist = importlib.metadata.distribution("numpy")
    installed_text = dist.read_text("RECORD")
    base = Path(dist.locate_file(""))
    z = zipfile.ZipFile(wheel)
    w = record_lines(z.read(next(n for n in z.namelist() if n.endswith(".dist-info/RECORD"))).decode())
    i = record_lines(installed_text)
    differ = sorted(k for k in w if k in i and i[k] != w[k])
    missing = sorted(k for k in w if k not in i)
    extra = sorted(k for k in i if k not in w)
    bad_files, hashed = [], 0
    for path, h in i.items():
        h = h.rsplit(",", 1)[0]
        if not h:
            continue
        hashed += 1
        digest = base64.urlsafe_b64encode(hashlib.sha256((base / path).read_bytes()).digest()).rstrip(b"=").decode()
        if h != f"sha256={digest}":
            bad_files.append(path)
    return dict(numpy_version=numpy.__version__, wheel_sha256=sha(wheel), wheel_entries=len(w), installed_entries=len(i),
                record_sha256=hashlib.sha256(installed_text.encode()).hexdigest(), pinned_record_sha256=PINNED_RECORD_SHA256,
                differing=differ, missing_from_installed=missing, extra_in_installed=extra,
                files_hashed=hashed, files_not_matching=bad_files,
                ok=(numpy.__version__ == "2.3.5" and sha(wheel) == WHEEL_SHA256 and not differ and not missing
                    and set(extra) <= INSTALLER_LINES and not bad_files))


def main(machine, ngspice, pdk, wheel, out_json):
    exe = os.path.realpath(sys.executable)
    seen = dict(machine=machine, python_version=platform.python_version(), python_sha256=sha(exe), executable=sys.executable, prefix=sys.prefix)
    checks = dict(python=seen["python_version"] == "3.12.3" and seen["python_sha256"] == PYTHON_SHA256,
                  venv_not_at_pinned_path=sys.prefix != PINNED_VENV)
    seen["numpy"] = numpy_checks(wheel)
    checks["numpy_and_record_against_wheel"] = seen["numpy"]["ok"]
    ng = os.path.realpath(ngspice)
    seen["ngspice_sha256"] = sha(ng)
    version = subprocess.run([ng, "-v"], capture_output=True, text=True).stdout
    seen["ngspice_version_line"] = next((l for l in version.splitlines() if "ngspice-" in l), "")
    checks["ngspice"] = seen["ngspice_sha256"] == NGSPICE_SHA256 and "ngspice-42" in seen["ngspice_version_line"]
    head = subprocess.run(["git", "-C", str(pdk), "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
    dirty = subprocess.run(["git", "-C", str(pdk), "status", "--porcelain"], capture_output=True, text=True).stdout.strip()
    seen["pdk_commit"], seen["pdk_clean"] = head, dirty == ""
    checks["pdk"] = head == PDK_COMMIT and dirty == ""
    out = dict(seen=seen, checks=checks, all_ok=all(checks.values()))
    Path(out_json).write_text(json.dumps(out, indent=1) + "\n")
    print(json.dumps(dict(machine=machine, checks=checks, all_ok=out["all_ok"])))
    return out


if __name__ == "__main__":
    a = sys.argv[1:]
    if len(a) != 5:
        raise SystemExit(__doc__)
    sys.exit(0 if main(*a)["all_ok"] else 1)
