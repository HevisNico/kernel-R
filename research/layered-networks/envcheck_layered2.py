"""envcheck_layered.py with a numpy fingerprint that does not depend on the install path (defect 5 of the pre-freeze dry
run, 2026-11-25). Development only. envcheck_layered.py is kept as it is.

The defect: ENV.json's `numpy.record_sha256` is the sha256 of numpy's dist-info RECORD. RECORD lists the console
scripts bin/f2py and bin/numpy-config, whose shebang line holds the venv's python path. So two machines with the same
numpy got different static_sha256 values (02ff71db against a230eb9f in the dry run).

Here `numpy` in `static` is {version, files_sha256, files}:
- **The files**: every file RECORD lists under the package directories numpy/ and numpy.libs/, excluding __pycache__/
  (compiled bytecode holds the source path). It covers neither bin/ nor the dist-info.
- **files_sha256**: the sha256 of the lines "<sha256 of the file's bytes on disk>  <path relative to site-packages>\n",
  sorted by path. It is the files' actual content, not RECORD's claims.
- **files**: their number.

Everything else is envcheck_layered.env, unchanged. The format is "layered-env/2".

  envcheck_layered2.py [--json OUT]               the checks of envcheck_layered.py (unchanged)
  envcheck_layered2.py env OUTROOT [PLAN.json]    writes OUTROOT/ENV.json in format layered-env/2
  envcheck_layered2.py numpy                      prints numpy's fingerprint
"""
import hashlib
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import envcheck_layered as E  # noqa: E402

PACKAGE_DIRS = ("numpy/", "numpy.libs/")
FORMAT = "layered-env/2"


def numpy_fingerprint():
    try:
        import numpy
        from importlib import metadata
    except ImportError:
        return dict(version=None, files_sha256=None, files=0)
    dist = metadata.distribution("numpy")
    rows = []
    for f in dist.files or []:
        s = str(f).replace("\\", "/")
        if not s.startswith(PACKAGE_DIRS) or "/__pycache__/" in s:
            continue
        p = Path(dist.locate_file(f))
        if p.is_file():
            rows.append((s, hashlib.sha256(p.read_bytes()).hexdigest()))
    rows.sort()
    text = "".join(f"{h}  {s}\n" for s, h in rows)
    return dict(version=numpy.__version__, files_sha256=hashlib.sha256(text.encode()).hexdigest(), files=len(rows))


def env(plan=None):
    e = E.env(plan)
    static = dict(e["static"], numpy=numpy_fingerprint())
    return dict(e, format=FORMAT, static=static, static_sha256=hashlib.sha256(E.canon(static)).hexdigest())


if __name__ == "__main__":
    a = sys.argv[1:]
    if a and a[0] == "env":
        root = Path(a[1])
        plan = json.loads(Path(a[2]).read_text()) if len(a) > 2 else None
        root.mkdir(parents=True, exist_ok=True)
        (root / "ENV.json").write_bytes(E.canon(env(plan)))
        print((root / "ENV.json").read_text())
    elif a and a[0] == "numpy":
        print(json.dumps(numpy_fingerprint()))
    else:
        import runpy
        sys.argv = [str(HERE / "envcheck_layered.py")] + a
        runpy.run_path(str(HERE / "envcheck_layered.py"), run_name="__main__")
