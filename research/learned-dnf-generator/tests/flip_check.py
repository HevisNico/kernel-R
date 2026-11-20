"""The flip control, in detail. For each Flip_*.lean written by tests/run_synth.py:

1. it diffs the copy against its original (Control_pass.lean or Control_fail.lean) and requires exactly one differing
   line, the flipped theorem;
2. it compiles the copy with Lean (warnings as errors) and lists every error with its line and the theorem that
   encloses it;
3. it classifies each error as "at the flipped theorem" or "elsewhere", and, for an error elsewhere, as one that
   depends on the flipped theorem (a later theorem whose text names it) or not.

  python -I tests/flip_check.py M4_DIR LEAN BUILD_DIR      (BUILD_DIR: the compiled theory, e.g. GENCHECK_BUILD)

Prints a JSON report. Exits non-zero if a copy differs in more than one line, compiles, or has an error that neither is
at the flipped theorem nor depends on it.
"""
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile


def theorem_at(lines, n):
    """The name of the theorem whose text contains line n (1-based)."""
    name = None
    for k in range(n, 0, -1):
        m = re.match(r"^theorem (\S+) ", lines[k - 1])
        if m:
            return m.group(1)
        if lines[k - 1].startswith(("def ", "private def ")):
            return lines[k - 1].split()[1 if lines[k - 1].startswith("def ") else 2]
    return name


def main():
    d, lean, build = Path(sys.argv[1]), sys.argv[2], Path(sys.argv[3]).resolve()
    out, bad = [], 0
    for f in sorted(d.glob("Flip_*.lean")):
        orig = d / ("Control_pass.lean" if f.name.startswith("Flip_pass") else "Control_fail.lean")
        a, b = orig.read_text().splitlines(), f.read_text().splitlines()
        diff = [k + 1 for k, (x, y) in enumerate(zip(a, b)) if x != y] + (["length differs"] if len(a) != len(b) else [])
        flipped = theorem_at(b, diff[0]) if diff and diff[0] != "length differs" else None
        with tempfile.TemporaryDirectory() as tmp:
            shutil.copy(f, Path(tmp) / f.name)
            env = dict(os.environ, LEAN_PATH=str(build))
            p = subprocess.run([lean, "-DwarningAsError=true", f.name], cwd=tmp, env=env, capture_output=True, text=True)
        errs = []
        for m in re.finditer(r"^" + re.escape(f.name) + r":(\d+):(\d+): error: (.*)$", p.stdout + p.stderr, flags=re.M):
            line = int(m.group(1))
            th = theorem_at(b, line)
            start = next(k for k in range(line, 0, -1) if b[k - 1].startswith(f"theorem {th} "))
            end = next((k for k in range(start, len(b)) if not b[k].strip()), len(b))
            body = "\n".join(b[start:end])          # the theorem's proof, after its statement line
            errs.append(dict(line=line, theorem=th, message=m.group(3)[:100], at_flipped=th == flipped,
                             depends_on_flipped=th != flipped and flipped is not None and flipped in body))
        ok = len(diff) == 1 and p.returncode != 0 and errs and all(e["at_flipped"] or e["depends_on_flipped"] for e in errs) \
            and any(e["at_flipped"] for e in errs)
        bad += not ok
        out.append(dict(file=f.name, original=orig.name, differing_lines=diff, flipped_theorem=flipped,
                        flipped_line=b[diff[0] - 1] if len(diff) == 1 else None, returncode=p.returncode, errors=errs, ok=ok))
    print(json.dumps(out, indent=1))
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
