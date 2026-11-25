"""The save_ref round's comparator vectors, kept before its trace.raw is deleted (defect 2 of the pre-freeze dry run,
2026-11-25). Development only.

The defect: campaign_run5 deletes a round's trace.raw when its comparison agrees. The save_ref round (controls5
save_ref=1) holds each inverter's comparator reference only in that trace, and its record keeps just the vector names.
So the comparator noise could not be read from a campaign root.

The choice: **extraction**, not keeping the whole trace. The whole trace is 2.7 GB for an XOR3 round; the extract is
about 45 MB for XOR3 and 4 MB for NOT1.
- **Where.** Before the raw is deleted, ROUND/ref/trace.raw is written in ngspice's binary raw format (the same header
  lines, the same little-endian float64 rows).
- **Vectors.** It holds the `time` vector and, per inverter x<j>, the vectors that tests/check_ref_level.py and
  tests/check_noise_sources.py read: x<j>.vrefm, x<j>.vrefmn, x<j>.nzm (or v(...)), nzh<j>, nzj<j>. The values are the
  original columns' bytes, unchanged: a subset of columns, not a resampling.
- **ROUND/ref/noisy_record.json**: a byte copy of the round's record, which check_ref_level reads with the trace.
- **ROUND/ref/SHA256SUMS** covers both files. **ROUND/ref/ref.json** records the source trace's digest (from
  trace.digest.json), the vectors kept, the number of points and the extract's sha256 and size. Being a .json in the
  instance folder, it is also in the instance's SHA256SUMS.

  ref_extract.py ROUND           writes ROUND/ref/ (exit 1 if a needed vector is missing)
  then: tests/check_ref_level.py ROUND/ref     (in the controls tree) reads the comparator level from the extract
"""
import hashlib
import json
from pathlib import Path
import sys

import numpy as np


def header(path):
    with open(path, "rb") as f:
        head = b""
        while b"Binary:\n" not in head:
            chunk = f.read(1 << 16)
            if not chunk:
                raise SystemExit(f"{path}: no Binary: section")
            head += chunk
    i = head.find(b"Binary:\n")
    lines = head[:i].decode(errors="replace").splitlines()
    nv = int(next(l for l in lines if l.startswith("No. Variables:")).split(":")[1])
    npt = int(next(l for l in lines if l.startswith("No. Points:")).split(":")[1])
    k = lines.index("Variables:")
    var = [lines[k + 1 + j] for j in range(nv)]
    return lines[:k], var, nv, npt, i + len(b"Binary:\n")


def wanted(names, n_inv):
    low = {n.lower(): j for j, n in enumerate(names)}
    keep = [low["time"]]
    for j in range(n_inv):
        for base in (f"xn{j}.vrefm", f"xn{j}.vrefmn", f"xn{j}.nzm", f"nzhn{j}", f"nzjn{j}"):
            hit = low.get(base, low.get(f"v({base})"))
            if hit is None:
                raise SystemExit(f"missing vector {base}")
            keep.append(hit)
    return keep


def extract(rnd):
    rnd = Path(rnd)
    rec_bytes = (rnd / "noisy_record.json").read_bytes()
    rec = json.loads(rec_bytes)
    if not rec.get("saved_ref"):
        raise SystemExit(f"{rnd}: the record has no saved_ref (not a save_ref round)")
    n_inv = len(rec["slots"][0].get("inv", []))
    pre, var, nv, npt, off = header(rnd / "trace.raw")
    names = [v.split()[1] for v in var]
    keep = wanted(names, n_inv)
    data = np.memmap(rnd / "trace.raw", dtype="<f8", mode="r", offset=off, shape=(npt, nv))
    sub = np.ascontiguousarray(data[:, keep])
    out = rnd / "ref"
    out.mkdir(exist_ok=True)
    lines = [l if not l.startswith("No. Variables:") else f"No. Variables: {len(keep)}" for l in pre]
    lines += ["Variables:"] + [f"\t{i}\t{names[j]}\t{var[j].split(None, 2)[2] if len(var[j].split(None, 2)) > 2 else ''}"
                               .rstrip() for i, j in enumerate(keep)]
    raw = ("\n".join(lines) + "\nBinary:\n").encode() + sub.astype("<f8").tobytes()
    (out / "trace.raw").write_bytes(raw)
    (out / "noisy_record.json").write_bytes(rec_bytes)
    files = [out / "noisy_record.json", out / "trace.raw"]
    sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
    (out / "SHA256SUMS").write_text("".join(f"{sha(p)}  {p.name}\n" for p in files))
    dig = json.loads((rnd / "trace.digest.json").read_text()) if (rnd / "trace.digest.json").exists() else None
    meta = dict(format="layered-ref-extract/1", source_digest=dig, vectors=[names[j] for j in keep], points=npt,
                source_variables=nv, extract=dict(file="ref/trace.raw", sha256=sha(out / "trace.raw"),
                                                  size=(out / "trace.raw").stat().st_size))
    (out / "ref.json").write_text(json.dumps(meta, indent=1, sort_keys=True) + "\n")
    return meta


if __name__ == "__main__":
    if len(sys.argv) != 2:
        sys.exit(__doc__)
    m = extract(sys.argv[1])
    print(json.dumps(dict(vectors=len(m["vectors"]), points=m["points"], size=m["extract"]["size"])))
