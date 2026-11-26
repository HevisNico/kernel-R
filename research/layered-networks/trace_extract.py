"""The trace extract of a stage-N round, for the post-campaign check of the premises (the owner's decision, relayed
2026-11-26; POSTCHECK_DATA.md). Development only.

**What it keeps.** ROUND/extract/trace.raw holds, from ROUND/trace.raw, the `time` vector and:
- per R cell c (every cell read in the record): v(x<c>.p) (the latch), and for each port p (1, 2) v(x<c>.vmem<p>) and
  v(x<c>.x<p>.sum). The stored voltage is u_p = vmem_p − sum_p, as instrument.py measures it. Both columns are kept
  as they are, so the difference is taken afterwards;
- per inverter n<j> (every inverter of the record): v(xn<j>.p) and v(xn<j>.vq).

The extract is in ngspice's binary raw format (the same header lines, little-endian float64 rows). Its values are the
original columns' bytes: a subset of columns, not a resampling. A missing vector is an error (exit 1), and the whole
trace is then kept.

**Parts.** An extract over 50,000,000 bytes is written as trace.raw.part-000, -001, … (each at most 50,000,000 bytes,
cut at byte boundaries) and PARTS.txt instead of trace.raw. PARTS.txt has one line per part
(`sha256  size  name`), then `whole  sha256  size  trace.raw`. `trace_extract.py join ROUND` rebuilds
extract/trace.raw and checks it against the whole sha256.

**extract.json** records:
- the source trace's digest (trace.digest.json);
- the vectors, the points and the extract's sha256 and size;
- the parts, and this script's own sha256.

ROUND/extract/SHA256SUMS covers the extract's files (the parts and PARTS.txt, or trace.raw) and the record copy.

  trace_extract.py ROUND        writes ROUND/extract/ (exit 1 if a vector is missing)
  trace_extract.py join ROUND   rebuilds ROUND/extract/trace.raw from its parts and checks it
"""
import hashlib
import json
from pathlib import Path
import sys

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import ref_extract  # noqa: E402  (its raw header reader)

PART_BYTES = 50_000_000
FORMAT = "layered-trace-extract/1"


def sha(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for b in iter(lambda: f.read(1 << 22), b""):
            h.update(b)
    return h.hexdigest()


def units(rec):
    cells = sorted({f"c{r['layer']}_{r['index']}" for s in rec["slots"] for r in s.get("reads", [])})
    n_inv = max((len(s.get("inv") or []) for s in rec["slots"]), default=0)
    return cells, [f"n{j}" for j in range(n_inv)]


def wanted(names, cells, invs):
    low = {n.lower(): j for j, n in enumerate(names)}
    keep, missing = [low["time"]], []
    bases = [f"x{c}.{v}" for c in cells for v in ("p", "vmem1", "x1.sum", "vmem2", "x2.sum")]
    bases += [f"x{n}.{v}" for n in invs for v in ("p", "vq")]
    for base in bases:
        hit = low.get(f"v({base})", low.get(base))
        if hit is None:
            missing.append(base)
        else:
            keep.append(hit)
    if missing:
        raise SystemExit(f"missing vectors {missing}")
    return keep


def extract(rnd):
    rnd = Path(rnd)
    recf = rnd / "noisy_record.json"
    rec_bytes = recf.read_bytes()
    cells, invs = units(json.loads(rec_bytes))
    pre, var, nv, npt, off = ref_extract.header(rnd / "trace.raw")
    names = [v.split()[1] for v in var]
    keep = wanted(names, cells, invs)
    data = np.memmap(rnd / "trace.raw", dtype="<f8", mode="r", offset=off, shape=(npt, nv))
    sub = np.ascontiguousarray(data[:, keep])
    out = rnd / "extract"
    out.mkdir(exist_ok=True)
    for old in list(out.glob("trace.raw*")) + list(out.glob("PARTS.txt")):     # a re-extract leaves nothing stale
        old.unlink()
    lines = [l if not l.startswith("No. Variables:") else f"No. Variables: {len(keep)}" for l in pre]
    lines += ["Variables:"] + [f"\t{i}\t{names[j]}\t{var[j].split(None, 2)[2] if len(var[j].split(None, 2)) > 2 else ''}"
                               .rstrip() for i, j in enumerate(keep)]
    raw = ("\n".join(lines) + "\nBinary:\n").encode() + sub.astype("<f8").tobytes()
    whole = hashlib.sha256(raw).hexdigest()
    (out / "noisy_record.json").write_bytes(rec_bytes)
    files = [out / "noisy_record.json"]
    parts = []
    if len(raw) > PART_BYTES:
        for k in range(0, len(raw), PART_BYTES):
            p = out / f"trace.raw.part-{k // PART_BYTES:03d}"
            p.write_bytes(raw[k:k + PART_BYTES])
            parts.append(dict(file=p.name, sha256=sha(p), size=p.stat().st_size))
            files.append(p)
        (out / "PARTS.txt").write_text("".join(f"{x['sha256']}  {x['size']}  {x['file']}\n" for x in parts)
                                       + f"whole  {whole}  {len(raw)}  trace.raw\n")
        files.append(out / "PARTS.txt")
    else:
        (out / "trace.raw").write_bytes(raw)
        files.append(out / "trace.raw")
    (out / "SHA256SUMS").write_text("".join(f"{sha(p)}  {p.name}\n" for p in sorted(files)))
    dig = json.loads((rnd / "trace.digest.json").read_text()) if (rnd / "trace.digest.json").exists() else None
    meta = dict(format=FORMAT, source_digest=dig, cells=cells, inverters=invs, vectors=[names[j] for j in keep],
                points=npt, source_variables=nv, extract=dict(file="extract/trace.raw", sha256=whole, size=len(raw)),
                parts=parts, part_bytes=PART_BYTES, trace_extract_sha256=sha(Path(__file__)))
    (out / "extract.json").write_text(json.dumps(meta, indent=1, sort_keys=True) + "\n")
    return meta


def join(rnd):
    out = Path(rnd) / "extract"
    lines = [l.split() for l in (out / "PARTS.txt").read_text().splitlines()]
    whole = next(l for l in lines if l[0] == "whole")
    h = hashlib.sha256()
    with open(out / "trace.raw", "wb") as f:
        for s, n, name in (l for l in lines if l[0] != "whole"):
            b = (out / name).read_bytes()
            assert hashlib.sha256(b).hexdigest() == s and len(b) == int(n), name
            f.write(b)
            h.update(b)
    assert h.hexdigest() == whole[1], "the joined extract does not match its whole sha256"
    return True


if __name__ == "__main__":
    a = sys.argv[1:]
    if len(a) == 2 and a[0] == "join":
        sys.exit(0 if join(a[1]) else 1)
    if len(a) != 1:
        sys.exit(__doc__)
    m = extract(a[0])
    print(json.dumps(dict(vectors=len(m["vectors"]), points=m["points"], size=m["extract"]["size"], parts=len(m["parts"]))))
