"""yield_lot.py's report, after an integrity check of every machine's OUTROOT (the coordinator's relay of 2026-11-25).
Development only. yield_lot.py is kept as it is; YIELD.json is its report() unchanged.

The check, per ROOT:
- **Per-instance:** every line of every SHA256SUMS below ROOT except the top level (lean_build skipped, as in
  `campaign_run.py verify`) must match. A missing or different file is a failure.
- **Top level:** every line of ROOT/SHA256SUMS must match, with one known exception, the defect of campaign_run3/4/5.
  Those drivers add keys to RESULT.json after campaign_run2 hashed it. The RESULT.json line is accepted only when
  RESULT.json, with exactly those keys removed (core_budget, remote_duplicates, stopped_for_disk) and written as
  campaign_run2 writes it, gives the recorded hash. Anything else is a failure.

- **Pushed copies** (the evidence/yield-lot-K<nn> branches): a file listed in a SHA256SUMS but absent from the copy is
  accepted (as `absent_from_copy`, reported by name) only when two things hold. The root's NOT_COPIED_OVER_50MB.txt
  must list it, meaning it was over 50 MB and so not pushed (owner's choice, relayed 2026-11-25). And the root's
  VERIFY.txt, the machine's own `campaign_run.py verify` on the full OUTROOT, must be exactly one line,
  "BROKEN: <path>/RESULT.json". Every other missing file, and any hash difference, is a failure.

  yield_lot2.py report OUTDIR ROOT [ROOT ...]     OUTDIR/INTEGRITY.json, and OUTDIR/YIELD.json only if every ROOT passes
"""
import hashlib
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import yield_lot as YL  # noqa: E402

POST_KEYS = ("core_budget", "remote_duplicates", "stopped_for_disk")


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def check_sums(sums):
    bad = []
    for line in sums.read_text().splitlines():
        h, n = line.split("  ", 1)
        f = sums.parent / n
        if not f.exists():
            bad.append(dict(file=n, why="missing"))
        elif sha(f) != h:
            bad.append(dict(file=n, why="hash differs"))
    return bad


def machine_verified(root):
    v = Path(root) / "VERIFY.txt"
    if not v.exists():
        return False
    lines = v.read_text().strip().splitlines()
    return len(lines) == 1 and lines[0].startswith("BROKEN: ") and lines[0].endswith("/RESULT.json") and "," not in lines[0]


def not_copied(root):
    f = Path(root) / "NOT_COPIED_OVER_50MB.txt"
    if not f.exists():
        return set()
    return {t.strip().lstrip("./") for line in f.read_text().splitlines() for t in line.replace("\t", " ").split(" ") if t.strip()}


def listed(sums, n, root, names):
    rel = str((sums.parent / n).relative_to(root))
    return rel in names or any(x.endswith("/" + rel) for x in names)


def check_root(root):
    root = Path(root)
    copy_ok = machine_verified(root)
    names = not_copied(root)
    res = dict(root=str(root), per_instance=[], top_level=[], known_defect=None, machine_verify_only_result_json=copy_ok,
               absent_from_copy=[])
    for sums in sorted(root.rglob("SHA256SUMS")):
        if sums.parent == root or "lean_build" in sums.parts:
            continue
        bad = check_sums(sums)
        if copy_ok:
            absent = [b for b in bad if b["why"] == "missing" and listed(sums, b["file"], root, names)]
            res["absent_from_copy"] += [str((sums.parent / b["file"]).relative_to(root)) for b in absent]
            bad = [b for b in bad if b not in absent]
        res["per_instance"].append(dict(sums=str(sums.relative_to(root)), lines=len(sums.read_text().splitlines()),
                                        failed=bad))
    top = root / "SHA256SUMS"
    if not top.exists():
        res["top_level"].append(dict(file="SHA256SUMS", why="missing"))
    else:
        for line in top.read_text().splitlines():
            h, n = line.split("  ", 1)
            f = root / n
            if not f.exists():
                res["top_level"].append(dict(file=n, why="missing"))
            elif sha(f) != h:
                if n == "RESULT.json":
                    r = json.loads(f.read_text())
                    removed = {k: r.pop(k) for k in POST_KEYS if k in r}
                    again = hashlib.sha256((json.dumps(r, indent=1, sort_keys=True) + "\n").encode()).hexdigest()
                    if again == h:
                        res["known_defect"] = dict(file=n, recorded=h, present=sha(f), keys_removed=sorted(removed),
                                                   matches_without_them=True)
                        continue
                res["top_level"].append(dict(file=n, why="hash differs"))
    res["ok"] = not res["top_level"] and all(not x["failed"] for x in res["per_instance"]) and bool(res["per_instance"])
    return res


if __name__ == "__main__":
    c, *a = sys.argv[1:] or ["help"]
    if c != "report" or len(a) < 2:
        sys.exit(__doc__)
    outdir, *roots = a
    Path(outdir).mkdir(parents=True, exist_ok=True)
    checks = [check_root(r) for r in roots]
    ok = all(x["ok"] for x in checks)
    (Path(outdir) / "INTEGRITY.json").write_bytes(YL.canon(dict(ok=ok, roots=checks)))
    print(json.dumps([dict(root=x["root"], ok=x["ok"], per_instance_lines=sum(p["lines"] for p in x["per_instance"]),
                           failed=sum(len(p["failed"]) for p in x["per_instance"]) + len(x["top_level"]),
                           absent_from_copy=len(x["absent_from_copy"]), known_defect=bool(x["known_defect"])) for x in checks], indent=1))
    if not ok:
        sys.exit("refused: integrity check failed; YIELD.json not written")
    r = YL.report(roots)
    (Path(outdir) / "YIELD.json").write_bytes(YL.canon(r))
    print(json.dumps({g: (v["eligible_K0"]["k"], v["room_K3"]["k"], v["n"]) for g, v in r.items()}))
