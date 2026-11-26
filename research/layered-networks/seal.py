"""The sealed prediction record of stage D (CAMPAIGN_PLAN_DRAFT.md §2 and §10 step 5). Development only.

  stage_d.py seal   SEALDIR OUT [OUT ...]    one file per instance, MANIFEST.json and SHA256SUMS, in a new folder
  stage_d.py verify SEALDIR                  every line of SHA256SUMS checked, and the manifest against the files

Byte for byte reproducible on a second machine: each instance file is stage_d.py's prediction.json as written
(canonical JSON: sorted keys, no spaces, ASCII, one trailing newline; exact rationals as strings), with no date, no
host, no path and no cost field. Its name is <TAG>_<seed>.json. MANIFEST.json lists the instances in (tag, seed) order
with each file's sha256 and its eligibility and room; SHA256SUMS is `sha256sum` format (two spaces), sorted by name,
over every instance file and MANIFEST.json, and is checkable with `sha256sum -c SHA256SUMS`. The seal refuses an
existing folder (a seal is written once) and an instance whose prediction.json is missing or not canonical.
"""
import hashlib
import json
from pathlib import Path

MANIFEST_FORMAT = "layered-stage-d-seal/1"


def sha(b):
    return hashlib.sha256(b).hexdigest()


def canon(obj):
    return (json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True) + "\n").encode()


def seal(sealdir, *outs):
    sealdir = Path(sealdir)
    if sealdir.exists():
        raise SystemExit(f"refused: {sealdir} exists (a seal is written once)")
    files = {}
    for o in outs:
        b = (Path(o) / "prediction.json").read_bytes()
        p = json.loads(b)
        assert canon(p) == b, f"{o}/prediction.json is not canonical"
        name = f"{p['tag']}_{p['seed']}.json"
        assert name not in files, f"two predictions for {name}"
        files[name] = (b, p)
    sealdir.mkdir(parents=True)
    rows = []
    for name in sorted(files, key=lambda n: (files[n][1]["tag"], files[n][1]["seed"])):
        b, p = files[name]
        (sealdir / name).write_bytes(b)
        rows.append(dict(file=name, sha256=sha(b), tag=p["tag"], seed=p["seed"], status=p["status"],
                         eligible_K0=p["eligible_K0"], room_K3=p["room_K3"], inverter_gate=p["inverter_gate"]["source"]))
    man = canon(dict(format=MANIFEST_FORMAT, instances=rows, count=len(rows),
                     eligible_K0=sum(r["eligible_K0"] for r in rows), room_K3=sum(r["room_K3"] for r in rows)))
    (sealdir / "MANIFEST.json").write_bytes(man)
    sums = sorted([(r["file"], r["sha256"]) for r in rows] + [("MANIFEST.json", sha(man))])
    (sealdir / "SHA256SUMS").write_text("".join(f"{h}  {n}\n" for n, h in sums))
    print(f"sealed {len(rows)} instance(s) in {sealdir}; SHA256SUMS sha256 {sha((sealdir / 'SHA256SUMS').read_bytes())}")
    return True


def verify(sealdir, quiet=False):
    """True when every SHA256SUMS line matches, no file is unlisted, and the manifest's hashes match its files."""
    sealdir = Path(sealdir)
    bad = []
    listed = {}
    for line in (sealdir / "SHA256SUMS").read_text().splitlines():
        h, n = line.split("  ", 1)
        listed[n] = h
        if not (sealdir / n).exists() or sha((sealdir / n).read_bytes()) != h:
            bad.append(f"{n}: hash differs or file missing")
    extra = sorted(p.name for p in sealdir.iterdir() if p.name not in listed and p.name != "SHA256SUMS")
    bad += [f"{n}: not listed" for n in extra]
    if "MANIFEST.json" in listed:
        man = json.loads((sealdir / "MANIFEST.json").read_bytes())
        for r in man["instances"]:
            if listed.get(r["file"]) != r["sha256"]:
                bad.append(f"{r['file']}: manifest hash differs")
    else:
        bad.append("MANIFEST.json: not listed")
    if not quiet:
        print("seal verified" if not bad else "SEAL BROKEN: " + "; ".join(bad))
    return not bad


def load(sealdir, tag, seed):
    """The sealed prediction of (tag, seed), after the seal is verified; None if the seal has no such instance."""
    if not verify(sealdir, quiet=True):
        raise SystemExit(f"refused: the seal {sealdir} does not verify")
    p = Path(sealdir) / f"{tag}_{seed}.json"
    return json.loads(p.read_bytes()) if p.exists() else None
