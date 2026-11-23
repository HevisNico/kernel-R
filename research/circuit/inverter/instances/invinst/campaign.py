"""The inverter campaign's one entry: a seed list in, one record per instance out, for the layered network's stage D.

  python -m invinst.campaign OUTDIR --seeds 9711,9712        (or --seeds-file FILE, one seed per line, # comments)
                                    [--config config.json] [--netopts config_netopts.json]

Steps, all in OUTDIR:
  1. JOBS: the seeds, one per line, in the given order (driver2's input).
  2. CAMPAIGN_INPUT.json: the seeds, the sha256 of the configs, of this package's code and Lean files and of the
     single-source gate, the ngspice version line and the git HEAD.
  3. driver2 (invinst/driver2.py, unchanged): each seed measured at the network's directives (config_netopts.json,
     design C5 of config.json) and gated at K0, K3 and StateBound; `max_jobs` (4) at a time, each under
     `job_timeout_s` (1800 s), both from config.json. No stopping rule: every seed is run, and a failed or timed-out
     job is counted under its first failing clause, never dropped and never re-run.
  4. INVERTERS.json (the file stage D reads) and records/INVERTER_<seed>.json (the same record, one per file).
  5. SHA256SUMS: every file in OUTDIR except lean_build/ (build products) and SHA256SUMS itself.

From Python (the network pipeline):
  from invinst import campaign
  campaign.run([9711, 9712], outdir)          # steps 1-5; returns the path of INVERTERS.json
  recs = campaign.load(outdir)                # checks SHA256SUMS, returns {seed: record}
The record fields are listed in CAMPAIGN_INTERFACE.md.
"""
import argparse, hashlib, json, subprocess, sys
from pathlib import Path

from . import sim
from .gate import OPEN_PREMISES

PKG = Path(__file__).resolve().parents[1]
REPO = PKG.parents[3]
SCHEMA = "inverter-campaign/1"
PREMISE_ORDER = ("Order", "SilenceBefore", "SilenceAfter", "FiringBefore", "FiringAfter", "Timing")
CODE = sorted(str(p.relative_to(PKG)) for p in list((PKG / "invinst").glob("*.py")) + list((PKG / "lean").glob("*"))
              if p.is_file())
GATE_SOURCE = REPO / "research" / "circuit" / "lean" / "CircuitInverterGate.lean"


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read_seeds(text):
    return [int(t) for l in text.splitlines() for t in l.split("#")[0].replace(",", " ").split()]


def first_failing(status, gate, kernel_level):
    """The first clause that fails for the K0 (eligibility) or K3 (room) verdict, None if none fails."""
    if status != "ok":
        return "run_" + status                          # run_failed, run_timeout
    if gate is None:
        return "run_no_gate"
    if not gate.get("measured"):
        return "not_measured"
    for k, v in sorted(gate["observed"].items()):
        if not v:
            return "observed:" + k                      # fired_absent, same_sample, silent_present
    sb = gate["state_bound"]
    if not isinstance(sb, dict):
        return "StateBound:not_measured"
    if not sb["verdict"]:
        return "StateBound"
    if gate["kernel"] is None:
        return "kernel:no_verdict"
    if not gate["kernel"][kernel_level]:
        m = gate.get("mirror", {}).get(kernel_level, {})
        bad = [p for p in PREMISE_ORDER if m.get(p) is False]
        return "kernel:" + (bad[0] if bad else "Premises")
    if isinstance(gate.get("front_end_fits"), dict) and not gate["front_end_fits"]["verdict"]:
        return "FrontEndFits"
    return None


def record(out, seed, status):
    gp = out / "gates" / f"GATE_{seed}.json"
    mp = out / "runs" / str(seed) / "MEASURE.json"
    g = json.loads(gp.read_text()) if (status == "ok" and gp.exists()) else None
    m = json.loads(mp.read_text()) if (status == "ok" and mp.exists()) else None
    f0, f3 = first_failing(status, g, "K0"), first_failing(status, g, "K3")
    r = dict(seed=seed, status=status, eligible_K0=f0 is None, room_K3=f0 is None and f3 is None,
             first_failing_K0=f0, first_failing_K3=f3, gate_eligible_K0=None, gate_room_K3=None)
    if g is not None:
        att = [a for a in g["attempts"] if a["passed"]]
        lean = out / "gates" / att[0]["file"] if att else None
        r.update(gate_eligible_K0=g["eligible_K0"], gate_room_K3=g["room_K3"], kernel=g["kernel"],
                 kernel_agrees_with_mirror=g.get("kernel_agrees_with_mirror"), observed=g["observed"],
                 state_bound=g["state_bound"], margins=g["margins"], measures=g["measures"],
                 allowance=g["allowance"], timing=g["timing"], front_end_fits=g["front_end_fits"],
                 files=dict(gate=str(gp.relative_to(out)), measure=str(mp.relative_to(out)),
                            lean=str(lean.relative_to(out)) if lean else None),
                 sha256=dict(gate=sha256(gp), measure=sha256(mp), lean=sha256(lean) if lean else None))
    if m is not None:
        x = m["measures"]
        r.update(fingerprint=dict(names=list(sim.FINGER), values=m["runs"]["R1_absent"]["finger"]),
                 machine_s=x["machine_s_total"],
                 values={n: x[n] for n in ("delta", "etaH", "etaM", "etaJ", "eps0", "Q", "emit_absent_tu",
                                           "latch_delay_tu", "same_sample")}
                 | dict(leak_above=x["leak_above"]["rate"], leak_below=x["leak_below"]["rate"]))
    # the campaign's verdicts must never be looser than the gate's own
    assert not (r["eligible_K0"] and not r["gate_eligible_K0"]) and not (r["room_K3"] and not r["gate_room_K3"])
    return r


def write_sums(out):
    files = sorted(p for p in out.rglob("*") if p.is_file() and p.name != "SHA256SUMS"
                   and "lean_build" not in p.relative_to(out).parts)
    (out / "SHA256SUMS").write_text("".join(f"{sha256(p)}  {p.relative_to(out)}\n" for p in files))
    return len(files)


def run(seeds, outdir, config=None, netopts=None):
    out = Path(outdir).resolve()
    out.mkdir(parents=True, exist_ok=True)
    seeds = [int(s) for s in seeds]
    assert len(set(seeds)) == len(seeds), "a seed is listed twice"
    cfg_p = Path(config or PKG / "config.json").resolve()
    net_p = Path(netopts or PKG / "config_netopts.json").resolve()
    (out / "JOBS").write_text("".join(f"{s}\n" for s in seeds))
    ng = subprocess.run(["ngspice", "-v"], capture_output=True, text=True).stdout
    head = subprocess.run(["git", "-C", str(PKG), "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
    dirty = subprocess.run(["git", "-C", str(PKG), "status", "--porcelain", "--", "."], capture_output=True,
                           text=True).stdout.strip()
    inp = dict(schema=SCHEMA, seeds=seeds, config=dict(path=str(cfg_p), sha256=sha256(cfg_p)),
               netopts=dict(path=str(net_p), sha256=sha256(net_p)),
               code={p: sha256(PKG / p) for p in CODE}, gate_source=sha256(GATE_SOURCE),
               ngspice=next((l.strip("* ").strip() for l in ng.splitlines() if "ngspice-" in l), None),
               git_head=head, package_tree_clean=not dirty)
    (out / "CAMPAIGN_INPUT.json").write_text(json.dumps(inp, indent=1, sort_keys=True))
    cmd = [sys.executable, "-m", "invinst.driver2", str(out / "JOBS"), str(out), "--config", str(cfg_p),
           "--netopts", str(net_p)]
    p = subprocess.run(cmd, cwd=PKG, capture_output=True, text=True)
    (out / "driver2.log").write_text(p.stdout + p.stderr)
    if p.returncode:
        raise RuntimeError("driver2 failed (rc %d), see %s" % (p.returncode, out / "driver2.log"))
    summ = json.loads((out / "SUMMARY.json").read_text())
    status = {r["seed"]: r["status"] for r in summ["rows"]}
    recs = [record(out, s, status.get(s, "missing")) for s in seeds]
    (out / "records").mkdir(exist_ok=True)
    for r in recs:
        (out / "records" / f"INVERTER_{r['seed']}.json").write_text(json.dumps(r, indent=1, sort_keys=True))
    doc = dict(schema=SCHEMA, verdict_status="conditional on open_premises", open_premises=OPEN_PREMISES,
               input="CAMPAIGN_INPUT.json", input_sha256=sha256(out / "CAMPAIGN_INPUT.json"),
               n=len(recs), n_ok=sum(r["status"] == "ok" for r in recs),
               k_eligible_K0=sum(r["eligible_K0"] for r in recs), k_room_K3=sum(r["room_K3"] for r in recs),
               machine_minutes_jobs=summ["machine_minutes_jobs"], wall_minutes=summ["wall_minutes"],
               records=recs)
    (out / "INVERTERS.json").write_text(json.dumps(doc, indent=1, sort_keys=True))
    write_sums(out)
    return out / "INVERTERS.json"


def load(outdir, verify=True):
    """{seed: record} from OUTDIR/INVERTERS.json; with verify, every SHA256SUMS line is checked first."""
    out = Path(outdir)
    if verify:
        for line in (out / "SHA256SUMS").read_text().splitlines():
            h, name = line.split("  ", 1)
            if sha256(out / name) != h:
                raise ValueError(f"checksum mismatch: {name}")
    doc = json.loads((out / "INVERTERS.json").read_text())
    if doc["schema"] != SCHEMA:
        raise ValueError(f"schema {doc['schema']!r}, expected {SCHEMA!r}")
    return {r["seed"]: r for r in doc["records"]}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("outdir")
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--seeds", help="comma-separated seeds")
    g.add_argument("--seeds-file")
    ap.add_argument("--config")
    ap.add_argument("--netopts")
    a = ap.parse_args()
    seeds = read_seeds(a.seeds if a.seeds else Path(a.seeds_file).read_text())
    path = run(seeds, a.outdir, a.config, a.netopts)
    doc = json.loads(path.read_text())
    print(json.dumps({k: v for k, v in doc.items() if k not in ("records", "open_premises")}, indent=1))


if __name__ == "__main__":
    main()
