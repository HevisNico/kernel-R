"""The one driver: measure and gate a list of instances, at most `max_jobs` at a time, each under a timeout.

  python -m invinst.driver JOBS OUTDIR [--config config.json] [--section tt]
      JOBS: one seed per line (# comments allowed). Each job is `python -m invinst.driver --job SEED OUTDIR`,
      run in its own process under `job_timeout_s`; its status is OUTDIR/status/SEED.{ok,failed,timeout}.
      A failed or timed-out job is kept and counted, never retried here.
      --stop RULE.json: the stopping rule (DEV_LOT_RULE.md): after `check_after` finished jobs, if the eligible
      count is below `min_eligible`, no new job is started; nor once the jobs' summed wall time reaches
      `max_machine_minutes` (a job already running finishes).
  Writes OUTDIR/SUMMARY.json: counts (k eligible out of n, k with room out of n), machine-minutes, per-seed rows.
"""
import argparse, json, os, subprocess, sys, time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

PKG = Path(__file__).resolve().parents[1]


def load_config(path=None):
    return json.loads(Path(path or PKG / "config.json").read_text())


def one_job(seed, outdir, cfg, section, build):
    from . import measure, gate
    meas = measure.measure(cfg, seed, Path(outdir) / "runs", section=section)
    res = gate.gate(cfg, meas, Path(outdir) / "gates", build)
    return meas, res


def regate(cfg, seeds, runs, out, build):
    """Gate again the instances of `runs` from their MEASURE.json, adding the state bound from the kept traces."""
    from . import measure, gate
    build_library(build)
    rows = []
    for seed in seeds:
        meas = json.loads((runs / str(seed) / "MEASURE.json").read_text())
        x = meas["measures"]
        if "state_extent" not in x:
            x["state_extent"] = measure.state_extent(cfg, runs / str(seed),
                                                     (x["leak_above"]["rate"] + x["leak_below"]["rate"]) / 2)
        g = gate.gate(cfg, meas, out / "gates", build)
        rows.append(dict(seed=seed, eligible_K0=g["eligible_K0"], room_K3=g["room_K3"], kernel=g["kernel"],
                         kernel_agrees_with_mirror=g.get("kernel_agrees_with_mirror"), state_bound=g["state_bound"],
                         failing={K: [p for p, v in g.get("mirror", {}).get(K, {}).items() if not v] for K in ("K0", "K3")},
                         margins=g.get("margins"), state_extent=x["state_extent"]))
    summary = dict(verdict_status="conditional on open_premises", open_premises=gate.OPEN_PREMISES,
                   regated_from=str(runs), n=len(rows), k_eligible_K0=sum(r["eligible_K0"] for r in rows),
                   k_room_K3=sum(r["room_K3"] for r in rows), rows=rows)
    (out / "REGATE_SUMMARY.json").write_text(json.dumps(summary, indent=1, sort_keys=True))
    print(json.dumps({k: v for k, v in summary.items() if k != "rows"}, indent=1))


def build_library(build):
    Path(build).mkdir(parents=True, exist_ok=True)
    p = subprocess.run(["bash", str(PKG / "lean" / "check.sh")], env=dict(os.environ, GATE_BUILD=str(build)),
                       capture_output=True, text=True, timeout=3600)
    if p.returncode:
        raise RuntimeError(p.stdout + p.stderr)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("jobs")
    ap.add_argument("outdir")
    ap.add_argument("--config")
    ap.add_argument("--section")
    ap.add_argument("--stop")
    ap.add_argument("--job", action="store_true")
    ap.add_argument("--regate", help="RUNS dir of finished instances: re-gate them from their measures and kept "
                                     "traces (no simulation); JOBS lists the seeds, OUTDIR receives the new gates")
    a = ap.parse_args()
    cfg = load_config(a.config)
    out = Path(a.outdir)
    build = out / "lean_build"
    if a.job:
        one_job(int(a.jobs), out, cfg, a.section, build)
        return
    seeds = [int(l.split("#")[0]) for l in Path(a.jobs).read_text().splitlines() if l.split("#")[0].strip()]
    if a.regate:
        regate(cfg, seeds, Path(a.regate), out, build)
        return
    rule = json.loads(Path(a.stop).read_text()) if a.stop else None
    (out / "status").mkdir(parents=True, exist_ok=True)
    build_library(build)
    dcfg = cfg["driver"]
    state = dict(done=0, eligible=0, stopped=False, why=None, machine_s=0.0)
    t0 = time.time()

    def job(seed):
        if state["stopped"]:
            return seed, "not_started", 0.0
        cmd = [sys.executable, "-m", "invinst.driver", "--job", str(seed), str(out)]
        cmd += ["--config", a.config] if a.config else []
        cmd += ["--section", a.section] if a.section else []
        s = time.time()
        try:
            p = subprocess.run(cmd, cwd=PKG, capture_output=True, text=True, timeout=dcfg["job_timeout_s"])
            status = "ok" if p.returncode == 0 else "failed"
            log = p.stdout + p.stderr
        except subprocess.TimeoutExpired as e:
            status, log = "timeout", str(e)
        (out / "status" / f"{seed}.{status}").write_text(log[-5000:])
        g = out / "gates" / f"GATE_{seed}.json"
        ok = status == "ok" and g.exists() and json.loads(g.read_text())["eligible_K0"]
        state["done"] += 1
        state["eligible"] += int(ok)
        state["machine_s"] += time.time() - s
        if rule and not state["stopped"]:
            if state["done"] >= rule["check_after"] and state["eligible"] < rule["min_eligible"]:
                state["stopped"], state["why"] = True, f"{state['eligible']} eligible after {state['done']}"
            elif state["machine_s"] >= 60 * rule["max_machine_minutes"]:
                state["stopped"], state["why"] = True, "compute ceiling reached"
        return seed, status, time.time() - s

    with ThreadPoolExecutor(max_workers=dcfg["max_jobs"]) as ex:
        results = list(ex.map(job, seeds))
    rows = []
    for seed, status, wall in results:
        g = out / "gates" / f"GATE_{seed}.json"
        mpath = out / "runs" / str(seed) / "MEASURE.json"
        row = dict(seed=seed, status=status, job_wall_s=wall)
        if g.exists() and status == "ok":
            gr = json.loads(g.read_text())
            mm = json.loads(mpath.read_text())["measures"]
            row.update(eligible_K0=gr["eligible_K0"], room_K3=gr["room_K3"], kernel=gr["kernel"],
                       failing={K: [p for p, v in gr.get("mirror", {}).get(K, {}).items() if not v] for K in ("K0", "K3")},
                       margins=gr.get("margins"), machine_s=mm["machine_s_total"],
                       values={n: mm[n] for n in ("delta", "etaH", "etaM", "etaJ", "eps0", "Q", "emit_absent_tu",
                                                  "latch_delay_tu", "same_sample")}
                       | dict(leak_above=mm["leak_above"]["rate"], leak_below=mm["leak_below"]["rate"]))
        rows.append(row)
    run = [r for r in rows if r["status"] != "not_started"]
    from .gate import OPEN_PREMISES
    summary = dict(verdict_status="conditional on open_premises", open_premises=OPEN_PREMISES, n_started=len(run), n_ok=sum(r["status"] == "ok" for r in run),
                   k_eligible_K0=sum(bool(r.get("eligible_K0")) for r in run),
                   k_room_K3=sum(bool(r.get("room_K3")) for r in run),
                   stopped_by_rule=state["stopped"], stop_reason=state["why"], rule=rule,
                   machine_minutes_jobs=sum(r["job_wall_s"] for r in run) / 60, wall_minutes=(time.time() - t0) / 60,
                   rows=rows)
    (out / "SUMMARY.json").write_text(json.dumps(summary, indent=1, sort_keys=True))
    print(json.dumps({k: v for k, v in summary.items() if k != "rows"}, indent=1))


if __name__ == "__main__":
    main()
