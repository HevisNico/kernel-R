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
    a = ap.parse_args()
    cfg = load_config(a.config)
    out = Path(a.outdir)
    build = out / "lean_build"
    if a.job:
        one_job(int(a.jobs), out, cfg, a.section, build)
        return
    seeds = [int(l.split("#")[0]) for l in Path(a.jobs).read_text().splitlines() if l.split("#")[0].strip()]
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
    summary = dict(n_started=len(run), n_ok=sum(r["status"] == "ok" for r in run),
                   k_eligible_K0=sum(bool(r.get("eligible_K0")) for r in run),
                   k_room_K3=sum(bool(r.get("room_K3")) for r in run),
                   stopped_by_rule=state["stopped"], stop_reason=state["why"], rule=rule,
                   machine_minutes_jobs=sum(r["job_wall_s"] for r in run) / 60, wall_minutes=(time.time() - t0) / 60,
                   rows=rows)
    (out / "SUMMARY.json").write_text(json.dumps(summary, indent=1, sort_keys=True))
    print(json.dumps({k: v for k, v in summary.items() if k != "rows"}, indent=1))


if __name__ == "__main__":
    main()
