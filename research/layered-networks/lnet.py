"""The one driver of the layered-network package (development only, nothing preregistered).

  lnet.py deck    SPEC OUT                 write the SPICE deck of a spec (no simulation) and its size
  lnet.py run     SPEC OUT SEED            simulate one instance: train layer by layer, test every pattern (record.json)
  lnet.py measure SPEC OUT                 the chain quantities and the Python checks (measure.json)
  lnet.py lean    SPEC OUT                 emit OUT/Dev<TAG>.lean and check it with decide +kernel (lean.json)
  lnet.py job     SPEC OUT SEED            run, measure and lean in a row (one batch job)
  lnet.py batch   JOBS OUT                 the jobs of a JOBS file, at most config batch.parallel at a time, each with
                                           config batch.timeout_s; one status file per job (OUT/<name>.status)

A JOBS line: NAME SPEC SEED (blank lines and lines starting with # are skipped). Paths relative to the JOBS file.
Seeds of development instances: 9801 to 9803, outside every campaign range.
"""
import json
from pathlib import Path
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import deck as deckmod  # noqa: E402
import spec as specmod  # noqa: E402

CFG = json.loads((HERE / "config.json").read_text())


def cmd_deck(spec_path, out):
    s = specmod.load(spec_path)
    out = Path(out)
    out.mkdir(parents=True, exist_ok=True)
    text = deckmod.build(s, CFG)
    (out / "input.spice").write_text(text)
    print(json.dumps(dict(tag=s["tag"], **deckmod.size(text)), indent=1))


def cmd_run(spec_path, out, seed):
    import run
    r = run.train_and_test(specmod.load(spec_path), CFG, out, int(seed))
    print(json.dumps(dict(status=r["status"], cost=r["cost"], deck=r["deck"], words=r["words"]), indent=1))
    return r["status"] == "done"


def cmd_measure(spec_path, out):
    import measure
    measure.main(spec_path, out)


def cmd_lean(spec_path, out):
    import lean
    import measure
    out = Path(out)
    s = specmod.load(spec_path)
    rec = json.loads((out / "record.json").read_text())
    m = measure.Measure(s, CFG, rec)
    rep, dmin, dmax, lessons, maxw = m.report()
    path = out / f"Dev{s['tag']}.lean"
    path.write_text(lean.emit(m, dmin, dmax, lessons, maxw))
    build = HERE / "build"
    t0 = time.time()
    lean.build_modules(CFG, build)
    res = dict(file=path.name, modules_s=round(time.time() - t0, 1), **lean.check(CFG, path, build))
    (out / "lean.json").write_text(json.dumps(res, indent=1) + "\n")
    print(json.dumps({k: v for k, v in res.items() if k != "output" or not res["accepted"]}, indent=1))
    return res["accepted"]


def cmd_job(spec_path, out, seed):
    ok = cmd_run(spec_path, out, seed)
    cmd_measure(spec_path, out)
    return cmd_lean(spec_path, out) and ok


def cmd_batch(jobs, out):
    jobs, out = Path(jobs), Path(out)
    out.mkdir(parents=True, exist_ok=True)
    todo = []
    for l in jobs.read_text().splitlines():
        if l.strip() and not l.lstrip().startswith("#"):
            name, sp, seed = l.split()
            todo.append((name, (jobs.parent / sp).resolve(), int(seed)))
    par, limit = CFG["batch"]["parallel"], CFG["batch"]["timeout_s"]
    running = {}

    def status(name, **kw):
        (out / f"{name}.status").write_text(json.dumps(dict(name=name, **kw), indent=1) + "\n")

    for name, sp, seed in todo:
        status(name, state="queued", spec=str(sp), seed=seed)
    while todo or running:
        while todo and len(running) < par:
            name, sp, seed = todo.pop(0)
            log = (out / f"{name}.log").open("w")
            p = subprocess.Popen([sys.executable, str(HERE / "lnet.py"), "job", str(sp), str(out / name), str(seed)],
                                 stdout=log, stderr=subprocess.STDOUT)
            running[name] = (p, time.time(), log, sp, seed)
            status(name, state="running", spec=str(sp), seed=seed, pid=p.pid, started=time.time())
        time.sleep(2)
        for name in list(running):
            p, t0, log, sp, seed = running[name]
            rc = p.poll()
            if rc is None and time.time() - t0 > limit:
                p.kill()
                rc = "timeout"
            if rc is not None:
                log.close()
                del running[name]
                status(name, state="done" if rc == 0 else ("timeout" if rc == "timeout" else "failed"), returncode=rc,
                       spec=str(sp), seed=seed, wall_s=round(time.time() - t0, 1))


if __name__ == "__main__":
    a = sys.argv[1:]
    f = dict(deck=cmd_deck, run=cmd_run, measure=cmd_measure, lean=cmd_lean, job=cmd_job, batch=cmd_batch)[a[0]]
    r = f(*a[1:])
    sys.exit(0 if r in (None, True) else 1)
