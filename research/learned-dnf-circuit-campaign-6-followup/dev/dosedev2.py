"""Development only: the measures and the network runs of the nominal cell with the dose window rewritten.

Not campaign code. It edits no file of the repository and writes nothing inside it. Nominal cell only (no seed).

How it works: the frozen functions are called unchanged; only `net.deck`, the one function that writes a deck's text,
is wrapped for the time of the call, so that the `.param` line of the text is rewritten (dosedev.rewrite). With no
parameter the wrapper returns the frozen text, byte for byte (test_dosedev2.py).

  dosedev2.py caloff REPO OUT NGSPICE PDK [NAME=VALUE ...]
        the guard-off calibration deck: batch6.cal(out, None, "off", ...), frozen
  dosedev2.py scan   REPO OUT CELL KIND ARGS... NGSPICE PDK -- [NAME=VALUE ...]
        one scan, both-lines check or one-sided set: scan6.main([OUT, "none", CELL, KIND, ARGS..., NGSPICE, PDK]), frozen
        KIND pair | line1 | line2: ARGS = DELTA D1_V D2_V;  bothfire: D1_V D2_V;  onesided: S1 S2 D1_V D2_V
  dosedev2.py bound  REPO S_MAX SA HA SB HB
        the one-sided bound of a and b, in stages, with the mapping's "8" as the parameter S_MAX
  dosedev2.py net    REPO OUT ID NEEDS CONTROL NOISE NOISE_SEED SEEDS_FILE NGSPICE PDK [NAME=VALUE ...]
        one network run, as net6.network without its campaign guards: NEEDS a,b,c1,c2; CONTROL skew | none;
        NOISE none (NOISE_SEED 0) | injected (NOISE_SEED one of the declared development seeds of SEEDS_FILE)
  dosedev2.py many   JOBS.json
        the runs of JOBS.json, at most four at a time, each under its own time limit, in waves

Only vhi and vlo may be changed here (the window): cs0 and idis also enter the write gate, which this file leaves to
the frozen code.
"""
import contextlib
import hashlib
import json
from pathlib import Path
import resource
import subprocess
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
import dosedev                                             # noqa: E402

WINDOW_ONLY = ("vhi", "vlo")
JOBS_AT_A_TIME = 4


def parse(pairs):
    params = dosedev.parse(pairs)
    assert set(params) <= set(WINDOW_ONLY), f"refused: only {WINDOW_ONLY} may be changed for the measures and the network runs"
    return params


def repo_paths(repo):
    dosedev.repo_paths(repo)
    r = Path(repo).resolve() / "research" / "learned-dnf-circuit-campaign-6"
    for p in (r / "batch", r / "campaign6"):
        sys.path.insert(0, str(p))


@contextlib.contextmanager
def window(params, seen=None):
    """For the time of the block, net.deck returns its own text with the parameters rewritten. `seen` collects, per
    call, the SHA-256 of the frozen text and of the text returned."""
    import net
    frozen = net.deck

    def deck(*a, **k):
        original = frozen(*a, **k)
        text, changed = dosedev.rewrite(original, params)
        if seen is not None:
            seen.append(dict(frozen_sha256=hashlib.sha256(original.encode()).hexdigest(), as_run_sha256=hashlib.sha256(text.encode()).hexdigest(),
                             parameters_changed=changed, arguments=dict(cells=list(k.get("cells", a[0] if a else ())), **{x: k[x] for x in k if x != "cells"})))
        return text
    net.deck = deck
    try:
        yield
    finally:
        net.deck = frozen


def sidecar(out, what, seen, extra=None):
    """What this development run changed, beside the frozen record: DOSEDEV.json in the run's folder."""
    Path(out, "DOSEDEV.json").write_text(json.dumps(dict(what=what, development_run="nominal cell, outside any campaign", decks=seen, **(extra or {})), indent=1) + "\n")


def outside(repo, out):
    assert Path(repo).resolve() not in Path(out).resolve().parents, "refused: the run's folder is inside the repository"


def caloff(repo, out, ngspice, pdk, params):
    assert __debug__, "refused: not with python -O, the guards are asserts"
    repo_paths(repo)
    outside(repo, out)
    import batch6
    import c4
    print(c4.require_pinned())
    seen = []
    with window(params, seen):
        rec = batch6.cal(Path(out), None, "off", Path(ngspice), Path(pdk))
    sidecar(out, "guard-off calibration deck (batch6.cal, frozen)", seen)
    return rec


def scan(repo, out, argv, params):
    """argv: CELL KIND ARGS... NGSPICE PDK, as scan6.main takes them after OUT and the seed."""
    assert __debug__, "refused: not with python -O, the guards are asserts"
    repo_paths(repo)
    outside(repo, out)
    import scan6
    assert argv[1] in ("pair", "line1", "line2", "bothfire", "onesided"), f"refused: kind {argv[1]}"
    seen = []
    with window(params, seen):
        rec = scan6.main([str(out), "none", *argv])
    sidecar(out, f"{argv[1]} of {argv[0]} (scan6.main, frozen)", seen)
    return rec


def bound(s_max, S, h):
    """predict6.layer1_bounds with its 8 as a parameter: K = max over a, b of max(s_max - s*_x, s*_x); W_x = s*_x + K;
    the bound is W_x + h_x, in stages. S, h: {a, b: Fraction}."""
    K = max(max(s_max - S[x], S[x]) for x in ("a", "b"))
    return {x: S[x] + K + h[x] for x in ("a", "b")}


def declared_seeds(path):
    """The development noise seeds of NOISE_SEEDS_DEV.txt: {seed: dose label}. Lines `SEED LABEL`; `#` starts a comment."""
    out = {}
    for line in Path(path).read_text().splitlines():
        line = line.split("#")[0].strip()
        if line:
            seed, label = line.split()
            assert int(seed) not in out, f"seed {seed} listed twice"
            out[int(seed)] = label
    return out


def network(repo, out, rid, needs, control, noise, noise_seed, seeds_file, ngspice, pdk, params):
    """net6.network without the campaign's stage file and seed guard: the same frozen functions, in the same order
    (plans4.network, noisemodel.shim, net.deck, session4.play, run4.trnoise_fingerprint), on the nominal cell."""
    assert __debug__, "refused: not with python -O, the guards are asserts"
    repo_paths(repo)
    outside(repo, out)
    import c4
    import noisemodel
    import plans4
    import run4
    import session4
    from session4 import net
    print(c4.require_pinned())
    began = time.time()
    out = Path(out)
    assert noise in ("none", "injected"), "refused: the injected model only"
    assert control in (None, "skew"), "refused: control is skew or none"
    assert len(needs) == 4 and all(isinstance(n, int) and 1 <= n <= 7 for n in needs), needs
    rec = dict(id=rid, kind="network", section="tt", seed=None, stage=None)
    plan, slots = plans4.network(tuple(needs), control)
    noise_id, shim, seen = None, None, []
    with window(params, seen):
        text = net.deck(cells=c4.CELLS, section="tt", noise=True) if noise == "injected" else net.deck(cells=c4.CELLS, section="tt")
    changed = {k: v for k, v in seen[0]["parameters_changed"].items() if v["old"] != v["new"]}
    assert changed in ({}, dict(vhi=dict(old="0.6", new="0.7"))), f"refused: the network runs are for 1x (no change) and 2x (vhi 0.6 -> 0.7), not {changed}"
    label = "2x" if changed else "1x"
    if noise == "injected":
        declared = declared_seeds(seeds_file)
        assert noise_seed in declared, f"refused: {noise_seed} is not a declared development noise seed"
        assert declared[noise_seed] == label, f"refused: seed {noise_seed} is declared for {declared[noise_seed]}, this deck is {label}"
        used = Path(seeds_file).with_name("NOISE_SEEDS_USED")
        used.mkdir(exist_ok=True)
        try:                                                 # one file per seed, created exclusively: a seed is used once, even
            with open(used / str(noise_seed), "x") as f:     # by two runs started together, and even if its run then fails
                f.write(rid + "\n")
        except FileExistsError:
            raise AssertionError(f"refused: noise seed {noise_seed} was already used by {(used / str(noise_seed)).read_text().strip()}")
        out.mkdir(parents=True, exist_ok=True)
        shim, shim_info = noisemodel.shim(out)
        noise_id = noise_seed
        info = dict(model="injected", noise_seed=noise_id, imposed_process_number=noise_id, shim=shim_info)
    else:
        assert noise_seed == 0, "a run without noise has no noise seed"
        info = dict(model="none")
    rec.update(needs=list(needs), control=control, round=None, slots=len(slots))
    result, tr = session4.play(out / "evidence", plan, text, Path(ngspice), Path(pdk), seed=None, guard_off=False, noise_id=noise_id, shim=shim)
    (out / "evidence" / "pdk").unlink()
    reached = bool(tr.t[-1] >= result["horizon_s"] - 1e-9)
    mark = run4.trnoise_fingerprint(tr, c4.CELLS)
    if shim is not None:
        Path(shim).unlink()
    ev = out / "evidence"
    rec.update(noise=info, reached_its_last_date=reached, horizon_s=result["horizon_s"], waveform_ends_s=result["waveform_ends_s"],
               points=result["points"], files={x: run4.sha(ev / x) for x in ("input.spice", "session.log", "trace.raw", "result.json")})
    rec.update(noise_fingerprint=mark, wall_s=time.time() - began, peak_rss_MB=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss / 1024)
    rec["dosedev"] = dict(what="development network run on the nominal cell, outside any campaign", dose=label, decks=seen, interpreter=c4.interpreter())
    (out / "noise.sha256").write_text(mark + "\n")
    (out / "record.json").write_text(json.dumps(rec, indent=1) + "\n")
    assert reached, "the waveform ends before the last date of the run"
    return rec


def many(jobs_file):
    """JOBS.json: {"folder": DIR, "waves": [[{"id", "argv": [...], "limit_s"}, ...], ...]}. Each wave starts when the
    wave before it has ended; at most four runs at a time; each run under `timeout limit_s`, its output in
    DIR/<id>.log; DIR/STATE.json is rewritten at every start and end. A run that fails or is cut does not stop the
    others; the waves after it still start (a run that needs a failed one stops by itself on its missing input)."""
    spec = json.loads(Path(jobs_file).read_text())
    folder = Path(spec["folder"])
    folder.mkdir(parents=True, exist_ok=True)
    state = dict(started_utc=time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), runs={})

    def save():
        (folder / "STATE.json").write_text(json.dumps(state, indent=1) + "\n")
    for wave in spec["waves"]:
        todo, running = list(wave), {}
        while todo or running:
            while todo and len(running) < JOBS_AT_A_TIME:
                job = todo.pop(0)
                assert job["id"] not in state["runs"] and not (folder / job["id"]).exists(), f"refused: {job['id']} already exists"
                log = open(folder / f"{job['id']}.log", "w")
                p = subprocess.Popen(["timeout", str(job["limit_s"]), *job["argv"]], stdout=log, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL)
                running[job["id"]] = (p, log, time.time(), job)
                state["runs"][job["id"]] = dict(status="running", limit_s=job["limit_s"], argv=job["argv"])
                save()
            time.sleep(2)
            for rid, (p, log, t0, job) in list(running.items()):
                code = p.poll()
                if code is None:
                    continue
                log.close()
                wall = time.time() - t0
                status = "complete" if code == 0 else ("cut at its limit" if code == 124 else f"failed (exit {code})")
                state["runs"][rid].update(status=status, exit=code, wall_s=wall, share_of_limit=wall / job["limit_s"])
                del running[rid]
                save()
    state["ended_utc"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    save()
    print(json.dumps({k: v["status"] for k, v in state["runs"].items()}, indent=1))


if __name__ == "__main__":
    a = sys.argv[1:]
    if a and a[0] == "caloff":
        caloff(a[1], a[2], a[3], a[4], parse(a[5:]))
    elif a and a[0] == "scan":
        cut = a.index("--")
        scan(a[1], a[2], a[3:cut], parse(a[cut + 1:]))
    elif a and a[0] == "bound":
        from fractions import Fraction as F
        b = bound(F(a[2]), dict(a=F(a[3]), b=F(a[5])), dict(a=F(a[4]), b=F(a[6])))
        print(json.dumps({x: str(v) for x, v in b.items()}))
    elif a and a[0] == "net":
        network(a[1], a[2], a[3], [int(x) for x in a[4].split(",")], None if a[5] == "none" else a[5], a[6], int(a[7]), a[8], a[9], a[10], parse(a[11:]))
    elif a and a[0] == "many":
        many(a[1])
    else:
        raise SystemExit(__doc__)
