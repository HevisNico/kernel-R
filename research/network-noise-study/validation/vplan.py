"""Validation: the list of runs of PROTOCOL.md, run four at a time; a run whose result exists is not run again.

  vplan.py list          print the runs
  vplan.py env           the machine's environment (against the reference) and inventory
  vplan.py run WORK [FILTER]   run them (those whose name contains FILTER, or machine=1|2), results in WORK/<name>.json
                               or WORK/<name>/
"""
import re, subprocess, sys, time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

HERE = Path(__file__).resolve().parent
PY = "/home/user/owner-prep/venv312/bin/python"
DEV = ("7101", "7102", "7103")


def runs():
    R = []
    # V8
    for i in DEV:
        R += [("seeding", f"v8_{i}_r3", i, "3"), ("seeding", f"v8_{i}_r4", i, "4"), ("seeding", f"v8_{i}_r3again", i, "3"),
              ("seeding", f"v8_{i}_quiet", i, "quiet")]
    # V3/V4 hold
    R += [("frozen", f"v3_nominal_hold_r{r}", "nominal", "hold", "a", "1", "0.08", str(r), "model") for r in range(1, 33)]
    for i in DEV:
        R += [("frozen", f"v3_{i}_hold_r{r}", i, "hold", "all", "-", "0.08", str(r), "model") for r in range(5, 13)]
    # V3 window, fire, pulse
    outs = {"nominal": [("window", "a", "1"), ("fire", "a", "-"), ("pulse", "a", "1")]}
    for i in DEV:
        outs[i] = [("window", "a", "1"), ("window", "b", "2"), ("fire", "a", "-"), ("fire", "b", "-"), ("pulse", "a", "1"),
                   ("pulse", "b", "2")]
    for i, first in (("nominal", 33),) + tuple((i, 13) for i in DEV):
        r = first
        for st, c, p in outs[i]:
            for _ in range(8):
                R.append(("frozen", f"v3_{i}_{st}_{c}{p.strip('-')}_r{r}", i, st, c, p, "0.02", str(r), "model"))
                r += 1
    # V6
    for i, first in (("nominal", 57),) + tuple((i, 61) for i in DEV):
        R.append(("preset", f"v6_{i}_zero", i, "zero"))
        R += [("preset", f"v6_{i}_r{r}", i, str(r)) for r in range(first, first + 32)]
    # V7 and section 3
    for i in DEV:
        R += [("train", f"tr_{i}_quiet1", i, "quiet"), ("train", f"tr_{i}_quiet2", i, "quiet"), ("train", f"tr_{i}_zero", i, "zero")]
        R += [("train", f"tr_{i}_r{r}", i, str(r)) for r in range(93, 98)]
    # V5: the injected model
    R += [("frozen", f"v5_nominal_hold_inj{k}", "nominal", "hold", "a", "1", "0.08", "-", "injected") for k in range(32)]
    for i in DEV:
        R += [("frozen", f"v5_{i}_hold_inj{k}", i, "hold", "all", "-", "0.08", "-", "injected") for k in range(8)]
        R += [("train", f"tr_{i}_inj{k}", i, "injected") for k in range(5)]
    return R


MACHINES = 4


def machine(name):
    """The fixed split (the owner's four machines, VALIDATION_SPLIT.md): the run of index i in the list of runs()
    goes to machine 1 + i mod 4. No run is moved or repeated afterwards."""
    names = [r[1] for r in runs()]
    return 1 + names.index(name) % MACHINES


REFERENCE = dict(ngspice_sha256="820658317b0b54035208da41936fd6871ce924036e5ea4113a4168b821b7fc45",
                 pdk_commit="1232782c1b9fab3aacda74d67ce7c92bf7da8105", python_version="3.12.3",
                 python_sha256="e50d468e8b0adfb05733f5b87b3cff34829c4a8c1aea50c865aa8bdfe4bb150f", numpy_version="2.3.5",
                 numpy_record_sha256="064003bdb6f9f7bb06e46e07cc3398cbfdc3c114dfe55b89d239e564917be2fb",
                 analog_cm_sha256="98c7c296dfd04e81f568db91c8261a07f00d8d63e63e5cc1d331451ccda30941")


def inventory():
    """The machine's environment (as the launch kit computes it) and inventory."""
    import hashlib, importlib.metadata, os, platform
    sha = lambda b: hashlib.sha256(b).hexdigest()
    pdk = HERE.parent.parent / "circuit" / "pdk"
    py = subprocess.run([PY, "-c", "import importlib.metadata, hashlib, numpy, platform, os, sys; "
                         "print(platform.python_version(), numpy.__version__, "
                         "hashlib.sha256(importlib.metadata.distribution('numpy').read_text('RECORD').encode()).hexdigest(), "
                         "os.path.realpath(sys.executable))"], capture_output=True, text=True, cwd="/").stdout.split()
    env = dict(ngspice_sha256=sha(Path("/usr/bin/ngspice").read_bytes()),
               pdk_commit=subprocess.check_output(["git", "-C", str(pdk.resolve()), "rev-parse", "HEAD"], text=True).strip(),
               python_version=py[0], python_sha256=sha(Path(py[3]).read_bytes()), numpy_version=py[1], numpy_record_sha256=py[2],
               analog_cm_sha256=sha(Path("/usr/lib/x86_64-linux-gnu/ngspice/analog.cm").read_bytes()))
    mem = next(l for l in Path("/proc/meminfo").read_text().splitlines() if l.startswith("MemTotal"))
    cpu = next((l.split(":", 1)[1].strip() for l in Path("/proc/cpuinfo").read_text().splitlines() if l.startswith("model name")), "")
    inv = dict(hostname=platform.node(), processors=os.cpu_count(), memory=mem.split(":")[1].strip(), cpu=cpu,
               os=platform.platform(), venv=PY)
    return dict(environment=env, identical_to_reference=env == REFERENCE, inventory=inv)


def command(work, r):
    kind, name = r[0], r[1]
    out = Path(work) / (name if kind == "train" else f"{name}.json")
    return out, [PY, "-B", str(HERE / "vrun.py"), kind, str(out)] + list(r[2:])


def run(work, filt=""):
    """FILT: a substring of the run names, or `machine=K` (K = 1 to 4: that machine's share, after its environment is
    checked against the reference; a machine whose hashes differ runs nothing)."""
    import json, os
    Path(work).mkdir(parents=True, exist_ok=True)
    if filt.startswith("machine="):
        inv = inventory()
        inv["machine"] = int(filt.split("=")[1])
        (Path(work) / f"MACHINE_{inv['machine']}.json").write_text(json.dumps(inv, indent=1) + "\n")
        assert inv["identical_to_reference"], "this machine's environment differs from the reference: it runs nothing"
        os.environ["VAL_MACHINE"] = str(inv["machine"])
    if filt.startswith("machine="):
        R = runs()
        todo = [r for i, r in enumerate(R) if 1 + i % MACHINES == int(filt.split("=")[1])]
    else:
        todo = [r for r in runs() if filt in r[1]]
    log = open(Path(work) / "plan.log", "a")

    def one(r):
        out, cmd = command(work, r)
        done = (out / "meta.json") if r[0] == "train" else out
        if done.exists():
            return
        t0 = time.time()
        p = subprocess.run(cmd, capture_output=True, text=True)
        msg = f"{r[1]} exit {p.returncode} {time.time() - t0:.0f} s"
        if p.returncode:
            msg += "\n" + p.stderr[-2000:]
        print(msg, file=log, flush=True)
    with ThreadPoolExecutor(4) as ex:
        list(ex.map(one, todo))
    print("done", filt, file=log, flush=True)


if __name__ == "__main__":
    if sys.argv[1] == "env":                  # vplan.py env: the machine's environment and inventory
        import json
        print(json.dumps(inventory(), indent=1))
    elif sys.argv[1] == "list":
        for r in runs():
            print(" ".join(r))
        print(len(runs()), "runs")
    else:
        run(sys.argv[2], sys.argv[3] if len(sys.argv) > 3 else "")
