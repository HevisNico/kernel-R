"""Why did run a55-main-tt27 stop? Exploratory diagnosis made after the campaign. It replaces no run and enters no count.

  diagnose_a55.py scan OUT FIRST LAST NGSPICE PDK     short sessions with imposed process numbers FIRST..LAST-1
  diagnose_a55.py again OUT NGSPICE PDK               the numbers that aborted in OUT, four more ways
  diagnose_a55.py report PARENT                       -> FAILED_RUN_a55-main-tt27.json, from the session logs of every scan under PARENT

Run a55 used the deck of every `main-tt27` run and `setseed 10055`; its noise also depended on the
number of its simulator process, which nobody chose and nobody recorded (it stopped before the
fingerprint was written). Here the same deck and the same seed are started again with process numbers
imposed through a small preloaded library — what the registered launcher forbids — and each session is
stopped after 30 us, before the first pulse. A session costs a few seconds.
"""
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "sky130-supervisor-closure"))
import sim

SHIM = """#define _GNU_SOURCE
#include <stdlib.h>
#include <unistd.h>
#include <sys/syscall.h>
#include <sys/types.h>
pid_t getpid(void) { const char *s = getenv("FAKEPID"); if (s) return (pid_t) atoi(s); return (pid_t) syscall(SYS_getpid); }
"""
SEED = 10055
STOP_S = 0.02002                # the end of the transient of run a55: 91 slots


def shim(out):
    out.mkdir(parents=True, exist_ok=True)
    if not (out / "fakepid.so").exists():
        (out / "fakepid.c").write_text(SHIM)
        subprocess.run(["gcc", "-shared", "-fPIC", "-O2", str(out / "fakepid.c"), "-o", str(out / "fakepid.so")], check=True)
    return (out / "fakepid.so").resolve()


def session(folder, number, ngspice, pdk, library, edit=lambda t: t, seed=SEED, max_step="200n"):
    text = edit(sim.deck(section="tt", temperature=27, noise=True, leak_S=1e-11, junction="areas"))
    s = sim.Session(folder, text, ngspice, pdk, seed=seed, stop_s=STOP_S, max_step=max_step, noise_id=number, shim=library)
    try:
        s.run_to(30e-6)
        s.kill()
        return dict(number=number, aborted=False)
    except RuntimeError:
        s.kill()
        log = (Path(folder) / "session.log").read_text(errors="replace").splitlines()
        return dict(number=number, aborted=True, message=next((l.strip() for l in log if "imestep too small" in l), "no message"))


def swap(text, old, new):
    assert text.count(old) == 1, old
    return text.replace(old, new)


def main():
    out = Path(sys.argv[2])
    if sys.argv[1] == "scan":
        first, last, ngspice, pdk = int(sys.argv[3]), int(sys.argv[4]), Path(sys.argv[5]), Path(sys.argv[6])
        library = shim(out)
        rows = [session(out / f"n{n}", n, ngspice, pdk, library) for n in range(first, last)]
        (out / f"scan-{first}-{last}.json").write_text(json.dumps(rows, indent=1) + "\n")
    elif sys.argv[1] == "again":
        ngspice, pdk = Path(sys.argv[3]), Path(sys.argv[4])
        library = shim(out)
        bad = [r["number"] for f in sorted(out.glob("scan-*.json")) for r in json.loads(f.read_text()) if r["aborted"]]
        rows = []
        for n in bad:
            rows.append(dict(number=n,
                             same_again=session(out / f"again-{n}", n, ngspice, pdk, library),
                             other_seed=session(out / f"seed-{n}", n, ngspice, pdk, library, seed=SEED + 1),
                             looser_current_tolerance=session(out / f"abstol-{n}", n, ngspice, pdk, library, edit=lambda t: swap(t, "abstol=1e-13", "abstol=1e-12")),
                             smaller_largest_step=session(out / f"step-{n}", n, ngspice, pdk, library, max_step="100n")))
        (out / "again.json").write_text(json.dumps(rows, indent=1) + "\n")
    if sys.argv[1] != "report":
        return
    rows = []                                               # every session whose transient command returned or aborted; a scan that was cut leaves its last session out
    for log in sorted(out.glob("*/n*/session.log"), key=lambda p: int(p.parent.name[1:])):
        text = log.read_text(errors="replace")
        if ">>> tran " in text:
            message = next((l.strip() for l in text.splitlines() if "imestep too small" in l), None)
            rows.append(dict(number=int(log.parent.name[1:]), aborted=message is not None, message=message))
    bad = [r for r in rows if r["aborted"]]
    again = [x for f in sorted(out.glob("*/again.json")) for x in json.loads(f.read_text())]
    summary = dict(scope="exploratory diagnosis after the campaign; imposed process numbers; sessions stopped at 30 us; no run of the campaign is replaced",
                   deck="main-tt27: typical corner, 27 C, noise, junction areas", setseed=SEED, sessions=len(rows),
                   process_numbers=[min(r["number"] for r in rows), max(r["number"] for r in rows)], aborted=len(bad),
                   aborted_numbers=[r["number"] for r in bad], messages=sorted({r["message"] for r in bad}), again=again or None)
    (HERE / "FAILED_RUN_a55-main-tt27.json").write_text(json.dumps(summary, indent=1) + "\n")
    print(json.dumps(summary, indent=1))


if __name__ == "__main__":
    main()
