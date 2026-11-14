"""Does the noise fingerprint follow the random draw and nothing else? Exploratory check, never part of a registered run.

  fingerprint_check.py OUT NGSPICE PDK

ngspice 42 seeds its noise sources from the number of its own process (see ../circuit/repetition,
PR 115). This check, and only this check, imposes that number through a small preloaded library, so
as to give the same number to different circuits and different numbers to the same circuit. The
decks are those with junction areas. Each session is stopped after the first 30 us. Expected:

- two sessions have the same fingerprint exactly when they have the same process number and the
  same `setseed` command; the corner and the temperature do not matter;
- on a corner without mismatch, `setseed` changes the noise and nothing else: without noise, the
  waveform is the same byte for byte whatever the seed. A distinct `setseed` per run therefore
  separates the draws of two runs even if they get the same process number. On a mismatch
  instance `setseed` is the instance itself and cannot be used for that.

The registered launcher refuses any preloaded library: there the process number is whatever the
operating system gives, the noise cannot be replayed, and the fingerprint is the only record of
what was drawn.
"""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import extract
import sim

SHIM = """#define _GNU_SOURCE
#include <stdlib.h>
#include <unistd.h>
#include <sys/syscall.h>
#include <sys/types.h>
pid_t getpid(void) { const char *s = getenv("FAKEPID"); if (s) return (pid_t) atoi(s); return (pid_t) syscall(SYS_getpid); }
"""
CASES = [("tt27", 4242, True, None), ("ss27", 4242, True, None), ("tt125", 4242, True, None), ("mm2001", 4242, True, None),
         ("mm2002", 4242, True, None), ("tt27", 4243, True, None), ("mm2001", 4243, True, None), ("tt27", 4242, True, 7),
         ("tt27", 4242, True, 8), ("ss27", 4242, True, 7), ("tt27", 4243, True, 7),
         ("tt27", 4242, False, None), ("tt27", 4242, False, 7), ("tt27", 4243, False, 8)]


def main():
    out, ngspice, pdk = Path(sys.argv[1]), Path(sys.argv[2]), Path(sys.argv[3])
    out.mkdir(parents=True)
    (out / "fakepid.c").write_text(SHIM)
    subprocess.run(["gcc", "-shared", "-fPIC", "-O2", str(out / "fakepid.c"), "-o", str(out / "fakepid.so")], check=True)
    configs = json.loads((HERE / "configs.json").read_text())
    rows = []
    for i, (name, number, noise, seed) in enumerate(CASES):
        c = dict(configs[name])
        c["seed"] = c["seed"] if seed is None else seed
        s = sim.Session(out / f"case-{i}", sim.deck(section=c["section"], temperature=c["temperature_C"], noise=noise, junction="areas"), ngspice, pdk,
                        seed=c["seed"], stop_s=sim.SLOT, noise_id=number, shim=(out / "fakepid.so").resolve())
        s.run_to(30e-6)
        raw = s.close()
        d = extract.read_raw(raw)
        rows.append(dict(config=name, setseed=c["seed"], imposed_process_number=number, noise=noise, raw_sha256=sim.digest(raw),
                         points_sha256=hashlib.sha256(d.tobytes()).hexdigest(), fingerprint=extract.noise_fingerprint(d)))   # the raw file also carries its date
    noisy = [r for r in rows if r["noise"]]
    draw = lambda r: (r["imposed_process_number"], r["setseed"])
    same = all((a["fingerprint"] == b["fingerprint"]) == (draw(a) == draw(b)) for a in noisy for b in noisy)
    quiet = [r for r in rows if not r["noise"]]
    result = dict(cases=rows, same_draw_same_fingerprint_and_only_then=same, noisy_waveforms_all_different=len({r["points_sha256"] for r in noisy}) == len(noisy),
                  without_noise_the_seed_changes_nothing=len({r["points_sha256"] for r in quiet}) == 1 and len({r["fingerprint"] for r in quiet}) == 1,
                  quiet_fingerprint_differs_from_every_noisy_one=all(quiet[0]["fingerprint"] != r["fingerprint"] for r in noisy))
    (out / "result.json").write_text(json.dumps(result, indent=1) + "\n")
    print(json.dumps(result, indent=1))
    assert all(v for k, v in result.items() if k != "cases")


if __name__ == "__main__":
    main()
