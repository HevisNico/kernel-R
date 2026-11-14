"""The reads of each port of a network instance at the spacing of the calendar, with every other port idle.
Phase 1, exploratory.

  noisechar.py OUT SECTION SEED quiet|noise NGSPICE PDK [READS]

Two cells in the deck of the network, no edge: a calendar of sources only. Port 1 of each cell receives
READS pulses 18 units apart, then port 2 does; the pulses of cell b are 9 units after those of cell a, so
no cell ever sees two pulses closer than 18 units. With `quiet` the run gives, per port, the latency of a
FIRE at that spacing without noise; with `noise`, the scatter of that latency and of the dose. The seed
fixes the mismatch sample; the noise is seeded by the simulator's process number and differs at each run.
"""
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
import router

SPACING = 18


def calendar(reads):
    sources = []
    for i, port in enumerate((1, 2)):
        for k in range(reads):
            sources.append((SPACING * (i * reads + k), "a", port))
            sources.append((SPACING * (i * reads + k) + SPACING // 2, "b", port))
    return dict(name=f"each port alone, {reads} reads {SPACING} units apart", sources=sorted(sources), edges=[],
                horizon=SPACING * 2 * reads + SPACING // 2)


if __name__ == "__main__":
    out, section, seed, mode, ngspice, pdk = sys.argv[1:7]
    reads = int(sys.argv[7]) if len(sys.argv) > 7 else 26
    r = router.run(Path(out), calendar(reads), Path(ngspice), Path(pdk), seed=None if seed == "none" else int(seed),
                   section=section, noise=mode == "noise")
    print(json.dumps(dict(word=router.word(r), fires=len(r["fires"]), wall_s=round(r["wall_s"]))))
