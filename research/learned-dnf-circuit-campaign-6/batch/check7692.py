"""Campaign 6's development batch: the declared check that the scans' deck (`net.deck(..., leak_per_port=True)`) draws
the same mismatched cell as the calibration deck (`net.deck(...)`) for one seed. Run once before the marker, on
campaign 5's development seed 7692 only (already simulated, in no claim); never on a seed of the batch. New code.

  check7692.py OUT RM_CAL_ON NGSPICE PDK      RM_CAL_ON: campaign 5's collected guard-on deck of 7692 (RM, machine a)

For each cell: a leak-deck session (scan6.Driver, the cell's two ports on the path) measures u(0), then gives two
joint doses (both ports, clock-only, writes enabled) and measures each move. They are compared with the guard-on
deck's u before its first read (stage 0, `empty`) and its joint-dose moves of stages 0 and 1. Tolerances, fixed
before the check: 2 uV on u, 20 uV on a move (the scan's own resolution). Beyond them: STOP and report (the scans
would measure another cell).
"""
import json
from pathlib import Path
import sys
import time

HERE = Path(__file__).resolve().parent
import batch6                                           # noqa: E402
import scan6                                            # noqa: E402
import c4                                               # noqa: E402
import predicted as P                                   # noqa: E402

SEED = 7692
TOL_U_V, TOL_MOVE_V = 2e-6, 20e-6


def main(argv=None):
    a = sys.argv[1:] if argv is None else argv
    batch6.require_debug()
    out, on, ngspice, pdk = Path(a[0]), Path(a[1]), Path(a[2]), Path(a[3])
    rec = json.loads((on / "record.json").read_text())
    assert rec.get("seed") == SEED and rec.get("guard") == "on", "refused: this check runs on campaign 5's 7692 guard-on deck only"
    print(c4.require_pinned())
    began = time.time()
    rows, _ = P.load(on, on)
    by = {(r["cell"], r["stage"], r["read"]): r for r in rows}
    res = {}
    for c in c4.CELLS:
        drv = scan6.Driver(out / c, SEED, c, (1, 2), {1: 1e-3, 2: 1e-3}, ngspice, pdk)
        u0 = dict(drv.u0)
        moves = []
        for _ in range(2):
            before = dict(drv.u)
            drv.slot("dose", (1, 2))
            moves.append({p: before[p] - drv.u[p] for p in (1, 2)})
        drv.close()
        (out / c / "evidence" / "pdk").unlink()
        ref_u = {p: by[(c, 0, "empty")]["ports"][str(p)]["u_before_mV"] / 1e3 for p in (1, 2)}
        ref_m = [{p: by[(c, k, "joint dose")]["ports"][str(p)]["move_mV"] / 1e3 for p in (1, 2)} for k in (0, 1)]
        du = {p: u0[p] - ref_u[p] for p in (1, 2)}
        dm = [{p: m[p] - r[p] for p in (1, 2)} for m, r in zip(moves, ref_m)]
        ok = all(abs(v) <= TOL_U_V for v in du.values()) and all(abs(v) <= TOL_MOVE_V for d in dm for v in d.values())
        res[c] = dict(u0_V=u0, deck_u_V=ref_u, du_V=du, moves_V=moves, deck_moves_V=ref_m, dmoves_V=dm, within_tolerance=ok)
    out_rec = dict(check="the leak deck draws the calibration deck's cell (BATCH_SPEC.md, declared check)", seed=SEED,
                   tolerances_V=dict(u=TOL_U_V, move=TOL_MOVE_V), cells=res, all_within=all(v["within_tolerance"] for v in res.values()),
                   wall_s=time.time() - began)
    (out / "CHECK_7692.json").write_text(json.dumps(out_rec, indent=1, default=str) + "\n")
    print(json.dumps(dict(all_within=out_rec["all_within"], cells={c: v["within_tolerance"] for c, v in res.items()})))


if __name__ == "__main__":
    main()
