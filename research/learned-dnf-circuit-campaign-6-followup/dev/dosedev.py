"""Development only: the nominal cell's guard-on calibration deck with the dose parameters of the cell rewritten.

Not campaign code. It edits no file of the repository and writes nothing inside it. It takes no seed: the three cells
are the nominal cell (section `tt`), and the deck is a quiet deck (no noise source, no noise seed).

  dosedev.py deck  REPO OUT.spice [NAME=VALUE ...]   the deck's text, written to OUT.spice; nothing is simulated
  dosedev.py cal   REPO OUT NGSPICE PDK [NAME=VALUE ...]   one guard-on calibration deck, then its doses
  dosedev.py doses REPO OUT                           the doses of a finished run, again

NAME is one of vhi, vlo, cs0, idis: the parameters of `research/circuit/cell.spice` that set the dose
(`(cs0 / cf0) x (vhi - vlo)`, DESIGN.md) and the discharge rate (`idis / cs0`). VALUE is written as given, in SPICE
notation (0.7, 600f, 12.3n). With no NAME=VALUE the deck is the repository's own, byte for byte (test_dosedev.py).

The run is batch6.cal's (campaign 6's development batch), called through the same frozen functions
(plans4.calibration, net.deck, session4.play, run4.trnoise_fingerprint), with the deck's text rewritten in between and
no seed. If `idis` is changed, the write gate of the plan restores the changed value instead of c4.IDIS.
"""
import hashlib
import json
from pathlib import Path
import re
import resource
import sys
import time

ALLOWED = ("vhi", "vlo", "cs0", "idis")
SPICE_NUMBER = re.compile(r"^[0-9]+(\.[0-9]+)?(e-?[0-9]+)?[fpnum]?$")
SCALE = dict(f=1e-15, p=1e-12, n=1e-9, u=1e-6, m=1e-3)


def repo_paths(repo):
    r = Path(repo).resolve() / "research"
    for p in (r / "learned-dnf-circuit-campaign-5", r / "network-circuit", r / "learned-dnf-circuit", r / "circuit"):
        sys.path.insert(0, str(p))


def parse(pairs):
    """['vhi=0.7', ...] -> {'vhi': '0.7'}. Refuses any other name, a name given twice, and a value that is not a number."""
    out = {}
    for x in pairs:
        name, _, value = x.partition("=")
        assert name in ALLOWED, f"refused: {name!r} is not one of {ALLOWED}"
        assert name not in out, f"refused: {name} given twice"
        assert SPICE_NUMBER.match(value), f"refused: {value!r} is not a SPICE number"
        out[name] = value
    return out


def number(value):
    """A SPICE number as a float (for the gate of idis only)."""
    return float(value[:-1]) * SCALE[value[-1]] if value[-1] in SCALE else float(value)


def rewrite(text, params):
    """The deck's text with each NAME=old replaced by NAME=new on its `.param` line. Each name must appear exactly
    once as a parameter definition in the whole deck. With no parameter the text is returned unchanged."""
    changed = {}
    for name, value in params.items():
        pattern = re.compile(rf"(?m)^(\.param\b.*?\b{name}=)(\S+)")
        found = pattern.findall(text)
        assert len(found) == 1, f"{name}: {len(found)} definitions on .param lines, not 1"
        assert len(re.findall(rf"\b{name}=", text)) == 1, f"{name}= appears elsewhere in the deck"
        changed[name] = dict(old=found[0][1], new=value)
        text = pattern.sub(lambda m: m.group(1) + value, text)
    return text, changed


def deck(params):
    import c4
    import net
    original = net.deck(cells=c4.CELLS, section="tt")
    text, changed = rewrite(original, params)
    return original, text, changed


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def cal(repo, out, ngspice, pdk, params):
    """One guard-on calibration deck on the nominal cell, as batch6.cal, with the rewritten deck."""
    assert __debug__, "refused: not with python -O, the guards are asserts"
    repo_paths(repo)
    import c4
    print(c4.require_pinned())
    import plans4
    import run4
    import session4
    began = time.time()
    out = Path(out).resolve()
    assert Path(repo).resolve() not in out.parents, "refused: the run's folder is inside the repository"
    plan, reads = plans4.calibration()
    if "idis" in params:                                     # the write gate restores the changed bias, not c4.IDIS
        new = number(params["idis"])
        plan["gates"] = [(date, {port: (new if value else 0.0) for port, value in settings.items()}) for date, settings in plan["gates"]]
    original, text, changed = deck(params)
    result, tr = session4.play(out / "evidence", plan, text, Path(ngspice), Path(pdk), seed=None, guard_off=False)
    (out / "evidence" / "pdk").unlink()
    reached = bool(tr.t[-1] >= result["horizon_s"] - 1e-9)
    mark = run4.trnoise_fingerprint(tr, c4.CELLS)
    ev = out / "evidence"
    rec = dict(id=out.name, kind="cal", section="tt", seed=None, stage=None, guard="on", reads=reads)
    rec.update(noise=dict(model="none"), reached_its_last_date=reached, horizon_s=result["horizon_s"], waveform_ends_s=result["waveform_ends_s"],
               points=result["points"], files={x: sha(ev / x) for x in ("input.spice", "session.log", "trace.raw", "result.json")})
    rec.update(noise_fingerprint=mark, wall_s=time.time() - began, peak_rss_MB=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss / 1024)
    rec["dosedev"] = dict(what="development run on the nominal cell, outside any campaign", parameters_changed=changed,
                          deck_sha256_of_the_repository=hashlib.sha256(original.encode()).hexdigest(),
                          deck_sha256_as_run=hashlib.sha256(text.encode()).hexdigest(), interpreter=c4.interpreter())
    (out / "noise.sha256").write_text(mark + "\n")
    (out / "record.json").write_text(json.dumps(rec, indent=1) + "\n")
    assert reached, "the waveform ends before the last date of the run"
    return rec


def doses(repo, out):
    """The doses of a finished guard-on deck: per port, its eight joint-dose moves, and D_V as campaign 6's inputs6
    writes it: repr(float(mean of the eight moves, exact, in mV) / 1000). Also each read's FIRE bit, latency and writes,
    and the checks of the write's timing (`timing`)."""
    repo_paths(repo)
    import c4
    import measure
    import predicted as P
    import reads4
    out = Path(out)
    rec = json.loads((out / "record.json").read_text())
    result = json.loads((out / "evidence" / "result.json").read_text())
    rows = reads4.calibration_reads(measure.Trace(out / "evidence" / "trace.raw"), result, rec["reads"])
    by = {(r["cell"], r["stage"], r["read"]): r for r in rows}
    res = dict(parameters_changed=rec["dosedev"]["parameters_changed"], D_V={}, moves_mV={}, spread_of_successive_doses={}, reads=[])
    for c in c4.CELLS:
        res["D_V"][c], res["moves_mV"][c], res["spread_of_successive_doses"][c] = [], [], []
        for p in (1, 2):
            moves = [P.exact(by[(c, k, "joint dose")]["ports"][str(p)]["move_mV"]) for k in range(c4.STAGES)]
            mean = sum(moves) / len(moves)
            res["D_V"][c].append(repr(float(mean) / 1000))
            res["moves_mV"][c].append([float(m) for m in moves])
            res["spread_of_successive_doses"][c].append(float((max(moves) - min(moves)) / mean))
    for r in rows:
        if r["read"] == "joint dose":
            continue
        res["reads"].append(dict(cell=r["cell"], stage=r["stage"], read=r["read"], fire=r["fire"], latency=r["latency"], late_fires=r["late_fires"],
                                 writes={p: r["ports"][p]["writes"] for p in ("1", "2")},
                                 move_mV={p: r["ports"][p]["move_mV"] for p in ("1", "2")}, q_peak=r["q_peak"]))
    res["timing"] = timing(rows, c4.CELLS)
    (out / "DOSES.json").write_text(json.dumps(res, indent=1) + "\n")
    print(json.dumps(dict(parameters_changed=res["parameters_changed"], D_V=res["D_V"], spread_of_successive_doses=res["spread_of_successive_doses"],
                          timing={k: v for k, v in res["timing"].items() if k != "per_cell_detail"}), indent=1))
    return res


TU = 20e-6                                                   # one time unit, as net.TU
ENTRY_AFTER_FIRE_UNITS = 0.2                                 # G2 of DOSE_PLAN.md
GATED_MOVE_BOUND_MV = 0.01                                   # c4.MOVE_BOUND_MV


def timing(rows, cells):
    """What a guard-on calibration deck shows about the timing of a write (G2), and the first firing stages (G3).

    In this deck every read is gated (its dose bias is zero, so its sensor does not discharge and it has no ERROR
    phase), and every dose is a clock-only slot with no pulse (so it cannot fire). So the deck cannot show a read that
    fires and writes. It gives the two dates separately, per cell:
      - the ERROR entry: in each joint-dose slot, the rise of the write signal of each port, after the slot's start;
      - the FIRE: the latency of each firing read.
    `entry_minus_fire_units` is the earliest entry minus the latest FIRE latency of the cell. The direct check, a
    read that both receives a pulse and may write, exists only in a network run."""
    out = dict(per_cell={}, per_cell_detail={}, reads_that_fire_and_write=[], gated_reads_that_write=[], largest_gated_move_mV=0.0, first_firing_stage={})
    for c in cells:
        entries, widths, lat = [], [], []
        for r in rows:
            if r["cell"] != c:
                continue
            if r["read"] == "joint dose":
                for p in ("1", "2"):
                    rises = r["ports"][p]["rises"]
                    assert len(rises) == 1, f"joint dose of {c}{p} at stage {r['stage']}: {len(rises)} rises of the write signal"
                    entries.append((rises[0]["rise_s"] - r["start_s"]) / TU)
                    widths.append(rises[0]["width_s"] / TU)
            else:
                wrote = any(r["ports"][p]["writes"] for p in ("1", "2"))
                if r["fire"]:
                    lat.append(r["latency"])
                    if wrote:
                        out["reads_that_fire_and_write"].append(dict(cell=c, stage=r["stage"], read=r["read"]))
                if wrote:
                    out["gated_reads_that_write"].append(dict(cell=c, stage=r["stage"], read=r["read"]))
                out["largest_gated_move_mV"] = max([out["largest_gated_move_mV"]] + [abs(r["ports"][p]["move_mV"]) for p in ("1", "2")])
        margin = min(entries) - max(lat) if lat else None
        out["per_cell"][c] = dict(error_entry_units=[min(entries), max(entries)], error_width_units=[min(widths), max(widths)],
                                  fire_latency_units=[min(lat), max(lat)] if lat else None, firing_reads=len(lat),
                                  entry_minus_fire_units=margin, at_least_0_2=None if margin is None else margin >= ENTRY_AFTER_FIRE_UNITS)
        out["per_cell_detail"][c] = dict(error_entry_units=entries, error_width_units=widths, fire_latency_units=lat)
        for read in ("empty", "port 1", "port 2", "both", "both, second 0.3 late"):
            mine = sorted((r for r in rows if r["cell"] == c and r["read"] == read), key=lambda r: r["stage"])
            if mine:
                out["first_firing_stage"][f"{c}, {read}"] = next((r["stage"] for r in mine if r["fire"]), None)
    out["gated_moves_within_bound"] = out["largest_gated_move_mV"] <= GATED_MOVE_BOUND_MV
    return out


if __name__ == "__main__":
    a = sys.argv[1:]
    if a and a[0] == "deck":
        repo_paths(a[1])
        original, text, changed = deck(parse(a[3:]))
        Path(a[2]).write_text(text)
        print(json.dumps(dict(changed=changed, sha256_of_the_repository_deck=hashlib.sha256(original.encode()).hexdigest(),
                              sha256_written=hashlib.sha256(text.encode()).hexdigest())))
    elif a and a[0] == "cal":
        cal(a[1], a[2], a[3], a[4], parse(a[5:]))
        doses(a[1], a[2])
    elif a and a[0] == "doses":
        doses(a[1], a[2])
    else:
        raise SystemExit(__doc__)
