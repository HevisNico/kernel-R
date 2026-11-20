"""Development only, EXPLORATORY: one scan of the nominal cell with the solver's relative tolerance rewritten.

Not campaign code. It edits no file of the repository and writes nothing inside it. dosedev.py and dosedev2.py are
not changed: this file adds one allowed name, `reltol`, for scans only.

  dosedev_tol.py scan REPO OUT CELL KIND ARGS... NGSPICE PDK -- [NAME=VALUE ...]
        as `dosedev2.py scan`, with NAME one of vhi, vlo (the window, as before) or reltol

How: dosedev2.scan is called unchanged. It rewrites the deck's text through dosedev.rewrite; for the time of the call
that function is replaced by `rewrite` below, which does what dosedev.rewrite does for the window and, for reltol,
replaces the value on the deck's `.option` line: `reltol=` must appear exactly once in the whole deck, on a line that
starts with `.option`. With no reltol the text is dosedev.rewrite's, byte for byte (test_dosedev_tol.py).
No calibration deck and no network run takes a reltol here.
"""
import contextlib
from pathlib import Path
import re
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import dosedev                                             # noqa: E402
import dosedev2                                            # noqa: E402

TOLERANCE = "reltol"
TOLERANCE_VALUE = re.compile(r"^[0-9]+(\.[0-9]+)?e-[0-9]+$")
FROZEN_REWRITE = dosedev.rewrite


def parse(pairs):
    """['vhi=0.7', 'reltol=1e-5'] -> {'vhi': '0.7', 'reltol': '1e-5'}. The window's names go through dosedev2.parse,
    unchanged. reltol: at most once, a number written with an exponent."""
    mine = [x for x in pairs if x.partition("=")[0] == TOLERANCE]
    params = dosedev2.parse([x for x in pairs if x.partition("=")[0] != TOLERANCE])
    assert len(mine) <= 1, f"refused: {TOLERANCE} given twice"
    if mine:
        value = mine[0].partition("=")[2]
        assert TOLERANCE_VALUE.match(value), f"refused: {value!r} is not a tolerance written as 1e-5"
        params[TOLERANCE] = value
    return params


def rewrite(text, params):
    """dosedev.rewrite for every name but reltol; then reltol's value on its `.option` line."""
    text, changed = FROZEN_REWRITE(text, {k: v for k, v in params.items() if k != TOLERANCE})
    if TOLERANCE in params:
        pattern = re.compile(rf"(?m)^(\.option\b.*?\b{TOLERANCE}=)(\S+)")
        found = pattern.findall(text)
        assert len(found) == 1, f"{TOLERANCE}: {len(found)} definitions on .option lines, not 1"
        assert len(re.findall(rf"\b{TOLERANCE}=", text)) == 1, f"{TOLERANCE}= appears elsewhere in the deck"
        changed[TOLERANCE] = dict(old=found[0][1], new=params[TOLERANCE])
        text = pattern.sub(lambda m: m.group(1) + params[TOLERANCE], text)
    return text, changed


@contextlib.contextmanager
def tolerance():
    """For the time of the block, dosedev.rewrite is `rewrite` above."""
    assert dosedev.rewrite is FROZEN_REWRITE, "refused: dosedev.rewrite is already replaced"
    dosedev.rewrite = rewrite
    try:
        yield
    finally:
        dosedev.rewrite = FROZEN_REWRITE


def scan(repo, out, argv, pairs):
    params = parse(pairs)
    assert argv[1] in ("pair", "line1", "line2"), f"refused: kind {argv[1]} (scans only)"
    with tolerance():
        return dosedev2.scan(repo, out, argv, params)


if __name__ == "__main__":
    a = sys.argv[1:]
    if a and a[0] == "scan":
        cut = a.index("--")
        scan(a[1], a[2], a[3:cut], a[cut + 1:])
    else:
        raise SystemExit(__doc__)
