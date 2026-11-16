"""A calendar shim for the noise study's cost3.py (`dnf_calendar` reads a copy of dnf.py by path): the same module
as ../dnf.py, with `calendar` giving the untrained control run (the 16 tests only, on the preset state). Code only,
no data."""
import importlib.util
from pathlib import Path

_spec = importlib.util.spec_from_file_location("dnf_phase0", Path(__file__).resolve().parent.parent / "dnf.py")
_dnf = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_dnf)
INPUTS, LINES, WINDOW, WIRE, SLOT, SETTLE = _dnf.INPUTS, _dnf.LINES, _dnf.WINDOW, _dnf.WIRE, _dnf.SLOT, _dnf.SETTLE


def calendar(need_a, need_b, need_c1, need_c2):
    return _dnf.calendar(need_a, need_b, need_c1, need_c2, "untrained")
