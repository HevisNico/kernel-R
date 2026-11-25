"""controls4 against controls3: the same stage N, plus the trace. No simulation.

  check_controls4.py C4_DIR C3_DIR     a controls4 run and a controls3 run of the same spec, seed, round and seal

Holds iff input.spice is byte-identical, noisy_record.json is identical once the cost fields are removed (as
tests/check_duplicate.py removes them), and the controls4 folder has trace.raw and trace.digest.json, with the digest
matching the raw file.
"""
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent))
import check_duplicate as cd  # noqa: E402


def main(c4, c3):
    c4, c3 = Path(c4), Path(c3)
    same_deck = (c4 / "input.spice").read_bytes() == (c3 / "input.spice").read_bytes()
    a, b = (cd.strip(json.loads((d / "noisy_record.json").read_text())) for d in (c4, c3))
    diff = cd.first_diff(a, b)
    has = (c4 / "trace.raw").exists() and (c4 / "trace.digest.json").exists()
    dig = False
    if has:                                                 # recompute the data digest, the stored file untouched
        import hashlib
        stored = json.loads((c4 / "trace.digest.json").read_text())
        data = (c4 / "trace.raw").read_bytes()
        i = data.find(b"Binary:\n")
        dig = hashlib.sha256(data[i + 8:]).hexdigest() == stored["data_sha256"]
    print(f"input.spice byte-identical: {same_deck}")
    print(f"noisy_record.json identical (cost removed): {diff is None}" + ("" if diff is None else f", first difference {diff}"))
    print(f"controls4 trace.raw and trace.digest.json present: {has}; digest matches the raw data: {dig}")
    ok = same_deck and diff is None and has and dig
    print("CONTROLS4 = CONTROLS3 + TRACE" if ok else "CONTROLS4 CHECK FAILS")
    return ok


if __name__ == "__main__":
    sys.exit(0 if main(sys.argv[1], sys.argv[2]) else 1)
