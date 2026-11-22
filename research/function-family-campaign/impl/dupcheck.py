"""The duplicate check with the criterion fixed by PREDICTION.md section 6: topup.compare's five fields, with
`trace.raw` compared after removing its `Date:` header line. New code; topup.compare is not changed.

  dupcheck.py RUN_DIR DUP_DIR        prints the comparison as JSON; exit 0 when identical

The header of an ngspice raw file is text lines up to the line `Binary:` (or `Values:`); only a header line that
starts with `Date: ` is removed, exactly once, and everything else (the rest of the header and all the data) is
hashed as it is. A file with no such line, or with more than one, is compared as it is and flagged.
"""
import hashlib
import json
from pathlib import Path
import sys

MARKERS = (b"\nBinary:\n", b"\nValues:\n")


def trace_without_date(path):
    """(sha256 of the file with its one `Date:` header line removed, how many Date lines the header had)."""
    data = Path(path).read_bytes()
    ends = [data.find(m) for m in MARKERS if data.find(m) >= 0]
    end = min(ends) if ends else len(data)
    header, rest = data[:end + 1], data[end + 1:]
    lines = header.split(b"\n")
    dates = [i for i, ln in enumerate(lines) if ln.startswith(b"Date: ")]
    if len(dates) == 1:
        del lines[dates[0]]
        header = b"\n".join(lines)
    return hashlib.sha256(header + rest).hexdigest(), len(dates)


def comparable(run_dir):
    import topup
    out = topup.comparable(run_dir)
    out["trace_raw_full"] = out.pop("trace_raw")
    out["trace_raw"], out["date_lines"] = trace_without_date(Path(run_dir) / "evidence" / "trace.raw")
    return out


FIELDS = ("input_spice", "record", "result", "noise_sha256", "trace_raw")


def compare(d1, d2):
    a, b = comparable(d1), comparable(d2)
    out = dict(first=str(d1), second=str(d2), criterion="PREDICTION.md section 6: trace.raw without its Date: header line",
               fields={k: dict(first=a[k], second=b[k], equal=a[k] == b[k]) for k in FIELDS},
               trace_raw_full_equal=a["trace_raw_full"] == b["trace_raw_full"], date_lines=[a["date_lines"], b["date_lines"]])
    out["identical"] = all(v["equal"] for v in out["fields"].values()) and out["date_lines"] == [1, 1]
    return out


if __name__ == "__main__":
    r = compare(sys.argv[1], sys.argv[2])
    print(json.dumps(r, indent=1))
    sys.exit(0 if r["identical"] else 1)
