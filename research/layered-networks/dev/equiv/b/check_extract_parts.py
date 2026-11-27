"""Equivalence test (b), a record helper: the split trace extracts of one instance against the reference's.

  check_extract_parts.py OUT.json NEW_INSTANCE_DIR REF_INSTANCE_DIR

For every round folder N<n>/extract holding trace.raw.part-NNN files (traces over 50 MB are split), on both sides:
  - each part: byte-identical, and identical once the first "Date: ..." line is removed (check_duplicate's only raw
    exception; it can only occur in part-000, which holds the header);
  - the parts concatenated in order (the whole trace): its length on both sides, and identical once the first Date:
    line is removed.
tests/equiv_b.py compares files ending in trace.raw with raw_compare, but the split parts fall to a byte compare; this
helper is the record of what those differences are. It changes nothing and is not part of the campaign's code.
Exit 0 if every part and every whole trace is identical except the Date: line.
"""
import hashlib
import json
import re
import sys
from pathlib import Path

DATE = re.compile(rb"Date: [^\n]*\n")


def no_date(b):
    return DATE.sub(b"", b, count=1)


def main(outp, new, ref):
    new, ref = Path(new), Path(ref)
    out = dict(format="layered-equiv-b-extract-parts/1", script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
               new=str(new), ref=str(ref), rounds={})
    ok = True
    for d in sorted(new.glob("N*/extract")):
        n = d.parent.name
        pa = sorted(d.glob("trace.raw.part-*"))
        pb = sorted((ref / n / "extract").glob("trace.raw.part-*"))
        r = dict(parts_new=[p.name for p in pa], parts_ref=[p.name for p in pb], parts={})
        if [p.name for p in pa] != [p.name for p in pb]:
            r["same_part_names"] = False
            ok = False
        for a in pa:
            b = ref / n / "extract" / a.name
            if not b.exists():
                continue
            x, y = a.read_bytes(), b.read_bytes()
            r["parts"][a.name] = dict(bytes_identical=x == y, identical_without_date_line=no_date(x) == no_date(y))
            ok = ok and r["parts"][a.name]["identical_without_date_line"]
        wa = b"".join(p.read_bytes() for p in pa)
        wb = b"".join(p.read_bytes() for p in pb)
        r["whole"] = dict(length_new=len(wa), length_ref=len(wb), identical_without_date_line=no_date(wa) == no_date(wb),
                          date_line_new=(DATE.search(wa).group().decode().strip() if DATE.search(wa) else None),
                          date_line_ref=(DATE.search(wb).group().decode().strip() if DATE.search(wb) else None))
        ok = ok and r["whole"]["identical_without_date_line"]
        out["rounds"][n] = r
    out["all_identical_except_date_line"] = ok and bool(out["rounds"])
    Path(outp).write_text(json.dumps(out, indent=1, sort_keys=True) + "\n")
    print("identical except the Date: line" if out["all_identical_except_date_line"] else "DIFFERS", len(out["rounds"]), "rounds")
    return out["all_identical_except_date_line"]


if __name__ == "__main__":
    sys.exit(0 if main(*sys.argv[1:]) else 1)
