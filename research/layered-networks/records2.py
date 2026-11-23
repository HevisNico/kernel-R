"""Loading an instrumented record with records.py's same-edge rule, plus the repeat rule v2 (development only).

Repeat rule v2 (supersedes instrument.ScanCell._close, which is pushed and kept as it is):
- A group's repeats are the two reads made after its bracket [L0, U0] closed: L read again after a FIRE, U after a
  silence.
- If every repeat gives its end's outcome (L silent, U firing), the bracket is L = the largest silence and U = the
  smallest FIRE over L0, U0 and the repeats (v1, unchanged).
- If any repeat gives the opposite outcome, the state is disputed. The bracket is the envelope of the end reads, from
  the least to the largest of L0, U0 and the repeats' measured states, and repeats_agree is false.
Why: v1 judged agreement by the measured states only, so a repeat of U that landed 0.00002 stage below U0 and read
silent narrowed the bracket to +-0.00001 (XOR3 c1_0 on 9803) where the cell had, in substance, fired and stayed silent
at the same state. v2 keys disagreement on the outcome at the end.
Every group so changed is listed in rec["repeat_rule_v2"] with its v1 and v2 brackets. The record file is unchanged.
"""
from fractions import Fraction as F
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import records  # noqa: E402


def close_v2(g):
    if not g.get("ok") or not g.get("repeats") or not g.get("bracket_before_repeats"):
        return None
    L0, U0 = (F(x) for x in g["bracket_before_repeats"])
    reps = g["repeats"]
    agree = all(r["fired"] == (r["end"] == "U") for r in reps)
    if agree:
        lo = max([L0] + [F(r["s"]) for r in reps if not r["fired"]])
        hi = min([U0] + [F(r["s"]) for r in reps if r["fired"]])
    else:
        ends = [L0, U0] + [F(r["s"]) for r in reps]
        lo, hi = min(ends), max(ends)
    new = dict(s_star=str((lo + hi) / 2), half_bracket=str((hi - lo) / 2), bracket=[str(lo), str(hi)],
               repeats_agree=agree, consistent=agree)
    if any(g.get(k) != v for k, v in new.items()):
        before = dict(bracket=g["bracket"], repeats_agree=g.get("repeats_agree"))
        g.update(new)
        return dict(group=g["group"], v1=before, v2=dict(bracket=new["bracket"], repeats_agree=agree))
    return None


def load(outdir):
    rec = records.load(outdir)
    changed = []
    sc = rec.get("scans") or {}
    for part, cells in (("parallel", sc.get("cells") or {}), ("solo", (sc.get("solo") or {}).get("cells") or {})):
        for c, res in cells.items():
            for g in res:
                ch = close_v2(g)
                if ch:
                    changed.append(dict(part=part, cell=c, **ch))
    rec["repeat_rule_v2"] = changed
    return rec
