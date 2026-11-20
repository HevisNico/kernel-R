"""Test (a) of GENERATOR_DESIGN.md 4.1: the generator, through the legacy adapter, writes the 7 committed reference
files byte for byte. The references and their JSON inputs are read from an extracted copy of the campaign-6 impl
branch (IMPL_ROOT, the root of a `git archive` of research/), and the frozen campaign-5 code is imported from it.

  python -I tests/test_legacy.py IMPL_ROOT [OUT_DIR]

Prints one line per reference and exits non-zero on any difference (the first differing byte is shown).
"""
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
import legacy  # noqa: E402
import spec  # noqa: E402

SOURCE_C6 = "the development batch's predictions (campaign 6)"   # predict6.gate_file's source string


def references(root):
    c5 = root / "research/learned-dnf-circuit-campaign-5"
    c6 = root / "research/learned-dnf-circuit-campaign-6/stages"
    out = []
    for stage, js in (("c1", "PREDICTED.json"), ("r3", "PREDICTED_RN.json")):
        for x in json.loads((c6 / stage / js).read_text())["instances"]:
            f = c6 / stage / f"Gate6_{x['seed']}.lean"
            if f.exists():
                out.append((f"{stage}/Gate6_{x['seed']}.lean", [dict(x, tag=str(x["seed"]))], SOURCE_C6, f))
    cases = json.loads((c5 / "expected/CASES.json").read_text())["cases"]
    out.append(("C5/expected/Gate5Cases.lean", cases, "CASES.json", c5 / "expected/Gate5Cases.lean"))
    return c5, out


def main():
    root = Path(sys.argv[1]).resolve()
    od = Path(sys.argv[2]) if len(sys.argv) > 2 else None
    c5, refs = references(root)
    bad = 0
    for name, xs, source, ref in refs:
        try:
            text = legacy.lean_file(xs, source, c5)
        except spec.SpecError as e:
            print(f"{name}: REFUSED by spec.load: {e}")
            bad += 1
            continue
        got, want = text.encode(), ref.read_bytes()
        if od:
            od.mkdir(parents=True, exist_ok=True)
            (od / name.replace("/", "_")).write_bytes(got)
        if got == want:
            print(f"{name}: identical ({len(want)} bytes, {len(xs)} instance(s))")
        else:
            bad += 1
            k = next((i for i, (a, b) in enumerate(zip(got, want)) if a != b), min(len(got), len(want)))
            print(f"{name}: DIFFERENT at byte {k} (got {len(got)}, want {len(want)}): got {got[max(0, k - 60):k + 60]!r} want {want[max(0, k - 60):k + 60]!r}")
    print(f"test (a): {len(refs) - bad} of {len(refs)} identical")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
