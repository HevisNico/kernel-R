"""Campaign 4, amendment 8: the structural comparison of two JSON files of the gate (CASES.json, MUTATIONS.json), for a
CI runner without AVX-512, where OpenBLAS cannot run the SkylakeX kernel the committed files were written with.

    structural_compare.py GENERATED.json COMMITTED.json

Every integer, string, Boolean and null must be exactly equal (rationals are strings), every list and object have the
same length and keys in the same order, and each number of the same type; only floats, the reported values
(np.polyfit's fits), may differ: math.isclose with rel_tol=1e-9 and abs_tol=1e-15, set after the test under the
Haswell kernel (largest relative difference 2.68e-12, in validation_residual_M5.c). Exit 1 otherwise. On an AVX-512
machine check.sh compares these files byte for byte instead.
"""
import json
import math
import sys

REL, ABS = 1e-9, 1e-15


def walk(a, b, path, out):
    if type(a) is not type(b):
        out["mismatch"].append(f"{path}: {type(a).__name__} against {type(b).__name__}")
    elif isinstance(a, dict):
        if list(a) != list(b):
            out["mismatch"].append(f"{path}: keys {list(a)} against {list(b)}")
        else:
            for k in a:
                walk(a[k], b[k], f"{path}.{k}", out)
    elif isinstance(a, list):
        if len(a) != len(b):
            out["mismatch"].append(f"{path}: length {len(a)} against {len(b)}")
        else:
            for i, (x, y) in enumerate(zip(a, b)):
                walk(x, y, f"{path}[{i}]", out)
    elif isinstance(a, float):
        out["floats"] += 1
        if a != b:
            out["floats_differing"] += 1
            rel = abs(a - b) / max(abs(a), abs(b))
            out["largest_relative"] = max(out["largest_relative"], rel)
            if not math.isclose(a, b, rel_tol=REL, abs_tol=ABS):
                out["mismatch"].append(f"{path}: {a!r} against {b!r} (relative {rel:.3g})")
    elif a != b:
        out["mismatch"].append(f"{path}: {a!r} against {b!r}")
    else:
        out["exact"] += 1


def main():
    generated, committed = sys.argv[1:3]
    out = dict(exact=0, floats=0, floats_differing=0, largest_relative=0.0, mismatch=[])
    walk(json.load(open(generated)), json.load(open(committed)), "$", out)
    print(f"structural comparison of {committed}: {out['exact']} exact values equal, {out['floats']} floats, "
          f"{out['floats_differing']} differing, largest relative difference {out['largest_relative']:.3g} (tolerance rel {REL}, abs {ABS})")
    if out["mismatch"]:
        print("\n".join(out["mismatch"][:20]), file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
