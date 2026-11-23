"""The layered deck against the family's deck, cell for cell: python3 -B tests/test_deck_identity.py

The family deck is network-circuit/net.py deck(cells, section='tt_mm', leak_per_port=True) (junction areas by default,
as campaign 5's run4.py calls it), rewritten to the family's design point as batch2x.py does it (vhi=0.7 on its .param
line, reltol=1e-5 on its .option line; dosedev.rewrite / dosedev_tol.rewrite). net.py is imported read-only, for the
comparison only. Checked, for every R cell of each spec:
  1. the cell's flattened element lines (every line whose name lies under x<cell>.) are identical, as a list, in order;
  2. the cell's stimulus sources (vinit, vks, vkr, vkp, vts, vamp) are identical; the per-port leak source vgl is
     the one stated difference (pulse at 0 V here, dc 0 there; 0 V in both outside a scan);
  3. every .lib, .param and .option line of the deck is identical, and the design point is the family's.
The inverters exist only in the layered deck; they are reported, not compared.
"""
import json
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(HERE))
sys.path.insert(1, str(HERE.parent / "network-circuit"))
import deck as deckmod  # noqa: E402
import instrument  # noqa: E402
import net  # noqa: E402  (family deck generator, frozen, read only)
import spec as specmod  # noqa: E402

CFG = json.loads((HERE / "config.json").read_text())


def family(cells):
    text = net.deck(cells=tuple(cells), section="tt_mm", leak_per_port=True)
    return instrument.rewrite(text, {"vhi": "0.7"}, {"reltol": "1e-5"})


def cell_lines(text, c):
    out = []
    for l in text.splitlines():
        tok = l.split()
        if not tok or tok[0].startswith(("*", ".")):
            continue
        name = tok[0]
        if f"x{c}." in name or re.match(rf"^(v(init|ks|kr|kp|ts|amp|gl)){c}[12]$", name) or name == f"x{c}":
            out.append(l.strip())
    return out


def directives(text):
    return [l.strip() for l in text.splitlines() if l.startswith((".lib", ".param", ".option"))]


def check(name):
    s = specmod.load(HERE / "specs" / f"{name}.json")
    cells, invs = deckmod.names(s)
    mine, fam = instrument.deck_text(s, CFG), family(cells)
    assert directives(mine) == directives(fam), (name, set(directives(mine)) ^ set(directives(fam)))
    assert any("vhi=0.7" in l for l in directives(mine)) and any("reltol=1e-5" in l for l in directives(mine))
    n = 0
    for c in cells:
        a, b = cell_lines(mine, c), cell_lines(fam, c)
        # the one known difference, in the stimulus and not in the cell: the per-port leak source is a pulse at 0 V
        # (a scan sets its window) where the family's is dc 0 (its scans alter the dc value while stopped). Both are
        # 0 V outside a scan; nothing else may differ.
        for p in (1, 2):
            ours, theirs = f"vglc{c[1:]}{p}".replace("vglc", f"vgl{c[0]}"), None
            la = [x for x in a if x.startswith(f"vgl{c}{p} ")]
            lb = [x for x in b if x.startswith(f"vgl{c}{p} ")]
            assert la == [f"vgl{c}{p} gl{c}{p} 0 pulse(0 0 1 1n 1n 1u 2)"] and lb == [f"vgl{c}{p} gl{c}{p} 0 dc 0"], (la, lb)
        a = [x for x in a if not x.startswith(f"vgl{c}")]
        b = [x for x in b if not x.startswith(f"vgl{c}")]
        assert a == b, (name, c, [x for x in a if x not in b][:3], [x for x in b if x not in a][:3])
        assert sum(1 for l in a if " ad=" in l) == 232, (name, c)
        n += len(a)
    inv = sum(1 for l in mine.splitlines() if l.split() and any(f"x{x}." in l.split()[0] for x in invs))
    return len(cells), n, inv


def test_identity():
    for name in ("not1", "andor3", "xor3"):
        cells, lines, inv = check(name)
        print(f"ok {name}: {cells} R cells, {lines} element lines identical to the family deck; {inv} inverter lines (not compared)")


if __name__ == "__main__":
    test_identity()
    print("deck identity holds")
