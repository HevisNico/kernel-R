# Independent check of the spacing to wide metal3 and metal4 (rules m3.3 and m4.5 of SKY130).
#
#   klayout -b -r wide_metal_check.py -rd input=rcell.gds
#
# The deck of the PDK (sky130A.lydrc) splits each layer into its parts wider than 3 um and the rest,
# and reports the two wherever they are nearer than 0.4 um. A wire attached to a plate touches the
# plate, so the deck reports every such junction. This script asks the question of the rule itself
# (met3.3c/d and met4.5a/b: 0.4 um between a feature wider than 3 um, with what is attached to it
# within 0.28 um, and the other metal of the layer): is such a wide part nearer than 0.4 um to
# another polygon, or to another wide part? Polygons are merged over the whole hierarchy first.
import pya

ly = pya.Layout()
ly.read(input)                                      # noqa: F821  (given with -rd)
top = ly.top_cell()
dbu = ly.dbu
total = 0
for name, layer in (("metal3", 70), ("metal4", 71)):
    m = pya.Region(top.begin_shapes_rec(ly.layer(layer, 20)))
    m.merge()
    half = int(round(1.5 / dbu))
    wide = m.sized(-half).sized(half)
    huge = m.interacting(wide)
    rest = m - huge
    zone = wide.sized(int(round(0.28 / dbu))) & m       # the wide part and what is attached within 0.28 um
    d = int(round(0.4 / dbu))
    va, vb, vc = zone.separation_check(rest, d), zone.isolated_check(d), zone.notch_check(d)
    a, b, c = va.count(), vb.count(), vc.count()
    for pair in list(va.each())[:5] + list(vb.each())[:5] + list(vc.each())[:5]:
        print("   at", pair.bbox().to_s())
    total += a + b + c
    print(f"WIDE {name}: polygons {m.count()}, with a part wider than 3 um {huge.count()}; "
          f"nearer than 0.4 um to another polygon: {a + b}; notches below 0.4 um: {c}")
print("WIDE_TOTAL", total)
