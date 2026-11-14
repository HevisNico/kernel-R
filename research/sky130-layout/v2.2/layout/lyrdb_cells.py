"""Violations in a KLayout report database, by rule and by the cell they are reported in.
For the two rules of spacing to wide metal, also how many reports are two edges that touch:
on one line and overlapping, at distance zero."""
import collections
import re
import sys
import xml.etree.ElementTree as ET

root = ET.parse(sys.argv[1]).getroot()
count = collections.Counter()
touching = collections.Counter()
for item in root.find("items"):
    rule = item.find("category").text.strip("'")
    count[(rule, item.find("cell").text)] += 1
    if rule in ("m3.3ab", "m4.5ab"):
        x1, y1, x2, y2, x3, y3, x4, y4 = [float(v) for v in re.findall(r"-?\d+\.?\d*", item.find("values").find("value").text)]
        along_x = y1 == y2 == y3 == y4 and max(min(x1, x2), min(x3, x4)) <= min(max(x1, x2), max(x3, x4))
        along_y = x1 == x2 == x3 == x4 and max(min(y1, y2), min(y3, y4)) <= min(max(y1, y2), max(y3, y4))
        touching[rule] += along_x or along_y
print("KLAYOUT_COUNT", sum(count.values()))
for (rule, cell), n in sorted(count.items()):
    print(f"KLAYOUT {rule} {cell} {n}")
for rule in ("m3.3ab", "m4.5ab"):
    print(f"KLAYOUT_TOUCHING {rule} {touching[rule]} of {sum(n for (r, _), n in count.items() if r == rule)}")
