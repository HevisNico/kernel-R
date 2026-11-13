"""Number of violations in a KLayout report database, by rule."""
import collections, sys
import xml.etree.ElementTree as ET
root = ET.parse(sys.argv[1]).getroot()
items = collections.Counter(i.find("category").text.strip("'") for i in root.find("items"))
print("KLAYOUT_COUNT", sum(items.values()), " ".join(f"{k}:{v}" for k, v in sorted(items.items())))
