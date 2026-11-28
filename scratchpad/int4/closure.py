import re, sys, json
from pathlib import Path
L = Path(sys.argv[1])
entries = sys.argv[2:]
mods = {p.stem: p for p in L.glob("*.py")}
tmods = {p.stem: p for p in (L / "tests").glob("*.py")}
seen, todo, data = set(), [L / e for e in entries], set()
while todo:
    p = todo.pop()
    if p in seen or not p.exists():
        continue
    seen.add(p)
    t = p.read_text()
    for m in re.findall(r"^\s*(?:import|from)\s+([A-Za-z_]\w*)", t, re.M) + re.findall(r"import\s+([A-Za-z_]\w*)\s+as\s+\w+\s+#", t):
        q = mods.get(m) or (tmods.get(m) if p.parent.name == "tests" else None)
        if q: todo.append(q)
    for m in re.findall(r"""["']([\w./-]+\.(?:json|spice|txt|lib))["']""", t):
        data.add(m)
print(json.dumps(dict(py=sorted(str(p.relative_to(L)) for p in seen), data=sorted(data)), indent=0))
