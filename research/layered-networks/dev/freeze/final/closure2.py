"""Closure of what the campaign runs, imports or reads, from entry scripts in research/layered-networks.
Follows: import statements anywhere (module-level or in functions) of modules in L or L/tests or L/noise4_gate; string
literals naming a .py/.json/.txt/.spice/.lean/.toml/.sh file that exists relative to L or to the repo top."""
import json, re, sys
from pathlib import Path
top = Path(sys.argv[1]); L = top / "research/layered-networks"
entries = sys.argv[2:]
mods = {}
for d in (L, L / "tests", L / "noise4_gate"):
    for p in d.glob("*.py"):
        mods.setdefault(p.stem, p)
seen, todo, why = set(), [L / e for e in entries], {}
for e in entries: why[str((L / e).relative_to(top))] = "entry"
lit = re.compile(r"""["']([\w./-]+\.(?:py|json|txt|spice|lean|toml|sh|lib))["']""")
while todo:
    p = todo.pop()
    if p in seen or not p.is_file():
        continue
    seen.add(p)
    if p.suffix != ".py":
        continue
    t = p.read_text()
    src = str(p.relative_to(top))
    names = re.findall(r"^\s*import\s+([\w, ]+?)(?:\s+as\s+\w+)?\s*(?:#.*)?$", t, re.M)
    ms = set()
    for n in names:
        for x in n.split(","):
            ms.add(x.strip().split(" ")[0])
    ms |= set(re.findall(r"^\s*from\s+(\w+)\s+import", t, re.M))
    for m in ms:
        q = mods.get(m)
        if q and q not in seen:
            why.setdefault(str(q.relative_to(top)), f"imported by {src}"); todo.append(q)
    for s in lit.findall(t):
        for base in (p.parent, L, top):
            q = (base / s)
            if q.is_file():
                q = q.resolve()
                if top.resolve() in q.parents:
                    r = str(q.relative_to(top.resolve()))
                    why.setdefault(r, f"named in {src}"); todo.append(top / r)
                break
print(json.dumps(dict(files=sorted(str(p.relative_to(top)) for p in seen), why=why), indent=1, sort_keys=True))
