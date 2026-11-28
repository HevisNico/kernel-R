import re, textwrap, sys
from pathlib import Path
L = Path(sys.argv[1]); src = (L / "dev/freeze/final/proof2.py").read_text()
text = (L / "FREEZE.txt").read_text().split("\n")
blocks, k = {}, 0
while k < len(text):
    m = re.fullmatch(r"\s*\[block ([a-z0-9-]+)\]\s*", text[k])
    if m:
        j = next(i for i in range(k + 1, len(text)) if text[i].strip() == "[end]")
        blocks[m.group(1)] = textwrap.dedent("\n".join(text[k + 1:j])) + "\n"; k = j
    k += 1
seg = src[src.index('PUSH = f"git push'):src.index("twins_md = [")]
ns = dict(GH="https://github.com/HevisNico/kernel-R", TWIN="/W/github_twin.git", W="/W", T1M="T", L="/L", PY="/PY", LOG="/LOG")
exec(seg, ns)
bad = 0
for name, tw in ns["TWINS"].items():
    for old, new, why in tw:
        n = blocks[name].count(old)
        print(f"{name}: {n}x  {old[:70]!r}")
        bad += n != 1
print("ALL TWINS APPLY ONCE" if not bad else f"{bad} TWINS DO NOT APPLY")
line = "the list is right 36 144 sha256 " + "a" * 64 + " scan_sha256 " + "b" * 64
for name in ("vars-campaign",):
    for old, new, why in ns["TWINS"][name]:
        print(new.replace("/LOG/08_check-list.out", "<<<").split("$(")[1])
