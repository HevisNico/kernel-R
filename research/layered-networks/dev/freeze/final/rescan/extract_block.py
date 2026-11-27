"""Print one [block NAME] ... [end] of FREEZE.txt, extracted by proof2.py's own rule (the lines between the two
markers, dedented, plus a final newline):  python extract_block.py FREEZE.txt NAME"""
import re
import sys
import textwrap

text = open(sys.argv[1]).read().split("\n")
name, found, k = sys.argv[2], [], 0
while k < len(text):
    m = re.fullmatch(r"\s*\[block ([a-z0-9-]+)\]\s*", text[k])
    if m:
        j = next(i for i in range(k + 1, len(text)) if text[i].strip() == "[end]")
        if m.group(1) == name:
            found.append(textwrap.dedent("\n".join(text[k + 1:j])) + "\n")
        k = j
    k += 1
if len(found) != 1:
    sys.exit(f"REFUSED: [block {name}] found {len(found)} times in {sys.argv[1]}")
sys.stdout.write(found[0])
