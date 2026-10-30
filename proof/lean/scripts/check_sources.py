#!/usr/bin/env python3
"""Check source hygiene and byte identity of the five inherited Lean modules.

The compiled axiom check in Audit.lean remains the authority on proof dependencies.
This lexical check is an additional guard, not a Lean parser or security sandbox.
"""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]


def without_comments(text):
    # Lean block comments may nest. Preserve newlines for useful diagnostics.
    out = []
    depth = 0
    i = 0
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1
            i += 2
        elif depth and text.startswith('-/', i):
            depth -= 1
            i += 2
        elif not depth and text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        else:
            out.append(text[i] if not depth or text[i] == '\n' else ' ')
            i += 1
    if depth:
        raise ValueError('unterminated block comment')
    return ''.join(out)


def main():
    paths = sorted(ROOT.glob('*.lean')) + sorted((ROOT / 'KernelR').rglob('*.lean'))
    banned = re.compile(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by|extern)\b')
    for path in paths:
        source = without_comments(path.read_text())
        # Ignore ordinary string literals, e.g. the diagnostic text in Audit.lean.
        source = re.sub(r'"(?:\\.|[^"\\])*"', '""', source)
        match = banned.search(source)
        if match:
            raise SystemExit(f'{path.relative_to(ROOT)}: forbidden token {match[0]}')
    upstream = json.loads((ROOT / 'evidence/UPSTREAM.json').read_text())
    for entry in upstream['files']:
        data = (ROOT / entry['local']).read_bytes()
        blob = b'blob ' + str(len(data)).encode() + b'\0' + data
        if hashlib.sha1(blob).hexdigest() != entry['git_blob_sha1']:
            raise SystemExit('upstream source differs: ' + entry['local'])
    print(f'Source checks passed: {len(paths)} Lean files, 5 unchanged upstream modules.')


if __name__ == '__main__':
    main()
