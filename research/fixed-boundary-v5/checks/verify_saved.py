#!/usr/bin/env python3
"""Authenticate the authorized saved files, then run the frozen v5 verifier.

This wrapper never imports or launches the registered runner, regenerates
scenarios, rewrites evidence, or modifies the frozen source inventory.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parents[1]
AUTHORIZATION_COMMIT = 'f067f1cf1b2dc47ea33dcdf652995b2d794f10c4'
MANIFEST_PATH = 'research/fixed-boundary-v5/PENDING_EVIDENCE.json'
POSTRUN_PATH = 'research/fixed-boundary-v5/POSTRUN_CHECKS.json'
RAW_PREFIX = 'research/fixed-boundary-v5/run-v5/'
EXPECTED_COUNT = 50


class EvidenceError(RuntimeError):
    """The saved evidence does not match the immutable publication scope."""


def git(repo: Path, *args: str) -> bytes:
    try:
        return subprocess.check_output(['git', *args], cwd=repo, stderr=subprocess.PIPE)
    except subprocess.CalledProcessError as exc:
        raise EvidenceError('Git evidence lookup failed: '+exc.stderr.decode(errors='replace').strip()) from exc


def _unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise EvidenceError('Duplicate JSON key: '+key)
        result[key] = value
    return result


def decode_json(data: bytes):
    try:
        return json.loads(data, object_pairs_hook=_unique_object)
    except (ValueError, UnicodeDecodeError) as exc:
        raise EvidenceError('Invalid evidence metadata JSON') from exc


def manifest_entries(document, expected_count=EXPECTED_COUNT):
    if (not isinstance(document, dict) or type(document.get('attempt')) is not int
            or document['attempt'] != 1):
        raise EvidenceError('Manifest must identify attempt 1')
    files = document.get('files')
    if not isinstance(files, list) or len(files) != expected_count:
        raise EvidenceError(f'Manifest must contain exactly {expected_count} files')
    entries = {}
    for item in files:
        if not isinstance(item, dict) or set(item) != {'path', 'bytes', 'sha256'}:
            raise EvidenceError('Malformed manifest entry')
        path, size, digest = item['path'], item['bytes'], item['sha256']
        if (not isinstance(path, str) or '\\' in path or '\x00' in path
                or not path.startswith(RAW_PREFIX)
                or PurePosixPath(path).is_absolute()
                or any(part in ('', '.', '..') for part in path.split('/'))
                or PurePosixPath(path).as_posix() != path):
            raise EvidenceError('Unsafe or noncanonical evidence path: '+repr(path))
        if path in entries:
            raise EvidenceError('Duplicate evidence path: '+path)
        if type(size) is not int or size < 0:
            raise EvidenceError('Invalid byte count: '+path)
        if not isinstance(digest, str) or re.fullmatch(r'[0-9a-f]{64}', digest) is None:
            raise EvidenceError('Invalid SHA256: '+path)
        entries[path] = item
    return entries


def disk_inventory(repo: Path):
    raw = repo / RAW_PREFIX.rstrip('/')
    # Reject symlinks in each parent as well as within the evidence directory.
    current = repo
    for part in PurePosixPath(RAW_PREFIX.rstrip('/')).parts:
        current /= part
        if current.is_symlink():
            raise EvidenceError('Symlink in evidence directory path')
    if not raw.is_dir():
        raise EvidenceError('Saved evidence directory is missing')
    found = set()
    for directory, dirs, files in os.walk(raw, followlinks=False):
        for name in dirs + files:
            path = Path(directory) / name
            if path.is_symlink():
                raise EvidenceError('Symlink in evidence inventory: '+str(path.relative_to(repo)))
            if name in files:
                if not path.is_file():
                    raise EvidenceError('Nonregular evidence entry: '+str(path.relative_to(repo)))
                found.add(path.relative_to(repo).as_posix())
    return found


def _require_bytes(data: bytes, item, location: str):
    if len(data) != item['bytes']:
        raise EvidenceError(location+' byte count differs: '+item['path'])
    if hashlib.sha256(data).hexdigest() != item['sha256']:
        raise EvidenceError(location+' SHA256 differs: '+item['path'])


def verify_saved_manifest(repo: Path, authorization_commit=AUTHORIZATION_COMMIT):
    """Read-only verification; commit override exists solely for temporary tests."""
    repo = Path(repo).resolve()
    if re.fullmatch(r'[0-9a-f]{40}', authorization_commit) is None:
        raise EvidenceError('Invalid authorization commit')
    authorized = manifest_entries(decode_json(git(repo, 'show', authorization_commit+':'+MANIFEST_PATH)))
    current = manifest_entries(decode_json((repo / MANIFEST_PATH).read_bytes()))
    # Ordering and a changed human-readable status do not alter the authorized
    # set; every path, size and SHA256 must equal the prior published manifest.
    if current != authorized:
        raise EvidenceError('Current manifest differs from the authorized file entries')
    found = disk_inventory(repo)
    if found != set(authorized):
        missing, extra = sorted(set(authorized)-found), sorted(found-set(authorized))
        raise EvidenceError('Evidence inventory differs; missing='+repr(missing)+' extra='+repr(extra))
    local = {}
    for path, item in authorized.items():
        local[path] = (repo/path).read_bytes()
        _require_bytes(local[path], item, 'Local')
    postrun = decode_json((repo/POSTRUN_PATH).read_bytes())
    if not isinstance(postrun, dict) or postrun.get('raw_evidence_committed') is not True:
        raise EvidenceError('POSTRUN_CHECKS does not confirm raw evidence publication')
    raw_commit = postrun.get('raw_evidence_commit')
    if not isinstance(raw_commit, str) or re.fullmatch(r'[0-9a-f]{40}', raw_commit) is None:
        raise EvidenceError('POSTRUN_CHECKS must identify the exact raw evidence commit')
    ancestry = git(repo, 'rev-list', '--parents', '-n', '1', raw_commit).decode().split()
    if ancestry != [raw_commit, authorization_commit]:
        raise EvidenceError('Raw evidence commit must have the authorized commit as its sole parent')
    git(repo, 'merge-base', '--is-ancestor', raw_commit, 'HEAD')
    changed = git(repo, 'diff-tree', '--no-commit-id', '--no-renames', '--name-status',
                  '-r', '-z', authorization_commit, raw_commit).split(b'\x00')
    if changed[-1:] == [b'']:
        changed.pop()
    if len(changed) != 2*EXPECTED_COUNT:
        raise EvidenceError('Dedicated raw commit must change exactly 50 files')
    additions = {}
    for index in range(0, len(changed), 2):
        status, path = changed[index:index+2]
        if status != b'A':
            raise EvidenceError('Dedicated raw commit contains a non-addition')
        name = path.decode('utf-8')
        if name in additions:
            raise EvidenceError('Duplicate path in raw commit changes')
        additions[name] = status
    if set(additions) != set(authorized):
        raise EvidenceError('Dedicated raw commit additions differ from authorized manifest')
    tree = git(repo, 'ls-tree', '-r', '-z', '--full-tree', raw_commit, '--', RAW_PREFIX.rstrip('/'))
    tree_paths = set()
    for entry in tree.split(b'\x00'):
        if not entry:
            continue
        header, name = entry.split(b'\t', 1)
        mode, kind, _blob = header.split()
        path = name.decode('utf-8')
        if mode != b'100644' or kind != b'blob':
            raise EvidenceError('Raw commit has nonregular evidence file: '+path)
        tree_paths.add(path)
    if tree_paths != set(authorized):
        raise EvidenceError('Raw commit evidence tree differs from manifest')
    for path, item in authorized.items():
        data = git(repo, 'show', raw_commit+':'+path)
        _require_bytes(data, item, 'Committed')
        if data != local[path]:
            raise EvidenceError('Local and dedicated-commit bytes differ: '+path)
    return dict(files=len(authorized), bytes=sum(item['bytes'] for item in authorized.values()),
                authorization_commit=authorization_commit, raw_evidence_commit=raw_commit)


def main():
    if len(sys.argv) != 1:
        raise EvidenceError('This saved-evidence wrapper takes no launch or regeneration arguments')
    result = verify_saved_manifest(REPO)
    print('PASS: exact authorized saved inventory, sizes, SHA256 and dedicated 50-addition commit', flush=True)
    print(json.dumps(result, sort_keys=True), flush=True)
    # Only the frozen read-only verifier is invoked. No runner, --preflight,
    # --report or experiment argument is accepted/passed by this wrapper.
    completed = subprocess.run([sys.executable, '-B', str(ROOT/'verify.py')], cwd=ROOT)
    return completed.returncode


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (EvidenceError, OSError) as exc:
        print('Saved evidence verification failed: '+str(exc), file=sys.stderr)
        sys.exit(1)
