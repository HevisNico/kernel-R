"""Campaign 5's collector (PREDICTION.md, 10.7): campaign 4's collect_with_links.py (SHA-256 e3b13277...cdab2, reviewed
at d073110 and used in campaign 4's amendment 11), unchanged but for this docstring's first lines. The collection of a
kit evidence folder whose stopped runs left symbolic links, which the kit's `collect` refuses ("Evidence symlink cannot
be silently copied or omitted").

    collect.py OUT_DIR DESTINATION

- Every regular file of OUT_DIR is copied byte for byte to DESTINATION, at the same relative path; its SHA-256 is
  computed when read, the copy is read back and checked, and the source is read again and must be unchanged.
- Every symbolic link is recorded as text (its path and its target, from os.readlink), never followed, never copied
  as a link; nothing is copied for it.
- Directories are recreated as needed; empty directories are recorded.
- Anything else (fifo, socket, device) refuses the whole collection.
- DESTINATION/COLLECTED.json is the manifest, in place of the kit's SURVIVORS.json: the source folder, the kit state
  read from STATE.json, every file (path, bytes, sha256), every link (path, target), every empty directory, the
  SHA-256 of this script, and the rule.
- OUT_DIR is only read: nothing is written, moved or deleted in it. Before and after, the script takes a listing of
  OUT_DIR (every path, its type, the SHA-256 of each file and the target of each link, and each entry's size and
  mtime from lstat) and refuses if the two listings differ.
- It refuses if DESTINATION exists, if DESTINATION is inside OUT_DIR, or if STATE.json reads `running`.
"""
import hashlib
import json
import os
from pathlib import Path
import stat
import sys
from datetime import datetime, timezone


def sha(data):
    return hashlib.sha256(data).hexdigest()


def listing(root):
    out = []
    for p in sorted(root.rglob("*")):
        st = os.lstat(p)
        rel = p.relative_to(root).as_posix()
        if stat.S_ISLNK(st.st_mode):
            out.append((rel, "link", os.readlink(p), st.st_size, st.st_mtime_ns))
        elif stat.S_ISREG(st.st_mode):
            out.append((rel, "file", sha(p.read_bytes()), st.st_size, st.st_mtime_ns))
        elif stat.S_ISDIR(st.st_mode):
            out.append((rel, "dir", None, None, st.st_mtime_ns))
        else:
            raise SystemExit(f"refused: unsupported file type at {rel}")
    return out


def main():
    out, dest = Path(sys.argv[1]).resolve(), Path(sys.argv[2]).resolve()
    if not out.is_dir() or dest.exists() or dest.is_relative_to(out):
        raise SystemExit("refused: need an existing evidence folder and a new destination outside it")
    state = json.loads((out / "STATE.json").read_bytes()) if (out / "STATE.json").exists() else dict(status="unknown")
    if state.get("status") == "running":
        raise SystemExit("refused: the kit state reads running")
    before = listing(out)
    dest.mkdir(parents=True)
    files, links, empty = [], [], []
    for rel, kind, value, size, _ in before:
        src = out / rel
        if kind == "link":
            links.append(dict(path=rel, target=value))
        elif kind == "dir":
            if not any(os.scandir(src)):
                empty.append(rel)
            (dest / rel).mkdir(parents=True, exist_ok=True)
        else:
            data = src.read_bytes()
            if sha(data) != value:
                raise SystemExit(f"refused: {rel} changed during the collection")
            (dest / rel).parent.mkdir(parents=True, exist_ok=True)
            with open(dest / rel, "xb") as f:
                f.write(data)
            if sha((dest / rel).read_bytes()) != value:
                raise SystemExit(f"refused: the copy of {rel} differs")
            files.append(dict(path=rel, bytes=len(data), sha256=value))
    after = listing(out)
    if after != before:
        raise SystemExit("refused: the evidence folder changed during the collection")
    manifest = dict(source=str(out), kit_status=state.get("status"), files=files, links=links, empty_directories=empty,
                    collector=Path(__file__).name, collector_sha256=sha(Path(__file__).read_bytes()),
                    collected_utc=datetime.now(timezone.utc).isoformat(),
                    rule="every regular file copied byte for byte with its SHA-256; every symbolic link recorded as text "
                         "(path and target), never followed; the evidence folder only read, and checked unchanged")
    with open(dest / "COLLECTED.json", "x") as f:
        f.write(json.dumps(manifest, indent=1, sort_keys=True) + "\n")
    print(json.dumps(dict(files=len(files), links=len(links), empty_directories=len(empty), kit_status=state.get("status"))))


if __name__ == "__main__":
    main()
