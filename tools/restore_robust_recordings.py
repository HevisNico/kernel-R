"""Restore the two available historical robust traces to a fresh directory."""
import argparse
import hashlib
import io
import json
from pathlib import Path
import subprocess
import tempfile
from urllib.request import urlopen
import zipfile

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = Path(__file__).with_name('robust_recordings.json')


def restore(archive, destination):
    manifest = json.loads(MANIFEST.read_text())
    destination = Path(destination).resolve()
    if destination.exists():
        raise ValueError('Choose a fresh --out directory; existing records are never replaced')
    if hashlib.sha256(archive).hexdigest() != manifest['archive_sha256']:
        raise ValueError('Robust archive SHA-256 differs from the pinned release asset')
    # Authenticate all inputs before creating any output. Read just the pinned
    # entries rather than extracting archive paths into the filesystem.
    records = {}
    with zipfile.ZipFile(io.BytesIO(archive)) as zipped:
        for campaign, entry in manifest['available'].items():
            trace = zipped.read(entry['entry'])
            if hashlib.sha256(trace).hexdigest() != entry['trace_sha256']:
                raise ValueError(f'Trace hash mismatch: {campaign}')
            result = subprocess.run(['git', 'show', f"{manifest['source_ref']}:{entry['report']}"],
                                    cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            if result.returncode:
                raise ValueError(f"Fetch historical commit {manifest['source_ref']} before restoring")
            report = result.stdout
            if json.loads(report)['trace_sha256'] != entry['trace_sha256']:
                raise ValueError(f'Historical report/trace mismatch: {campaign}')
            records[campaign] = (report, trace)
    destination.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='.robust-restore-', dir=destination.parent) as tmp:
        staged = Path(tmp) / 'records'
        staged.mkdir()
        for campaign, (report, trace) in records.items():
            folder = staged / campaign
            folder.mkdir()
            (folder / 'validation.json').write_bytes(report)
            (folder / 'traces.jsonl.gz').write_bytes(trace)
        (staged / 'RESTORED.json').write_text(json.dumps(manifest, indent=2) + '\n')
        if destination.exists():
            raise ValueError('Output appeared during restoration; refusing to replace it')
        staged.rename(destination)
    return dict(restored=list(records), unavailable=manifest['unavailable_in_this_archive'],
                source_ref=manifest['source_ref'], output=str(destination))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--archive', type=Path, help='Local robust_n_cells_tested.zip; otherwise download the pinned asset')
    parser.add_argument('--out', type=Path, required=True, help='Fresh directory, with local/ and periodic/ record pairs')
    args = parser.parse_args()
    try:
        if args.out.exists():
            raise ValueError('Choose a fresh --out directory; existing records are never replaced')
        if args.archive:
            archive = args.archive.read_bytes()
        else:
            manifest = json.loads(MANIFEST.read_text())
            with urlopen(manifest['archive_url'], timeout=60) as response:
                archive = response.read()
        print(json.dumps(restore(archive, args.out)))
    except (ValueError, OSError, zipfile.BadZipFile, KeyError) as error:
        parser.exit(1, f'{error}\n')


if __name__ == '__main__':
    main()
