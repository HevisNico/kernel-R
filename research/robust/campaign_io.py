"""Publish new numerical campaigns without replacing archived evidence."""
import argparse
from contextlib import contextmanager
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile
import uuid

REPOSITORY = Path(__file__).resolve().parents[2]


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


@contextmanager
def publish_run(destination, *, campaign, verify, quick=False):
    """Stage a complete run next to a fresh destination, then rename it once."""
    destination = Path(destination).resolve()
    if destination.exists():
        raise ValueError(f'Output already exists; choose a fresh --out directory: {destination}')
    destination.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix=f'.{destination.name}-', dir=destination.parent) as tmp:
        staged = Path(tmp) / 'campaign'
        staged.mkdir()
        try:
            yield staged
            report = json.loads((staged / 'validation.json').read_text())
            if not report.get('status', '').startswith('PASS'):
                raise ValueError('Only a successfully validated campaign may be published')
            report['publication'] = dict(schema_version=1, campaign=campaign, quick=quick)
            (staged / 'validation.json').write_text(json.dumps(report, indent=2) + '\n')
            manifest = dict(schema_version=1, files={name: sha256(staged / name)
                            for name in ('validation.json', 'traces.jsonl.gz')})
            (staged / 'MANIFEST.json').write_text(json.dumps(manifest, indent=2) + '\n')
            verify(staged)
            if destination.exists():
                raise ValueError(f'Output appeared during the run; refusing to replace it: {destination}')
            staged.rename(destination)
        except BaseException as error:
            # A failed attempt is separate from every previously published run.
            failure = destination.with_name(destination.name + f'.FAILED-{uuid.uuid4().hex}.json')
            failure.write_text(json.dumps(dict(status='FAILED', campaign=campaign, quick=quick,
                               output=str(destination), error_type=type(error).__name__, error=str(error),
                               time_utc=datetime.now(timezone.utc).isoformat()), indent=2) + '\n')
            raise
    print(f'Published complete campaign: {destination}', flush=True)


def _historical_bytes(ref, path):
    if not re.fullmatch(r'[0-9a-f]{40}', ref):
        raise ValueError('--source-ref must be a full 40-character commit SHA')
    path = Path(path).resolve()
    if not path.is_relative_to(REPOSITORY):
        raise ValueError('Historical source escapes the repository')
    result = subprocess.run(['git', 'show', f'{ref}:{path.relative_to(REPOSITORY).as_posix()}'],
                            cwd=REPOSITORY, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if result.returncode:
        raise ValueError(f'Historical source unavailable; fetch commit {ref} before verifying')
    return result.stdout


def verify_record(directory, here, sources, environment, *, source_ref=None):
    directory, here = Path(directory), Path(here)
    report_path, trace = directory / 'validation.json', directory / 'traces.jsonl.gz'
    if not report_path.is_file() or not trace.is_file():
        raise ValueError('Record incomplete: validation.json and traces.jsonl.gz are both required. '
                         'See research/robust/RECORDINGS.md for authenticated restoration and fresh --out runs.')
    report = json.loads(report_path.read_text())
    if not report.get('status', '').startswith('PASS'):
        raise ValueError('Record is not a successful campaign')
    if sha256(trace) != report['trace_sha256']:
        raise ValueError('Trace hash differs from the validation report')
    if source_ref:
        if report_path.read_bytes() != _historical_bytes(source_ref, here / 'evidence/validation.json'):
            raise ValueError('Report differs from the declared historical commit')
        for name, expected in report['source_sha256'].items():
            if hashlib.sha256(_historical_bytes(source_ref, here / name)).hexdigest() != expected:
                raise ValueError(f'Historical source mismatch: {name}')
    elif report['source_sha256'] != sources:
        raise ValueError('Source manifest mismatch; use the recorded checkout for a historical report '
                         'or --source-ref with its full commit SHA. A new run needs a fresh --out directory.')
    if report['environment'] != environment:
        raise ValueError('Runtime versions differ from the recorded environment')
    manifest_path = directory / 'MANIFEST.json'
    if report.get('publication') and not manifest_path.is_file():
        raise ValueError('Published campaign is missing MANIFEST.json')
    if manifest_path.is_file():
        manifest = json.loads(manifest_path.read_text())
        expected = {name: sha256(directory / name) for name in ('validation.json', 'traces.jsonl.gz')}
        if manifest != dict(schema_version=1, files=expected):
            raise ValueError('Published campaign manifest mismatch')
    return report


def main(runner, here, sources, environment, *, supports_quick=False):
    parser = argparse.ArgumentParser(description='Write a fresh campaign, or verify an existing record without rerunning it.')
    parser.add_argument('--out', type=Path, help='Fresh output directory for a run; record directory when verifying')
    parser.add_argument('--verify-record', action='store_true')
    parser.add_argument('--source-ref', help='Full commit SHA for an unchanged historical report and its sources')
    if supports_quick:
        parser.add_argument('--quick', action='store_true')
    args = parser.parse_args()
    if args.source_ref and not args.verify_record:
        parser.error('--source-ref is only valid with --verify-record')
    try:
        if args.verify_record:
            if supports_quick and args.quick:
                parser.error('--quick selects a new run, not record verification')
            verify_record(args.out or here / 'evidence', here, sources(), environment(), source_ref=args.source_ref)
            print('PASS: record source/runtime/trace correspondence (not a rerun)')
        else:
            if args.out is None:
                parser.error('--out is required; choose a fresh directory to preserve archived evidence')
            runner(args.out, **({'quick': args.quick} if supports_quick else {}))
    except (ValueError, OSError) as error:
        parser.exit(1, f'{error}\n')
