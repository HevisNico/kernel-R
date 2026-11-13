"""Regenerate only exploratory traces from frozen sources; never touches v5."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parent
RESEARCH=ROOT.parent


def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    module=importlib.util.module_from_spec(spec)
    sys.modules[name]=module
    spec.loader.exec_module(module)
    return module


def manifest():
    data=json.loads((ROOT/'SHA256.json').read_text())
    for name,expected in data['source_sha256'].items():
        if hashlib.sha256((RESEARCH/name).read_bytes()).hexdigest()!=expected:
            raise ValueError('Frozen generator source changed: '+name)
    return data['files']


def generate(output):
    expected=manifest()
    output=Path(output)
    output.mkdir(parents=True,exist_ok=True)
    generated=set()
    def write(name,rows):
        data=json.dumps(rows,sort_keys=True).encode()
        if name not in expected or hashlib.sha256(data).hexdigest()!=expected[name]:
            raise ValueError('Regenerated trace fingerprint differs: '+name)
        path=output/name
        path.parent.mkdir(parents=True,exist_ok=True)
        path.write_bytes(data)
        generated.add(name)
    study=load('repro_frozen_boundary',RESEARCH/'boundary-cost-study/study.py')
    for hard in (140,150):
        for policy in study.POLICIES:
            _,rows=study.simulate(hard,policy)
            write(f'boundary/H{hard}-{policy}.json',rows)
    sweep=load('repro_frozen_sweep',RESEARCH/'economic-sweep/sweep.py')
    reference=sweep.reference(RESEARCH/'boundary-cost-study/study.py')
    grid=json.loads((RESEARCH/'economic-sweep/grid.json').read_text())
    for scenario in grid['scenarios']:
        for capacity in grid['capacities']:
            for policy in grid['policies']:
                _,rows=sweep.simulate(reference,capacity,scenario,policy,grid['horizon'])
                write(f'economic/{scenario}-C{capacity}-{policy}.json',rows)
    if generated!=set(expected):
        raise ValueError('Generator did not cover the exact manifest')
    verify(output)
    return len(generated)


def verify(output):
    expected=manifest()
    output=Path(output)
    actual={p.relative_to(output).as_posix() for p in output.rglob('*') if p.is_file()}
    if actual!=set(expected):
        raise ValueError('Missing or unexpected generated file')
    for name,digest in expected.items():
        if hashlib.sha256((output/name).read_bytes()).hexdigest()!=digest:
            raise ValueError('Generated-file SHA-256 mismatch: '+name)
    return len(expected)


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--verify-only',action='store_true')
    args=parser.parse_args()
    count=verify(args.output) if args.verify_only else generate(args.output)
    print(f'PASS: {count} exploratory trace fingerprints; no v5 scenario generated or replayed')


if __name__=='__main__':
    main()
