#!/usr/bin/env python3
"""Export or freshness-check Lean's checked trusted-declaration metadata."""
import argparse
import json
from pathlib import Path
import subprocess
import tempfile

from lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[1]
DEFAULT = ROOT / 'evidence/trusted_base.json'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=DEFAULT)
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--print', action='store_true', dest='print_manifest')
    parser.add_argument('--actual-output', type=Path,
                        help='also preserve the fresh raw export, including in check mode')
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix='trusted-base-export-', dir=ROOT) as tmp:
        output = Path(tmp) / 'manifest.json'
        source = Path(tmp) / 'Check.lean'
        source.write_text('''import KernelR.TrustedBase
set_option maxHeartbeats 8000000
open Lean Elab Command in
run_cmd liftTermElabM do
  let data ← KernelR.TrustedBase.manifest
  IO.FS.writeFile OUTPUT data.pretty
'''.replace('OUTPUT', json.dumps(str(output))))
        command = lean_check_command(tmp, root_module='KernelR.TrustedBase')
        result = subprocess.run([*command, str(source)], cwd=ROOT, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=300)
        if result.returncode:
            raise SystemExit('Lean trusted-base export failed:\n' + result.stdout)
        actual = json.loads(output.read_text())
    if args.check:
        expected = json.loads(args.output.read_text())
        expected = {key: value for key, value in expected.items()
                    if key not in {'sources', 'code_commit'}}
        if actual != expected:
            raise SystemExit('Trusted-base metadata differs from a fresh checked Lean export.')
    else:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(actual, indent=2, ensure_ascii=False) + '\n')
    if args.actual_output:
        args.actual_output.parent.mkdir(parents=True, exist_ok=True)
        args.actual_output.write_text(json.dumps(actual, indent=2, ensure_ascii=False) + '\n')
    if args.print_manifest:
        print('TRUSTED_BASE_MANIFEST=' + json.dumps(actual, ensure_ascii=False))
    print(f'Trusted metadata {"checked" if args.check else "exported"}: '
          f'{len(actual["trusted"])} declarations.', flush=True)


if __name__ == '__main__':
    main()
