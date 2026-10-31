"""Reuse Lake's artifact paths for standalone positive/negative Lean controls.

This preserves the pinned compiler, imports and options. The setup map only
avoids repeating filesystem searches for thousands of dependency artifacts.
"""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def lean_check_command(directory, *, module_name='Check', extra_artifacts=None):
    source = ROOT / '.lake/build/ir/KernelR.setup.json'
    if not source.is_file():
        raise SystemExit('Run lake build before the standalone Lean controls.')
    setup = json.loads(source.read_text())
    setup['name'] = module_name
    setup['importArts']['KernelR'] = [[str(ROOT / '.lake/build/lib/lean/KernelR.olean')]]
    setup['importArts'].update(extra_artifacts or {})
    target = Path(directory) / f'{module_name}.setup.json'
    target.write_text(json.dumps(setup))
    return ['lake', 'env', 'lean', '--setup', str(target)]
