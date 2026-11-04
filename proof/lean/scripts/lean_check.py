"""Reuse Lake's artifact paths for standalone positive/negative Lean controls.

This preserves the pinned compiler, imports and options. The setup map only
avoids repeating filesystem searches for thousands of dependency artifacts.
"""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def lean_check_command(directory, *, module_name='Check', extra_artifacts=None,
                       root_module='KernelR'):
    module_path = root_module.replace('.', '/')
    source = ROOT / f'.lake/build/ir/{module_path}.setup.json'
    if not source.is_file():
        raise SystemExit(f'Run lake build {root_module} before the standalone Lean controls.')
    setup = json.loads(source.read_text())
    setup['name'] = module_name
    setup['importArts'][root_module] = [[str(ROOT / f'.lake/build/lib/lean/{module_path}.olean')]]
    setup['importArts'].update(extra_artifacts or {})
    target = Path(directory) / f'{module_name}.setup.json'
    target.write_text(json.dumps(setup))
    return ['lake', 'env', 'lean', '--setup', str(target)]
