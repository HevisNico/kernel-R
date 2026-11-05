"""Compile paired Lean controls in batches without losing per-case rejection.

Every original example must elaborate. Each altered example must produce its
own semantic error inside its source block. Import, parser and missing-name
errors are rejected independently of Lean's exit status.
"""
from pathlib import Path
import re
import subprocess
import tempfile

from lean_check import lean_check_command


def run_batches(cases, prefix, suffix='', *, root_module='KernelR', root=None,
                timeout=120, extra_artifacts=None):
    """Accept (label, positive, negative) tuples, or dictionaries with those data.

    The report maps each mutated example to at least one source diagnostic of
    its own. ``maxErrors=0`` makes Lean elaborate every example in a large batch.
    """
    root = Path(root) if root is not None else Path(__file__).resolve().parents[1]
    controls = [case if isinstance(case, dict) else
                dict(name=case[0], good=case[1], bad=case[2]) for case in cases]
    prefix = prefix.rstrip() + '\nset_option maxErrors 0\n'
    with tempfile.TemporaryDirectory(prefix='family-batch-negative-', dir=root) as tmp:
        path = Path(tmp) / 'Check.lean'
        command = lean_check_command(tmp, root_module=root_module,
                                     extra_artifacts=extra_artifacts)
        for key, expected in [('good', True), ('bad', False)]:
            source = prefix
            blocks = []
            for case in controls:
                start = source.count('\n') + 1
                source += case[key].rstrip() + '\n\n'
                blocks.append((start, source.count('\n'), case['name']))
            source += suffix
            path.write_text(source)
            result = subprocess.run([*command, str(path)], cwd=root, text=True,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                    timeout=timeout)
            if expected:
                if result.returncode != 0:
                    raise SystemExit('Valid family batch failed:\n' + result.stdout)
                print(f'Accepted all {len(controls)} original examples.', flush=True)
                continue
            if result.returncode == 0:
                raise SystemExit('Altered family batch unexpectedly compiled.')
            if re.search(r'unknown (constant|identifier|tactic)|unexpected token|invalid syntax|'
                         r'invalid (field|dotted identifier)|failed to infer|'
                         r"don't know how to synthesize implicit|failed to synthesize|"
                         r'object file .* does not exist|unknown module prefix',
                         result.stdout, re.I):
                raise SystemExit('Nonsemantic batch rejection:\n' + result.stdout)
            diagnostics = list(re.finditer(r'^.*?:(\d+):(\d+): error:', result.stdout, re.M))
            if not diagnostics:
                raise SystemExit('Altered batch failed without source diagnostics:\n' + result.stdout)
            rejected = set()
            for diagnostic in diagnostics:
                line = int(diagnostic.group(1))
                owners = [name for first, last, name in blocks if first <= line <= last]
                if len(owners) != 1:
                    raise SystemExit(f'Error outside a negative control at line {line}:\n' + result.stdout)
                rejected.add(owners[0])
            missing = {case['name'] for case in controls} - rejected
            if missing:
                raise SystemExit('No individual semantic error for: ' + ', '.join(sorted(missing)) +
                                 '\n' + result.stdout)
            for case in controls:
                print(f'{case["name"]}: original accepted; own altered conclusion rejected.', flush=True)
    return [dict(case=case['name'], covers=case.get('covers', [case['name']]),
                 positive='accepted', mutation='rejected') for case in controls]


def check_batches(root, controls, *, imports, root_module, timeout=120):
    """Convenience wrapper for controls in the parametric family's namespace."""
    root = Path(root)
    extra = {module: [[str(root / '.lake/build/lib/lean' /
                            (module.replace('.', '/') + '.olean'))]]
             for module in imports if module != root_module}
    prefix = ''.join(f'import {module}\n' for module in imports)
    prefix += 'namespace KernelR.Family\nopen KernelR.Hybrid Set\n'
    return run_batches(controls, prefix, '\nend KernelR.Family\n', root=root,
                       root_module=root_module, timeout=timeout, extra_artifacts=extra)
