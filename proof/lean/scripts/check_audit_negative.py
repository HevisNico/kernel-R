#!/usr/bin/env python3
"""Audit controls for current and imported declarations in both project namespaces."""
from pathlib import Path
import subprocess
import tempfile

from lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[1]


def run(command, path, *, expected, diagnostic=None):
    result = subprocess.run([*command, str(path)], cwd=ROOT, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=120)
    if (result.returncode == 0) != expected or (diagnostic and diagnostic not in result.stdout):
        raise SystemExit(f'Audit control failed:\n{result.stdout}')


def main():
    # Reuse the exact audit implementation; only the import set is reduced for
    # these controls. The ordinary Audit target still imports the whole project.
    audit = (ROOT / 'Audit.lean').read_text()
    body = audit[audit.index('set_option maxHeartbeats'):]
    prefix = 'import Lean\nimport Lean.Util.CollectAxioms\n'
    good = '''theorem KernelR.AuditControl.good : True := True.intro
theorem A22.AuditControl.good : True := True.intro
'''
    bad_current = '''namespace A22.AuditCorruption
axiom forbidden : False
theorem proof : False := forbidden
end A22.AuditCorruption
'''
    bad_import = '''namespace KernelR.AuditCorruption
axiom forbidden : False
theorem proof : False := forbidden
end KernelR.AuditCorruption
'''
    with tempfile.TemporaryDirectory(prefix='audit-negative-', dir=ROOT) as tmp:
        directory = Path(tmp)
        path = directory / 'Check.lean'
        command = lean_check_command(directory)
        path.write_text(prefix + good + body)
        run(command, path, expected=True, diagnostic='Axiom audit passed: 2 project theorems')
        path.write_text(prefix + good + bad_current + body)
        run(command, path, expected=False, diagnostic='Unexpected axiom A22.AuditCorruption.forbidden')
        imported = directory / 'BadImported.lean'
        compiled = directory / 'BadImported.olean'
        imported.write_text(bad_import)
        run([*lean_check_command(directory, module_name='BadImported'), '-o', str(compiled)],
            imported, expected=True)
        command = lean_check_command(directory, extra_artifacts={'BadImported': [[str(compiled)]]})
        path.write_text('import BadImported\n' + prefix + good + body)
        run(command, path, expected=False, diagnostic='Unexpected axiom KernelR.AuditCorruption.forbidden')
    print('Audit: valid controls accepted; current and imported corruption rejected.', flush=True)


if __name__ == '__main__':
    main()
