#!/usr/bin/env python3
"""Audit public/private, current/imported theorems in both project namespaces."""
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
    good_private = '''namespace KernelR.AuditControl
private theorem unused : True := True.intro
end KernelR.AuditControl
namespace A22.AuditControl
private theorem unused : True := True.intro
end A22.AuditControl
namespace OutsideAuditScope
private theorem unused : True := True.intro
end OutsideAuditScope
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
        path.write_text(prefix + good + good_private + body)
        run(command, path, expected=True, diagnostic='Axiom audit passed: 4 project theorems')
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

        imported = directory / 'GoodPrivateImported.lean'
        compiled = imported.with_suffix('.olean')
        imported.write_text(good_private)
        run([*lean_check_command(directory, module_name=imported.stem), '-o', str(compiled)],
            imported, expected=True)
        command = lean_check_command(directory, extra_artifacts={imported.stem: [[str(compiled)]]})
        path.write_text(f'import {imported.stem}\n' + prefix + good + body)
        run(command, path, expected=True, diagnostic='Axiom audit passed: 4 project theorems')

        # These private theorems are deliberately unused by every public
        # theorem. Transitive checks of public proofs alone cannot find them.
        # Exercise each namespace, location and kind of forbidden dependency.
        for namespace in ('KernelR', 'A22'):
            for label, proof, diagnostic in (
                ('Axiom', 'private theorem unused : False := OutsideAuditScope.forbidden\n',
                 'Unexpected axiom OutsideAuditScope.forbidden'),
                ('Sorry', 'private theorem unused : False := by sorry\n',
                 'Unexpected axiom sorryAx'),
            ):
                bad_private = ('axiom OutsideAuditScope.forbidden : False\n'
                               f'namespace {namespace}.AuditCorruption\n{proof}end {namespace}.AuditCorruption\n')
                command = lean_check_command(directory)
                path.write_text(prefix + good + bad_private + body)
                run(command, path, expected=False, diagnostic=diagnostic)
                module = f'{namespace}Private{label}'
                imported = directory / f'{module}.lean'
                compiled = imported.with_suffix('.olean')
                imported.write_text(bad_private)
                run([*lean_check_command(directory, module_name=module), '-o', str(compiled)],
                    imported, expected=True)
                command = lean_check_command(directory, extra_artifacts={module: [[str(compiled)]]})
                path.write_text(f'import {module}\n' + prefix + good + body)
                run(command, path, expected=False, diagnostic=diagnostic)

            for visibility in ('', 'private '):
                isolated = f'namespace {namespace}.AuditCorruption\n{visibility}axiom unused : False\nend {namespace}.AuditCorruption\n'
                command = lean_check_command(directory)
                path.write_text(prefix + good + isolated + body)
                run(command, path, expected=False, diagnostic='Unexpected axiom')
                module = f'{namespace}Isolated' + ('Private' if visibility else 'Public')
                imported = directory / f'{module}.lean'
                compiled = imported.with_suffix('.olean')
                imported.write_text(isolated)
                run([*lean_check_command(directory, module_name=module), '-o', str(compiled)],
                    imported, expected=True)
                command = lean_check_command(directory, extra_artifacts={module: [[str(compiled)]]})
                path.write_text(f'import {module}\n' + prefix + good + body)
                run(command, path, expected=False, diagnostic='Unexpected axiom')
    print('Audit: valid public/private controls counted; public corruption and all 8 unused-private '
          'corruption controls rejected (both namespaces, current/imported, axiom/sorry); '
          'all 8 isolated-axiom controls rejected.', flush=True)


if __name__ == '__main__':
    main()
