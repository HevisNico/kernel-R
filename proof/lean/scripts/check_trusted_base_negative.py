#!/usr/bin/env python3
"""Paired semantic controls for the trusted statement-closure checker.

Every original fixture must compile. Each mutation must then produce its own
Lean diagnostic containing the expected checker rejection, rather than an
unrelated parser, import, or missing-name error.
"""
import argparse
import json
from pathlib import Path
import subprocess
import tempfile

from lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[1]


def fixture(body, trusted, headline='headline'):
    return body + f'''
open Lean Elab Command in
run_cmd liftTermElabM do
  discard <| KernelR.TrustedBaseChecker.check `{{NAMESPACE}}.{headline} [{trusted}]
'''


def checker_cases():
    direct = 'def model : Nat := 0\ntheorem headline : model = 0 := rfl\n'
    nested = ('def inner : Nat := 0\ndef model : Nat := inner\n'
              'theorem headline : model = 0 := rfl\n')
    field = ('def bound : Nat := 1\nstructure Model where\n  count : Fin (bound + 1)\n'
             'theorem headline : Model → True := fun _ => True.intro\n')
    namespace = ('def Model : Nat := 0\ndef Model.unlisted : Nat := 0\n'
                 'theorem headline : Model.unlisted = 0 := rfl\n')
    auxiliary = ('def inner : Nat := 0\ndef model : Nat := 0\n'
                 'def model.match_1 : Nat := inner\n'
                 'theorem headline : model.match_1 = 0 := rfl\n')
    private = ('private def inner : Nat := 0\ndef model : Nat := inner\n'
               'theorem headline : model = 0 := rfl\n')
    proof_only = ('def implementation : Nat := 0\n'
                  'theorem headline : True := by\n'
                  '  have hidden : implementation = 0 := rfl\n  trivial\n')
    proof_in_type = ('def implementation : Nat := 0\n'
                     'theorem headline : implementation = 0 := rfl\n')
    return [
        ('direct needed name', fixture(direct, '`{NAMESPACE}.model'),
         fixture(direct, ''), 'Untrusted statement dependencies'),
        ('definition values', fixture(nested, '`{NAMESPACE}.inner, `{NAMESPACE}.model'),
         fixture(nested, '`{NAMESPACE}.model'), 'Untrusted statement dependencies'),
        ('structure fields', fixture(field, '`{NAMESPACE}.bound, `{NAMESPACE}.Model'),
         fixture(field, '`{NAMESPACE}.Model'), 'Untrusted statement dependencies'),
        ('nested names remain untrusted', fixture(namespace, '`{NAMESPACE}.Model.unlisted'),
         fixture(namespace, '`{NAMESPACE}.Model'), 'Untrusted statement dependencies'),
        ('auxiliary values are traversed', fixture(auxiliary, '`{NAMESPACE}.inner, `{NAMESPACE}.model'),
         fixture(auxiliary, '`{NAMESPACE}.model'), 'Untrusted statement dependencies'),
        ('every trusted name must exist', fixture(direct, '`{NAMESPACE}.model'),
         fixture(direct, '`{NAMESPACE}.model, `{NAMESPACE}.missing'),
         'Trusted declaration does not exist'),
        ('private computational definitions',
         fixture(private, '``{NAMESPACE}.inner, `{NAMESPACE}.model'),
         fixture(private, '`{NAMESPACE}.model'), 'Untrusted statement dependencies'),
        ('proof values are leaves but proposition definitions are not',
         fixture(proof_only, ''), fixture(proof_in_type, ''),
         'Untrusted statement dependencies'),
    ]


def headline_cases():
    command = '''
open Lean Elab Command in
run_cmd liftTermElabM do
  discard <| KernelR.TrustedBaseChecker.check
    `KernelR.Hybrid.TrustedHeadline.every_finite_chain TRUSTED
'''
    trusted = 'KernelR.TrustedBase.trustedDeclarations'
    variant_command = '''
open Lean Elab Command in
run_cmd liftTermElabM do
  discard <| KernelR.TrustedBaseChecker.check
    `{NAMESPACE}.variant KernelR.TrustedBase.trustedDeclarations
'''
    plain = '''open KernelR.Hybrid
theorem variant {n : ℕ} (state : Snapshot (n + 1)) : True := True.intro
'''
    constructed = '''open KernelR.Hybrid
theorem variant {n θ bornCells K sigma centre error T}
    (chain : @ConstructedIndexedBirthCadenceChain n θ bornCells K sigma centre error T) :
    True := True.intro
'''
    return [
        ('headline excludes construction structures', plain + variant_command,
         constructed + variant_command, 'Untrusted statement dependencies'),
        ('actual headline needs the explicit router', command.replace('TRUSTED', trusted),
         command.replace('TRUSTED',
                         f'({trusted}.erase `KernelR.Hybrid.explicitFiniteChainRouter)'),
         'Untrusted statement dependencies'),
    ]


def check_batches(cases, module):
    with tempfile.TemporaryDirectory(prefix='trusted-base-negative-', dir=ROOT) as temporary:
        path = Path(temporary) / 'Check.lean'
        command = lean_check_command(temporary, root_module=module)
        for good in [True, False]:
            source = f'import {module}\nset_option maxErrors 0\nset_option maxHeartbeats 8000000\n'
            blocks = []
            for index, (label, positive, negative, expected) in enumerate(cases):
                start = source.count('\n') + 1
                body = (positive if good else negative).replace('{NAMESPACE}', f'TrustControl{index}')
                source += f'namespace TrustControl{index}\n{body}\nend TrustControl{index}\n'
                blocks.append((start, source.count('\n'), label, expected))
            path.write_text(source)
            result = subprocess.run([*command, '--json', str(path)], cwd=ROOT, text=True,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=300)
            if good:
                if result.returncode:
                    raise SystemExit('Positive trusted-base controls failed:\n' + result.stdout)
                continue
            errors = []
            for line in result.stdout.splitlines():
                try:
                    message = json.loads(line)
                except json.JSONDecodeError:
                    continue
                if message.get('severity') == 'error':
                    errors.append(message)
            if result.returncode == 0:
                raise SystemExit('Altered trusted-base controls unexpectedly compiled.')
            for start, end, label, expected in blocks:
                own = [error for error in errors if start <= error.get('pos', {}).get('line', -1) <= end]
                if not own or any(expected not in str(error.get('data', '')) for error in own):
                    raise SystemExit(f'{label}: no own intended checker rejection:\n{result.stdout}')
                print(f'{label}: original accepted; altered contract rejected by checker.', flush=True)
            if any(not any(start <= error.get('pos', {}).get('line', -1) <= end
                           for start, end, _, _ in blocks) for error in errors):
                raise SystemExit('Diagnostic outside a control:\n' + result.stdout)
    return [dict(case=label, positive='accepted', mutation='rejected')
            for label, _, _, _ in cases]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--checker-only', action='store_true')
    parser.add_argument('--report', type=Path)
    args = parser.parse_args()
    module = 'KernelR.TrustedBaseChecker' if args.checker_only else 'KernelR.TrustedBase'
    cases = checker_cases()
    if not args.checker_only:
        cases += headline_cases()
    report = check_batches(cases, module)
    if args.report:
        args.report.write_text(json.dumps(report, indent=2) + '\n')
    print(f'All {len(cases)} paired checker controls passed.', flush=True)


if __name__ == '__main__':
    main()
