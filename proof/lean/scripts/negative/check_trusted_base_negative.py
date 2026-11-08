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

from scripts.lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[2]


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
    auxiliary = ('inductive Counter where | zero | succ : Counter → Counter\n'
                 'def inner : Nat := 0\n'
                 'def model : Counter → Nat | .zero => inner | .succ n => model n\n'
                 'theorem headline : model Counter.zero = 0 := rfl\n')
    private = ('private def inner : Nat := 0\ndef model : Nat := inner\n'
               'theorem headline : model = 0 := rfl\n')
    # Distinct discriminant types prevent Lean's matcher cache from sharing
    # another fixture's matcher (and thus its separate semantic owner).
    private_matcher = ('inductive Choice where | a | b | c\ndef inner : Nat := 0\n'
                       'private def model : Choice → Nat | .a => inner | .b => 1 | .c => 2\n'
                       'theorem headline : model Choice.a = 0 := rfl\n')
    proof_only = ('def implementation : Nat := 0\n'
                  'theorem headline : True := by\n'
                  '  have hidden : implementation = 0 := rfl\n  trivial\n')
    proof_in_type = ('def implementation : Nat := 0\n'
                     'theorem headline : implementation = 0 := rfl\n')
    cases = [
        ('direct needed name', fixture(direct, '`{NAMESPACE}.model'),
         fixture(direct, ''), 'Untrusted statement dependencies'),
        ('definition values', fixture(nested, '`{NAMESPACE}.inner, `{NAMESPACE}.model'),
         fixture(nested, '`{NAMESPACE}.model'), 'Untrusted statement dependencies'),
        ('structure fields', fixture(field, '`{NAMESPACE}.bound, `{NAMESPACE}.Model'),
         fixture(field, '`{NAMESPACE}.Model'), 'Untrusted statement dependencies'),
        ('nested names remain untrusted', fixture(namespace, '`{NAMESPACE}.Model.unlisted'),
         fixture(namespace, '`{NAMESPACE}.Model'), 'Untrusted statement dependencies'),
        ('auxiliary values are traversed',
         fixture(auxiliary, '`{NAMESPACE}.Counter, `{NAMESPACE}.inner, `{NAMESPACE}.model'),
         fixture(auxiliary, '`{NAMESPACE}.Counter, `{NAMESPACE}.model'),
         'Untrusted statement dependencies'),
        ('every trusted name must exist', fixture(direct, '`{NAMESPACE}.model'),
         fixture(direct, '`{NAMESPACE}.model, `{NAMESPACE}.missing'),
         'Trusted declaration does not exist'),
        ('private computational definitions',
         fixture(private, '``{NAMESPACE}.inner, `{NAMESPACE}.model'),
         fixture(private, '`{NAMESPACE}.model'), 'Untrusted statement dependencies'),
        ('genuine private matchers retain their private semantic owner',
         fixture(private_matcher, '`{NAMESPACE}.Choice, `{NAMESPACE}.inner, ``{NAMESPACE}.model'),
         fixture(private_matcher, '`{NAMESPACE}.Choice, `{NAMESPACE}.inner'),
         'Untrusted statement dependencies'),
        ('proof values are leaves but proposition definitions are not',
         fixture(proof_only, ''), fixture(proof_in_type, ''),
         'Untrusted statement dependencies'),
    ]
    # Literal-only bodies cannot be rejected accidentally through some other
    # unlisted project dependency. Every recognized suffix family is exercised.
    suffixes = [
        'match_1', 'proof_1', 'eq_custom', '_eq_custom', '_sizeOf_custom',
        '_sparseCasesOn_custom', 'rec', 'recOn', 'casesOn', 'brecOn', 'below',
        'ibelow', 'noConfusion', 'noConfusionType', 'inj', 'injEq', 'inj_iff',
        'sizeOf_spec', 'ctorIdx', '_unary', '_sunfold', '_unsafe_rec',
        'equations', 'splitter', 'eta', 'ext', 'ext_iff', 'elim', 'ctorElim',
        'ctorElimType', '_f', 'decEq',
    ]
    for suffix in suffixes:
        body = (f'def model : Nat := 0\ndef model.{suffix} : Nat := 1\n'
                f'theorem headline : model.{suffix} = 1 := rfl\n')
        cases.append((f'handwritten {suffix} is not compiler support',
                      fixture(body, f'`{{NAMESPACE}}.model, `{{NAMESPACE}}.model.{suffix}'),
                      fixture(body, '`{NAMESPACE}.model'),
                      'Untrusted statement dependencies'))
    private_helper = ('def model : Nat := 0\nprivate def model.proof_1 : Nat := 1\n'
                      'theorem headline : model.proof_1 = 1 := rfl\n')
    cases.append(('private handwritten helper is not compiler support',
                  fixture(private_helper, '`{NAMESPACE}.model, ``{NAMESPACE}.model.proof_1'),
                  fixture(private_helper, '`{NAMESPACE}.model'),
                  'Untrusted statement dependencies'))
    handwritten_instance = ('''inductive Model where | only
instance instDecidableEqModel : DecidableEq Model := fun x y =>
  isTrue (by cases x; cases y; rfl)
theorem headline : decide (Model.only = Model.only) = true := rfl
''')
    cases.append(('handwritten equality instance is not inline deriving',
                  fixture(handwritten_instance, '`{NAMESPACE}.Model, `{NAMESPACE}.instDecidableEqModel'),
                  fixture(handwritten_instance, '`{NAMESPACE}.Model'),
                  'Untrusted statement dependencies'))
    derived_instance = ('''inductive Model where
  | a | b
  deriving DecidableEq
theorem headline : decide (Model.a = Model.a) = true := rfl
''')
    cases.append(('inline derived equality retains its semantic owner',
                  fixture(derived_instance, '`{NAMESPACE}.Model'),
                  fixture(derived_instance, ''), 'Untrusted statement dependencies'))
    derived_fields = ('''inductive Model where
  | a : Nat → Model
  | b : Bool → Model
  deriving DecidableEq
theorem headline : decide (Model.a 0 = Model.a 0) = true := rfl
''')
    cases.append(('inline derived equality with fields retains its semantic owner',
                  fixture(derived_fields, '`{NAMESPACE}.Model'),
                  fixture(derived_fields, ''), 'Untrusted statement dependencies'))
    after_deriving = ('''inductive Model where
  | a | b
  deriving DecidableEq
def instDecidableEqModel.decEq : Nat := 1
theorem headline : instDecidableEqModel.decEq = 1 := rfl
''')
    cases.append(('handwritten helper after deriving remains independent',
                  fixture(after_deriving, '`{NAMESPACE}.Model, `{NAMESPACE}.instDecidableEqModel.decEq'),
                  fixture(after_deriving, '`{NAMESPACE}.Model'),
                  'Untrusted statement dependencies'))
    return cases


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


def imported_cases():
    return [
        ('imported handwritten matcher is not compiler support',
         fixture('theorem headline : TrustedImportedControl.model.match_1 = 1 := rfl\n',
                 '`TrustedImportedControl.model, `TrustedImportedControl.model.match_1'),
         fixture('theorem headline : TrustedImportedControl.model.match_1 = 1 := rfl\n',
                 '`TrustedImportedControl.model'), 'Untrusted statement dependencies'),
        ('imported handwritten proof helper is not compiler support',
         fixture('theorem headline : TrustedImportedControl.model.proof_1 = 1 := rfl\n',
                 '`TrustedImportedControl.model, `TrustedImportedControl.model.proof_1'),
         fixture('theorem headline : TrustedImportedControl.model.proof_1 = 1 := rfl\n',
                 '`TrustedImportedControl.model'), 'Untrusted statement dependencies'),
        ('imported inline deriving retains its semantic owner',
         fixture('theorem headline : decide (TrustedImportedControl.Model.a 0 = '
                 'TrustedImportedControl.Model.a 0) = true := rfl\n', '`TrustedImportedControl.Model'),
         fixture('theorem headline : decide (TrustedImportedControl.Model.a 0 = '
                 'TrustedImportedControl.Model.a 0) = true := rfl\n', ''),
         'Untrusted statement dependencies'),
    ]


def build_imported_fixture(directory, module):
    name = 'TrustedImportedControl'
    source = Path(directory) / f'{name}.lean'
    artifact = source.with_suffix('.olean')
    source.write_text('''import Lean
namespace TrustedImportedControl
def model : Nat := 0
def model.match_1 : Nat := 1
def model.proof_1 : Nat := 1
inductive Model where
  | a : Nat → Model
  | b : Bool → Model
  deriving DecidableEq
end TrustedImportedControl
''')
    command = lean_check_command(directory, module_name=name, root_module=module)
    result = subprocess.run([*command, '-o', str(artifact), str(source)], cwd=ROOT,
                            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=300)
    if result.returncode:
        raise SystemExit('Imported trusted-base fixture failed:\n' + result.stdout)
    return {name: [[str(artifact)]]}


def controls(*, checker_only=False):
    cases = checker_cases() + imported_cases()
    return cases if checker_only else cases + headline_cases()


def check_batches(cases, module, *, extra_artifacts=None):
    with tempfile.TemporaryDirectory(prefix='trusted-base-negative-', dir=ROOT) as temporary:
        path = Path(temporary) / 'Check.lean'
        command = lean_check_command(temporary, root_module=module, extra_artifacts=extra_artifacts)
        for good in [True, False]:
            source = f'import {module}\n'
            source += ''.join(f'import {name}\n' for name in extra_artifacts or {})
            source += 'set_option maxErrors 0\nset_option maxHeartbeats 8000000\n'
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
    cases = controls(checker_only=args.checker_only)
    with tempfile.TemporaryDirectory(prefix='trusted-base-import-', dir=ROOT) as directory:
        artifacts = build_imported_fixture(directory, module)
        report = check_batches(cases, module, extra_artifacts=artifacts)
    if args.report:
        args.report.write_text(json.dumps(report, indent=2) + '\n')
    print(f'All {len(cases)} paired checker controls passed.', flush=True)


if __name__ == '__main__':
    main()
