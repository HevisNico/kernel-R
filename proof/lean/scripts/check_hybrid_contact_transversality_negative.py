#!/usr/bin/env python3
"""Compile hybrid contact certificates and reject false guard-only claims."""
from pathlib import Path
import subprocess
import tempfile

from lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[1]
PREFIX = '''import KernelR.HybridBirthCadenceChain
import KernelR.HybridContactTransversalityCuts
import KernelR.HybridContactPortTransport
import KernelR.HybridContactSourceRestriction
import KernelR.HybridContactRouterTransport
open KernelR.Hybrid Set

example {n θ s u} (e : @Execution n θ (fun _ _ => []) s u)
    (positive : e.ContactsTransversal) (cutoff : ℝ) (before : u.time ≤ cutoff) :
    ∃ lifted : Execution θ (fun _ _ => []) (retainSourcesThrough cutoff s)
      (retainSourcesThrough cutoff u), lifted.ledger = e.ledger ∧
      lifted.deliveries = e.deliveries ∧ lifted.ContactsTransversal :=
  e.retainSourcesThrough_transversal positive cutoff before

example {n θ route s u} (e : @Execution n θ route s u)
    (positive : e.ContactsTransversal) (newRoute : Router n)
    (hMatches : ∀ ev ∈ e.ledger.emissions, route ev.1 ev.2 = newRoute ev.1 ev.2) :
    ∃ lifted : Execution θ newRoute s u, lifted.ledger = e.ledger ∧
      lifted.deliveries = e.deliveries ∧ lifted.ContactsTransversal := by
  obtain ⟨lifted, ledger, deliveries, contacts⟩ := e.retarget_router_transversal newRoute hMatches
  exact ⟨lifted, ledger, deliveries, contacts.mpr positive⟩
'''


def property_case(name, binders, proposition, proof):
    valid = f'''example {binders} : {proposition} := by
{proof}
'''
    invalid = f'''example {binders} : ¬ ({proposition}) := by
  have positive : {proposition} := by
''' + '\n'.join('  ' + line for line in proof.splitlines()) + '''
  simpa only [positive, not_true_eq_false]
'''
    return name, valid, invalid


FACTORY_BINDERS = '''{n θ bornCells K ε}
    (hborn : ∀ i : Fin (n+1), BirthState (bornCells i))
    (hb : @PhysicalBox (n+1) θ ε) (ha : ∀ i q, (bornCells i).aux 0 q = .ready)
    (hqueue : ∀ i, (bornCells i).pending = sourceTrain 0 (finiteChainPreparationPort n i) 0 8 16)
    (sigma centre : ℕ → ℝ) (delay : ℕ → ℝ → ℝ)
    (hK : 4 * (n+1) + 12 ≤ K) (hsigma : ∀ j, 0 ≤ sigma j)
    (hbudget : KernelR.Chain.pathJitter sigma n ≤ 3/20)
    (hcentre : ∀ j, j < n → (3/10 : ℝ) + sigma j ≤ centre j ∧ centre j ≤ 2/5 - sigma j)
    (herror : ∀ j, j < n → ∀ t,
      -sigma j ≤ delay j t - centre j ∧ delay j t - centre j ≤ sigma j)'''
FACTORY_PROPOSITION = '''∃ c : ConstructedBirthCadenceChain θ bornCells K sigma centre delay
      (cadenceChainTerminal n K), c.execution.ContactsTransversal'''
FACTORY_PROOF = '''  obtain ⟨c⟩ := birth_cadence_chain_exists hborn hb ha hqueue
    sigma centre delay hK hsigma hbudget hcentre herror
  exact ⟨c, c.contacts_transversal⟩'''

BOUNDARY_PREFIX = '''noncomputable def guardOnlyValues : Values 1 := fun _ coordinate =>
  match coordinate with
  | .q => 1
  | .m _ => 1 / 40
  | .z _ => 0
  | .b => 2 / 25
  | .energy => 100

noncomputable def guardOnlyState : Snapshot 1 where
  time := 0
  x := guardOnlyValues
  main := fun _ => .ready
  aux := fun _ _ => .ready
  raw := fun _ _ => none
  pending := []

noncomputable def guardOnlyFire : Jump (fun _ _ => []) guardOnlyState
    {setMain guardOnlyState 0 .fast with pending := []} :=
  .fire guardOnlyState 0 rfl rfl

theorem guardOnly_field (θ : Fin 1 → Parameters) :
    field θ guardOnlyState guardOnlyState.x guardOnlyState.time 0 .q = -9 / 20 := by
  norm_num [field, drive, current, guardOnlyState, guardOnlyValues]

noncomputable def balancedState : Snapshot 1 where
  time := 0
  x := fun _ coordinate => match coordinate with
    | .q => 1
    | .m _ => 1 / 40
    | .z _ => Real.log ((9 / 20 : ℝ) / a)
    | .b => 2 / 25
    | .energy => 100
  main := fun _ => .ready
  aux := fun _ _ => .ready
  raw := fun _ p => if p = 0 then some 0 else none
  pending := []

noncomputable def balancedFire : Jump (fun _ _ => []) balancedState
    {setMain balancedState 0 .fast with pending := []} :=
  .fire balancedState 0 rfl rfl

theorem balanced_field (θ : Fin 1 → Parameters) :
    field θ balancedState balancedState.x balancedState.time 0 .q = 0 := by
  have ha : 0 < a := by linarith [a_coarse_bounds.1]
  have gain : Real.exp (Real.log ((9 / 20 : ℝ) / a)) = (9 / 20 : ℝ) / a :=
    Real.exp_log (div_pos (by norm_num) ha)
  rw [ready_single_pulse_field balancedState 0 0 0 rfl
    (by simp [balancedState])
    (by intro p hp; simp [balancedState, hp]) (by norm_num [balancedState])]
  change (1 / 2 : ℝ) * (1 / 10 - 1) +
    Real.exp (Real.log ((9 / 20 : ℝ) / a)) * a * Real.exp (-a * (0 - 0)) = 0
  rw [gain, div_mul_cancel₀ _ (ne_of_gt ha)]
  norm_num
'''


def main():
    cases = [
        property_case('the original factory constructs a certified witness',
                      FACTORY_BINDERS, FACTORY_PROPOSITION, FACTORY_PROOF),
        property_case(
            'append retains both contact certificates',
            '''{n θ route s u v} (first : @Execution n θ route s u)
    (rest : Execution θ route u v) (left : first.ContactsTransversal)
    (right : rest.ContactsTransversal)''',
            '(first.append rest).ContactsTransversal',
            '  exact (first.contactsTransversal_append rest).mpr ⟨left, right⟩',
        ),
        property_case(
            'every actual execution prefix retains its certificate',
            '''{n θ route s u v} {e : @Execution n θ route s u}
    {cut : Execution θ route s v} (hPrefix : e.IsPrefix cut)
    (positive : e.ContactsTransversal)''',
            'cut.ContactsTransversal',
            '  exact hPrefix.contacts_transversal positive',
        ),
        property_case(
            'port permutation retains the actual contact fields',
            '''{n θ s u} (e : @Execution n θ (fun _ _ => []) s u)
    (positive : e.ContactsTransversal) (sigma : Equiv.Perm Port)''',
            '(e.permutePorts sigma).ContactsTransversal',
            '  exact e.contactsTransversal_permutePorts sigma positive',
        ),
        property_case(
            'queue and router transport retains the same physical jump',
            '''{n θ route route' s u Q R} (jump : @Jump n route s u)
    (lifted : @Jump n route' {s with pending := Q} {u with pending := R})
    (positive : jump.ContactTransversal θ)''',
            'lifted.ContactTransversal θ',
            '  exact (jump.contactTransversal_requeue lifted).mp positive',
        ),
        (
            'an enabled equality guard can have a negative READY field',
            BOUNDARY_PREFIX + '''example (θ : Fin 1 → Parameters) :
    ¬ guardOnlyFire.ContactTransversal θ := by
  norm_num [guardOnlyFire, Jump.ContactTransversal, guardOnly_field]
''',
            BOUNDARY_PREFIX + '''example (θ : Fin 1 → Parameters) :
    guardOnlyFire.ContactTransversal θ := by
  norm_num [guardOnlyFire, Jump.ContactTransversal, guardOnly_field]
''',
        ),
        (
            'a nonnegative field at equality is insufficient',
            BOUNDARY_PREFIX + '''example (θ : Fin 1 → Parameters) :
    0 ≤ field θ balancedState balancedState.x balancedState.time 0 .q ∧
      ¬ balancedFire.ContactTransversal θ := by
  norm_num [balancedFire, Jump.ContactTransversal, balanced_field]
''',
            BOUNDARY_PREFIX + '''example (θ : Fin 1 → Parameters) :
    0 ≤ field θ balancedState balancedState.x balancedState.time 0 .q ∧
      balancedFire.ContactTransversal θ := by
  norm_num [balancedFire, Jump.ContactTransversal, balanced_field]
''',
        ),
    ]
    with tempfile.TemporaryDirectory(prefix='hybrid-contact-controls-', dir=ROOT) as directory:
        path = Path(directory) / 'Check.lean'
        extra = {
            'KernelR.HybridContactTransversalityCuts': [[str(
                ROOT / '.lake/build/lib/lean/KernelR/HybridContactTransversalityCuts.olean')]],
        }
        command = lean_check_command(
            directory, root_module='KernelR.HybridBirthCadenceChain', extra_artifacts=extra,
        )
        for name, valid, invalid in cases:
            for expected, source in ((True, valid), (False, invalid)):
                path.write_text(PREFIX + source)
                result = subprocess.run(
                    [*command, str(path)], cwd=ROOT, text=True,
                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=180,
                )
                if (result.returncode == 0) != expected:
                    raise SystemExit(f'{name}: unexpected result:\n{result.stdout}')
                if not expected:
                    if 'error:' not in result.stdout or 'False' not in result.stdout:
                        raise SystemExit(f'{name}: wrong mathematical diagnostic:\n{result.stdout}')
                    forbidden = ('unknown module', 'unknown identifier', 'unexpected token',
                                 'failed to synthesize', 'object file', 'invalid import')
                    if any(message in result.stdout.lower() for message in forbidden):
                        raise SystemExit(f'{name}: import or elaboration failure:\n{result.stdout}')
            print(f'PASS {name}: valid certificate compiles, false claim rejected.', flush=True)
    print(f'{len(cases)} paired hybrid contact controls passed.', flush=True)


if __name__ == '__main__':
    main()
