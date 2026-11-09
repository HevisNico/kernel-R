#!/usr/bin/env python3
"""Paired controls for geometric crossings and exact native correspondence.

Polynomial controls check only the geometric sign clauses. They do not claim
that those polynomials solve Kernel R's ODE or construct Kernel orbit germs.
"""
import argparse
from pathlib import Path
import subprocess
import tempfile

from scripts.lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[2]
FIXTURE = ROOT / 'scripts' / 'fixtures' / 'crossing_grazing.lean'
# Keep Lean imports before the opens and declarations when inlining the fixture.
_fixture_lines = FIXTURE.read_text().splitlines()
FIXTURE_IMPORTS = '\n'.join(line for line in _fixture_lines if line.startswith('import '))
FIXTURE_BODY = '\n'.join(line for line in _fixture_lines if not line.startswith('import ')) + '\n'
PREFIX = 'import KernelR.HybridCrossingCorrespondence\n' + FIXTURE_IMPORTS + '''
open KernelR.Hybrid Set Filter
open scoped Topology
'''


def property_case(name, binders, proposition, proof):
    valid = f'''example {binders} : {proposition} := by
{proof}
'''
    invalid = f'''example {binders} : ¬ ({proposition}) := by
  have positive : {proposition} := by
''' + '\n'.join('  ' + line for line in proof.splitlines()) + '''
  simp [positive]
'''
    return name, valid, invalid


GUARD_PREFIX = '''noncomputable def boundary : Snapshot 1 where
  time := 0
  x := fun _ coordinate => match coordinate with
    | .q => 1
    | .m _ => 1 / 40
    | _ => 0
  main := fun _ => .ready
  aux := fun _ _ => .ready
  raw := fun _ _ => none
  pending := []
'''
GEOMETRY_PREFIX = '''def cubic (t : ℝ) : ℝ := 1 + t ^ 3

theorem cubic_derivative : HasDerivAt cubic 0 0 := by
  change HasDerivAt (fun t : ℝ => 1 + t ^ 3) 0 0
  convert ((hasDerivAt_id (0 : ℝ)).pow 3).const_add 1 using 1 <;> norm_num

theorem cubic_left : ∀ᶠ t in 𝓝[<] (0 : ℝ), cubic t < 1 := by
  filter_upwards [self_mem_nhdsWithin] with t ht
  change t < 0 at ht
  have cube := pow_pos (neg_pos.mpr ht) 3
  dsimp [cubic]
  nlinarith

theorem cubic_right : ∀ᶠ t in 𝓝[>] (0 : ℝ), 1 < cubic t := by
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  dsimp [cubic]
  linarith [pow_pos ht 3]

def tangent (t : ℝ) : ℝ := 1 - t ^ 2

theorem tangent_not_crossing : ¬ (∀ᶠ t in 𝓝[>] (0 : ℝ), 1 < tangent t) := by
  intro crossing
  obtain ⟨t, ht⟩ := crossing.exists
  dsimp [tangent] at ht
  nlinarith [sq_nonneg t]
'''
ROUTER_PREFIX = '''def zeroDelay : Router 1 := fun i t => [⟨i, 0, t⟩]
def positiveDelay : Router 1 := fun i t => [⟨i, 0, t + 1⟩]

theorem zero_causal : CausalRouter zeroDelay := by
  intro i t d member
  simp only [zeroDelay, List.mem_singleton] at member
  subst d
  exact le_rfl

theorem zero_not_strict : ¬ StrictCausalRouter zeroDelay := by
  intro strict
  have impossible := strict 0 0 ⟨0, 0, 0⟩ (by simp [zeroDelay])
  exact (lt_irrefl (0 : ℝ)) impossible

theorem positive_strict : StrictCausalRouter positiveDelay := by
  intro i t d member
  simp only [positiveDelay, List.mem_singleton] at member
  subst d
  dsimp
  linarith
'''

CHAIN_BINDERS = '''{n θ bornCells K sigma centre delay T ε}
    (chain : @ConstructedBirthCadenceChain n θ bornCells K sigma centre delay T)
    (box : PhysicalBox θ ε) {u}
    (candidate : CrossingExecution θ chain.router (familyPreparationBornSource bornCells K) u)
    (complete : CrossingCompleteThrough candidate T)'''


def cases():
    return [
        ('weak guards admit equality and native guards reject it',
         GUARD_PREFIX + '''example : WeakBeforeGuards boundary boundary.x ∧
    ¬ BeforeGuards boundary boundary.x := by
  norm_num [WeakBeforeGuards, BeforeGuards, boundary]
''',
         GUARD_PREFIX + '''example : WeakBeforeGuards boundary boundary.x ∧
    BeforeGuards boundary boundary.x := by
  norm_num [WeakBeforeGuards, BeforeGuards, boundary]
'''),
        ('an independent curve supplies no actual nil history',
         '''example {n θ route} (s : Snapshot n) (i : Fin n) (c : Coord)
    (curve : ℝ → ℝ) (_below : ∀ᶠ t in 𝓝[<] s.time, curve t < 1) :
    ¬ (@WeakExecution.nil n θ route s).LeftBelow i c := by
  simp only [WeakExecution.LeftBelow, not_false_eq_true]
''',
         '''example {n θ route} (s : Snapshot n) (i : Fin n) (c : Coord)
    (curve : ℝ → ℝ) (_below : ∀ᶠ t in 𝓝[<] s.time, curve t < 1) :
    (@WeakExecution.nil n θ route s).LeftBelow i c := by
  simp only [WeakExecution.LeftBelow]
'''),
        ('cubic geometry crosses with zero derivative',
         GEOMETRY_PREFIX + '''example :
    (∀ᶠ t in 𝓝[<] (0 : ℝ), cubic t < 1) ∧
    (∀ᶠ t in 𝓝[>] (0 : ℝ), 1 < cubic t) ∧ deriv cubic 0 = 0 := by
  exact ⟨cubic_left, cubic_right, cubic_derivative.deriv⟩
''',
         GEOMETRY_PREFIX + '''example :
    (∀ᶠ t in 𝓝[<] (0 : ℝ), cubic t < 1) ∧
    (∀ᶠ t in 𝓝[>] (0 : ℝ), 1 < cubic t) ∧ 0 < deriv cubic 0 := by
  simp only [cubic_derivative.deriv, lt_self_iff_false, and_false]
'''),
        # This conditional API control does not assert that a cubic Kernel germ exists.
        ('the real crossing predicate accepts a supplied cubic-shaped germ at zero derivative',
         GEOMETRY_PREFIX + '''example {n θ s} (i : Fin n) (c : Coord)
    (germ : CellOrbitGerm θ s i) (clock : s.time = 0)
    (shape : ∀ t, germ.path t i c = cubic t) :
    CellRightCrossing θ s i c ∧ deriv (fun t => germ.path t i c) 0 = 0 := by
  refine ⟨⟨germ, ?_⟩, ?_⟩
  · simpa only [clock, shape] using cubic_right
  · have same : (fun t => germ.path t i c) = cubic := funext shape
    rw [same]
    exact cubic_derivative.deriv
''',
         GEOMETRY_PREFIX + '''example {n θ s} (i : Fin n) (c : Coord)
    (germ : CellOrbitGerm θ s i) (clock : s.time = 0)
    (shape : ∀ t, germ.path t i c = cubic t) : ¬ CellRightCrossing θ s i c := by
  have crossing : CellRightCrossing θ s i c :=
    ⟨germ, by simpa only [clock, shape] using cubic_right⟩
  simp [crossing]
'''),
        ('a tangency never exceeds the threshold to the right',
         GEOMETRY_PREFIX + '''example : ¬ (∀ᶠ t in 𝓝[>] (0 : ℝ), 1 < tangent t) :=
  tangent_not_crossing
''',
         GEOMETRY_PREFIX + '''example : ∀ᶠ t in 𝓝[>] (0 : ℝ), 1 < tangent t := by
  simp only [tangent_not_crossing]
'''),
        ('strict routing rejects zero delay but accepts a positive delay',
         ROUTER_PREFIX + '''example : CausalRouter zeroDelay ∧ ¬ StrictCausalRouter zeroDelay ∧
    StrictCausalRouter positiveDelay :=
  ⟨zero_causal, zero_not_strict, positive_strict⟩
''',
         ROUTER_PREFIX + '''example : CausalRouter zeroDelay ∧ StrictCausalRouter zeroDelay ∧
    StrictCausalRouter positiveDelay := by
  simp only [zero_not_strict, false_and, and_false]
'''),
        property_case('the physical orbit solves every coordinate including plasticity and energy',
          '''{n θ s} (physical : @PhysicalInvariant n θ s) (i : Fin n) (p : Port)
    (t : ℝ) (within : t ∈ Ico s.time (s.time + (physical.cell_orbit i).duration))''',
          '''(∀ c, HasDerivAt (fun v => (physical.cell_orbit i).path v i c)
      (field θ s ((physical.cell_orbit i).path t) t i c) t) ∧
    HasDerivAt (fun v => (physical.cell_orbit i).path v i (.z p))
      (field θ s ((physical.cell_orbit i).path t) t i (.z p)) t ∧
    HasDerivAt (fun v => (physical.cell_orbit i).path v i .b)
      (field θ s ((physical.cell_orbit i).path t) t i .b) t ∧
    HasDerivAt (fun v => (physical.cell_orbit i).path v i .energy)
      (field θ s ((physical.cell_orbit i).path t) t i .energy) t''',
          '''  exact ⟨(physical.cell_orbit i).derivative t within,
    (physical.cell_orbit i).derivative t within (.z p),
    (physical.cell_orbit i).derivative t within .b,
    (physical.cell_orbit i).derivative t within .energy⟩'''),
        property_case('geometric completion refines the exact weak paths without candidate contact assumptions',
          '''{n θ ε route s u v T} (candidate : @CrossingExecution n θ route s u)
    (reference : Execution θ route s v) (routing : StrictCausalRouter route)
    (box : PhysicalBox θ ε) (physical : PhysicalInvariant θ s)
    (initial : InitiallyBelowReady s) (complete : CompleteThrough reference T)
    (positive : reference.ContactsTransversal)
    (modelComplete : CrossingCompleteThrough candidate T)''',
          '''∃ native : Execution θ route s u,
      native.toWeak = candidate.execution ∧ CompleteThrough native T''',
          '''  exact candidate.toNative_complete reference routing box physical initial
    complete positive modelComplete'''),
        property_case('the constructed protocol supplies a complete geometric execution',
          '''{n θ bornCells K sigma centre delay T ε}
    (chain : @ConstructedBirthCadenceChain n θ bornCells K sigma centre delay T)
    (box : PhysicalBox θ ε)''',
          'CrossingCompleteThrough (chain.crossingExecution box) T',
          '  exact chain.crossingExecution_complete box'),
        property_case('constructed-chain candidates refine without any supplied contact certificate',
          CHAIN_BINDERS,
          '''∃ native : Execution θ chain.router (familyPreparationBornSource bornCells K) u,
      native.toWeak = candidate.execution ∧ CompleteThrough native T''',
          '  exact chain.crossing_refines_native box candidate complete'),
        property_case('all crossing completions share physical observations and ordered FIRE lists',
          CHAIN_BINDERS,
          '''chain.final.ObservationalEq u ∧
      ∀ i, candidate.execution.emissionTimes i = chain.execution.emissionTimes i''',
          '  exact chain.every_crossing_complete box candidate complete'),
        property_case('every complete native execution has a complete crossing representative',
          '''{n θ bornCells K sigma centre delay T ε}
    (chain : @ConstructedBirthCadenceChain n θ bornCells K sigma centre delay T)
    (box : PhysicalBox θ ε) {u}
    (native : Execution θ chain.router (familyPreparationBornSource bornCells K) u)
    (complete : CompleteThrough native T)''',
          '''∃ v, ∃ model : CrossingExecution θ chain.router
      (familyPreparationBornSource bornCells K) v,
      CrossingCompleteThrough model T ∧ u.ObservationalEq v ∧
        ∀ i, native.emissionTimes i = model.execution.emissionTimes i''',
          '  exact chain.native_has_crossing_representative box native complete'),
        property_case('the full protocol outcome transfers to the actual crossing endpoint',
          CHAIN_BINDERS,
          '''UniversalCadenceOutcome θ bornCells K T u candidate.execution.emissionTimes
      candidate.execution.ledger.emissions.length''',
          '  exact chain.crossing_outcome box candidate complete'),
        # This is a constructed Kernel ODE history outside PhysicalBox/protocol.
        # The no-crossing assertion concerns its explicit orbit, not all germs.
        ('a genuine off-protocol grazing history admits a model flow and no native flow',
         FIXTURE_BODY + '''open KernelR.Hybrid.GrazingFixture
example :
    ∃ model : CrossingExecution parameters (fun _ _ => []) snapshot endpoint,
      model.execution.moveCount = 1 ∧ model.execution.ledger.emissions = [] ∧
      (∀ v, IsEmpty (Flow parameters snapshot v)) ∧
      HasDerivAt (fun t => orbit.path t 0 .q) 0 0 ∧
      (¬ ∀ᶠ t in 𝓝[>] (0 : ℝ), 1 < orbit.path t 0 .q) ∧
      (∃ germ : CellOrbitGerm parameters snapshot 0,
        snapshot.x 0 .q = 1 ∧ field parameters snapshot snapshot.x snapshot.time 0 .q = 0 ∧
        ∀ t : ℝ, 0 < t → germ.path t 0 .q < 1) := by
  exact ⟨grazingCrossingExecution, rfl, rfl, no_native_flow,
    orbit_zero_derivative, orbit_no_ascending_crossing, genuine_grazing_contact⟩
''',
         FIXTURE_BODY + '''open KernelR.Hybrid.GrazingFixture
example : Nonempty (Flow parameters snapshot endpoint) := by
  have impossible : ¬ Nonempty (Flow parameters snapshot endpoint) := by
    rintro ⟨flow⟩
    exact (no_native_flow endpoint).false flow
  simp only [impossible]
'''),
    ]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--direct', action='store_true',
                        help='check stable artifacts directly before Lake generated the target setup; never builds')
    args = parser.parse_args()
    controls = cases()
    with tempfile.TemporaryDirectory(prefix='hybrid-crossing-controls-', dir=ROOT) as directory:
        path = Path(directory) / 'Check.lean'
        command = (['lake', 'env', 'lean'] if args.direct else lean_check_command(
            directory, root_module='KernelR.HybridCrossingCorrespondence',
            extra_artifacts={
                module: [[str(ROOT / '.lake/build/lib/lean' / (module.replace('.', '/') + '.olean'))]]
                for module in (line.removeprefix('import ') for line in FIXTURE_IMPORTS.splitlines())
            }))
        for name, valid, invalid in controls:
            for expected, source in ((True, valid), (False, invalid)):
                path.write_text(PREFIX + source)
                result = subprocess.run([*command, str(path)], cwd=ROOT, text=True,
                                        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=180)
                if (result.returncode == 0) != expected:
                    raise SystemExit(f'{name}: unexpected result:\n{result.stdout}')
                if not expected:
                    if 'error:' not in result.stdout or 'False' not in result.stdout:
                        raise SystemExit(f'{name}: wrong mathematical diagnostic:\n{result.stdout}')
                    forbidden = ('unknown module', 'unknown identifier', 'unexpected token',
                                 'failed to synthesize', 'object file', 'invalid import',
                                 'type mismatch', 'application type mismatch')
                    if any(message in result.stdout.lower() for message in forbidden):
                        raise SystemExit(f'{name}: import or elaboration failure:\n{result.stdout}')
            print(f'PASS {name}: valid claim compiles, corrupted claim rejected.', flush=True)
    print(f'{len(controls)} paired crossing controls passed.', flush=True)


if __name__ == '__main__':
    main()
