#!/usr/bin/env python3
"""Paired controls for every complete physical execution, without a witness premise.

A rejected mutation shows that the supplied proof script does not establish the
altered statement. It does not independently prove that statement's negation.
"""
from pathlib import Path
import subprocess
import tempfile

from lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[1]
MODULES = [
    'HybridSnapshotObservational', 'HybridFlowUniqueness', 'HybridUrgentMoves',
    'HybridObservationalTransport', 'HybridJumpConfluence', 'HybridRawJumpConfluence',
    'HybridJumpDepartures', 'HybridJumpLocalDiamond', 'HybridJumpStripping',
    'HybridExecutionUniqueness', 'HybridUniversalExecution', 'HybridUniversalBirthCadenceChain',
]
PREFIX = '''import KernelR.HybridUniversalBirthCadenceChain
open KernelR.Hybrid
noncomputable section
'''


def pair(label, template, good, bad):
    assert '@v@' in template and good != bad
    return label, template.replace('@v@', good), template.replace('@v@', bad)


def cases():
    execution = '''example {n θ ε route s u v T}
    (e : @Execution n θ route s u) (f : Execution θ route s v)
    (hb : PhysicalBox θ ε) (hs : PhysicalInvariant θ s)
    (he : CompleteThrough e T) (hf : CompleteThrough f T) '''
    chain = '''example {n θ bornCells K sigma centre delay T ε}
    (c : @ConstructedBirthCadenceChain n θ bornCells K sigma centre delay T)
    (hb : PhysicalBox θ ε) {u}
    (e : Execution θ c.router (familyPreparationBornSource bornCells K) u)
    (hc : CompleteThrough e T) '''
    return [
        pair('complete executions reach the same actual terminal clock', execution +
             ''': u.time=@v@ := by
  exact (e.observational_unique f hb hs he hf).1.time
''', 'v.time', 'v.time+1'),
        pair('arbitrary complete traces preserve the same physical charge', execution +
             '''(i : Fin n) : u.x i .q=@v@ := by
  exact congrFun (congrFun (e.observational_unique f hb hs he hf).1.values i) .q
''', 'v.x i .q', 'v.x i .q+1'),
        pair('each cell keeps its own gain in every complete trace', execution +
             '''(i : Fin n) (p : Port) : u.x i (.z p)=@v@ := by
  exact congrFun (congrFun (e.observational_unique f hb hs he hf).1.values i) (.z p)
''', 'v.x i (.z p)', 'v.x i (.z p)+1'),
        pair('recovery is independent of legal execution interleavings', execution +
             '''(i : Fin n) : u.x i .b=@v@ := by
  exact congrFun (congrFun (e.observational_unique f hb hs he hf).1.values i) .b
''', 'v.x i .b', 'v.x i .b+1'),
        pair('the universal comparison retains the actual energy trajectory endpoint', execution +
             '''(i : Fin n) : u.x i .energy=@v@ := by
  exact congrFun (congrFun (e.observational_unique f hb hs he hf).1.values i) .energy
''', 'v.x i .energy', '100'),
        pair('terminal main modes agree without a supplied phase description', execution +
             '''(i : Fin n) : u.main i=@v@ := by
  exact congrFun (e.observational_unique f hb hs he hf).1.main i
''', 'v.main i', 'MainMode.ready'),
        pair('terminal auxiliary modes retain the same cell and port', execution +
             '''(i : Fin n) (p : Port) : u.aux i p=@v@ := by
  exact congrFun (congrFun (e.observational_unique f hb hs he hf).1.aux i) p
''', 'v.aux i p', 'AuxMode.ready'),
        pair('raw-current origins are retained rather than cleared by comparison', execution +
             '''(i : Fin n) (p : Port) : u.raw i p=@v@ := by
  exact congrFun (congrFun (e.observational_unique f hb hs he hf).1.raw i) p
''', 'v.raw i p', 'none'),
        pair('pending tokens are compared with their actual terminal presentation', execution +
             ''': u.pending.Perm @v@ := by
  exact (e.observational_unique f hb hs he hf).1.pending
''', 'v.pending', '[]'),
        pair('global simultaneous FIREs retain permutation rather than an imposed total priority', execution +
             ''': @v@ := by
  exact (e.observational_unique f hb hs he hf).2
''', 'e.ledger.emissions.Perm f.ledger.emissions', 'e.ledger.emissions=f.ledger.emissions'),
        pair('each ordered actual cell FIRE list is unique', execution +
             '''(i : Fin n) : e.emissionTimes i=@v@ := by
  exact e.emissionTimes_unique f hb hs he hf i
''', 'f.emissionTimes i', '(f.emissionTimes i).reverse'),
        pair('complete execution comparison preserves every actual cell FIRE count', execution +
             '''(i : Fin n) : (e.emissionTimes i).length=@v@ := by
  exact congrArg List.length (e.emissionTimes_unique f hb hs he hf i)
''', '(f.emissionTimes i).length', '(f.emissionTimes i).length+1'),
        pair('both arbitrary executions must be complete through the same horizon',
             '''example {n θ ε route s u v T}
    (e : @Execution n θ route s u) (f : Execution θ route s v)
    (hb : PhysicalBox θ ε) (hs : PhysicalInvariant θ s)
    (he : CompleteThrough e T) (hf : CompleteThrough f (@v@)) :
    u.ObservationalEq v := by
  exact (e.observational_unique f hb hs he hf).1
''', 'T', 'T+1'),
        pair('universality fixes the original physical initial state',
             '''example {n θ ε route s u v T}
    (e : @Execution n θ route s u) (f : Execution θ route (@v@) v)
    (hb : PhysicalBox θ ε) (hs : PhysicalInvariant θ s)
    (he : CompleteThrough e T) (hf : CompleteThrough f T) :
    u.ObservationalEq v := by
  exact (e.observational_unique f hb hs he hf).1
''', 's', 'u'),
        pair('universal comparison does not substitute a different wiring law',
             '''example {n θ ε route s u v T} (other : Router n)
    (e : @Execution n θ route s u) (f : Execution θ (@v@) s v)
    (hb : PhysicalBox θ ε) (hs : PhysicalInvariant θ s)
    (he : CompleteThrough e T) (hf : CompleteThrough f T) :
    u.ObservationalEq v := by
  exact (e.observational_unique f hb hs he hf).1
''', 'route', 'other'),
        pair('fabrication parameters remain fixed across competing executions',
             '''example {n θ ε route s u v T} (other : Fin n → Parameters)
    (e : @Execution n θ route s u) (f : Execution (@v@) route s v)
    (hb : PhysicalBox θ ε) (hs : PhysicalInvariant θ s)
    (he : CompleteThrough e T) (hf : CompleteThrough f T) :
    u.ObservationalEq v := by
  exact (e.observational_unique f hb hs he hf).1
''', 'θ', 'other'),
        pair('every complete finite-chain trace reaches the resting charge', chain +
             '''(i : Fin (n+1)) : u.x i .q=@v@ := by
  exact (c.every_complete_outcome hb e hc).charge i
''', '1/10', '1/4'),
        pair('every complete trace retains its own independently born active gain', chain +
             '''(i : Fin (n+1)) : u.x i (.z (cadenceActivePort n i))=
    (bornCells i).x 0 (.z (cadenceActivePort n i))+@v@ := by
  exact (c.every_complete_outcome hb e hc).gain i
''', '12/5', '9/5'),
        pair('the universal traffic count belongs to the supplied actual complete execution', chain +
             ''': e.ledger.emissions.length=@v@ := by
  exact (c.every_complete_outcome hb e hc).total_count
''', '(n+1)*(K-(n+1)+8)+2', '(n+1)*(K-(n+1)-4)'),
        pair('prescribed errors hold at every complete traces own actual FAST sender index',
             '''example {n θ bornCells K sigma centre error T ε}
    (c : @ConstructedIndexedBirthCadenceChain n θ bornCells K sigma centre error T)
    (hb : PhysicalBox θ ε) {u}
    (e : Execution θ c.chain.router (familyPreparationBornSource bornCells K) u)
    (hc : CompleteThrough e T) (j : ℕ) (hj : j<n) (k : ℕ)
    (hk : k<((e.emissionTimes (indexedCadenceSender n j hj)).drop
      (finiteChainPreparationCount n (indexedCadenceSender n j hj))).length) :
    c.delay j ((e.emissionTimes (indexedCadenceSender n j hj)).drop
      (finiteChainPreparationCount n (indexedCadenceSender n j hj)))[k]=centre j+error j (@v@) := by
  exact c.all_complete_errors hb u e hc j hj k hk
''', 'k', 'k+1'),
    ]


def main():
    controls = cases()
    with tempfile.TemporaryDirectory(prefix='hybrid-universal-execution-', dir=ROOT) as tmp:
        path = Path(tmp) / 'Check.lean'
        artifacts = {f'KernelR.{name}': [[str(ROOT / f'.lake/build/lib/lean/KernelR/{name}.olean')]]
                     for name in MODULES}
        command = lean_check_command(tmp, extra_artifacts=artifacts)

        def check(source, expected, name):
            path.write_text(PREFIX + source)
            result = subprocess.run([*command, str(path)], cwd=ROOT, text=True,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=240)
            if (result.returncode == 0) != expected:
                raise SystemExit(f'{name}: unexpected result:\n{result.stdout}')
            if not expected and 'error:' not in result.stdout:
                raise SystemExit(f'{name}: failed without a Lean diagnostic:\n{result.stdout}')

        check('\n'.join(good for _, good, _ in controls), True, 'all universal complete-execution contracts')
        print(f'All {len(controls)} positive universal complete-execution contracts accepted.', flush=True)
        for name, _, bad in controls:
            check(bad, False, name)
            print(f'{name}: original proof accepted; mutated proof script rejected.', flush=True)
        print(f'{len(controls)} paired universal complete-execution controls passed.', flush=True)


if __name__ == '__main__':
    main()
