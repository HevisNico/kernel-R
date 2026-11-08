#!/usr/bin/env python3
"""Paired prescribed-error, actual sender-ledger and full-history contracts."""
from pathlib import Path
import subprocess
import tempfile

from scripts.lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[2]
MODULES = [
    'HybridCadenceStageTransport', 'HybridPreparedCadencePrefixTransport',
    'HybridStrongCadenceChainStep', 'HybridIndexedPreparedCadenceChain',
    'HybridIndexedBirthCadenceChain',
]
PREFIX = '''import KernelR.HybridIndexedBirthCadenceChain
open KernelR.Hybrid
noncomputable section
'''


def pair(label, template, good, bad):
    assert '@v@' in template and good != bad
    return label, template.replace('@v@', good), template.replace('@v@', bad)


def cases():
    chain = '''example {n θ bornCells K sigma centre error T}
    (c : @ConstructedIndexedBirthCadenceChain n θ bornCells K sigma centre error T) '''
    indexed = chain + '''(j : ℕ) (hj : j<n) (i : ℕ)
    (hi : i<(c.chain.fastExecution.emissionTimes (indexedCadenceSender n j hj)).length) '''
    transport = '''example {d d' : FiniteCausalChainData} {K T depth m L J}
    (c : ConstructedCadenceChainStage d K T depth m L J)
    (hp : d.parameters depth=d'.parameters depth)
    (hr : d.route depth=d'.route depth) (hs : d.source depth=d'.source depth) '''
    strong = '''example {d : FiniteCausalChainData} {ε n K sigma centre delay j m L J}
    (domain : PreparedCadenceChainDomain d ε n K sigma centre delay)
    (hj : j<n) (hL : 5≤L) (hJ : J+sigma j≤3/20)
    (old : ConstructedCadenceChainStage d K (cadenceChainTerminal n K) j m L J) :
    ∃ next : ConstructedCadenceChainStage d K (cadenceChainTerminal n K)
      (j+1) (m+2) (L-4) (J+sigma j),
      ∀ i : Fin (j+1), next.stage.execution.emissionTimes i.succ=@v@ := by
  exact domain.strong_step_exists hj hL hJ old
'''
    factory = '''example {n θ bornCells K ε}
    (hborn : ∀ i : Fin (n+1), BirthState (bornCells i))
    (hb : @PhysicalBox (n+1) θ ε) (ha : ∀ i q, (bornCells i).aux 0 q=.ready)
    (hqueue : ∀ i, (bornCells i).pending=sourceTrain 0 (finiteChainPreparationPort n i) 0 8 16)
    (sigma centre : ℕ→ℝ) (error : ℕ→ℕ→ℝ)
    (hK : 4*(n+1)+12≤K) (hsigma : ∀ j, 0≤sigma j)
    (hbudget : KernelR.Chain.pathJitter sigma n≤3/20)
    (hcentre : ∀ j, j<n → (3/10:ℝ)+sigma j≤centre j ∧ centre j≤2/5-sigma j)
    (herror : ∀ j, j<n → ∀ i, -sigma j≤error j i ∧ error j i≤sigma j) :
    Nonempty (ConstructedIndexedBirthCadenceChain θ bornCells K sigma centre @v@ (cadenceChainTerminal n K)) := by
  exact indexed_birth_cadence_chain_exists hborn hb ha hqueue sigma centre error hK hsigma hbudget hcentre herror
'''
    return [
        pair('factory accepts arbitrary finite size and preserves the exact prescribed error family',
             factory, 'error', '(fun j k => error j (k+1))'),
        pair('each actual FAST sender FIRE uses exactly its prescribed error index', indexed +
             ''': c.delay j (c.chain.fastExecution.emissionTimes (indexedCadenceSender n j hj))[i]=
    centre j+error j (@v@) := by exact c.realizes j hj i hi
''', 'i', 'i+1'),
        pair('realized delay retains its declared static centre', indexed +
             ''': c.delay j (c.chain.fastExecution.emissionTimes (indexedCadenceSender n j hj))[i]=
    @v@+error j i := by exact c.realizes j hj i hi
''', 'centre j', 'centre (j+1)'),
        pair('native delay is bounded at every real time without an emission-membership premise', chain +
             '''(j : ℕ) (hj : j<n) (time : ℝ) :
    -sigma j≤c.delay j time-centre j ∧ c.delay j time-centre j≤@v@ := by
  exact c.error_bounds j hj time
''', 'sigma j', '0'),
        pair('wire k leaves the physical suffix cell depth minus k',
             '''example {n j : ℕ} (hj : j<n) : (indexedCadenceSender n j hj).val=@v@ := by rfl
''', 'n-j', 'n-1-j'),
        pair('the new link leaves cell one after the actual new parent is prepended',
             '''example (j : ℕ) : indexedCadenceSender (j+1) j (by omega)=@v@ := by
  exact indexedCadenceSender_new j
''', '(0 : Fin (j+1)).succ', '(0 : Fin (j+2))'),
        pair('strong physical extension preserves every exact ordered old sender stream', strong,
             'old.stage.execution.emissionTimes i', '(old.stage.execution.emissionTimes i).map (fun t => t+1)'),
        pair('prefix router transport preserves ordered FIRE dates rather than choosing another witness', transport +
             '''(i : Fin (depth+1)) : (c.transport hp hr hs).stage.execution.emissionTimes i=@v@ := by
  exact c.transport_times hp hr hs i
''', 'c.stage.execution.emissionTimes i', '(c.stage.execution.emissionTimes i).reverse'),
        pair('packet reindexing retains the exact physical stage',
             '''example {d : FiniteCausalChainData} {K T depth m L J m' L' J'}
    (c : ConstructedCadenceChainStage d K T depth m L J)
    (hm : m=m') (hL : L=L') (hJ : J=J') :
    (c.reindex hm hL hJ).stage.final.time=@v@ := by
  exact congrArg (fun s => s.final.time) (c.reindex_stage hm hL hJ)
''', 'c.stage.final.time', 'T+1'),
        pair('full birth history retains preparation FIREs before FAST FIREs', chain +
             '''(i : Fin (n+1)) : c.chain.execution.emissionTimes i=
    @v@++c.chain.fast.stage.execution.emissionTimes i := by exact c.chain.emission_times i
''', 'c.chain.preparation.execution.emissionTimes i', '[]'),
        pair('full source uses the own independent birth coordinates', chain +
             '''(i : Fin (n+1)) : c.chain.source.x i=@v@ := by
  exact c.chain.source_values i
''', '(bornCells i).x 0', '(bornCells (Fin.last n)).x 0'),
        pair('complete history starts at the real common birth clock', chain +
             ''': c.chain.source.time=@v@ := by exact c.chain.source_birth.1
''', '0', '1599/10'),
        pair('whole execution ledger retains actual preparation before actual FAST events', chain +
             ''': c.chain.execution.ledger=@v@ := by exact c.chain.ledger
''', 'c.chain.preparation.execution.ledger.add c.chain.fast.stage.execution.ledger',
             'c.chain.fast.stage.execution.ledger.add c.chain.preparation.execution.ledger'),
        pair('complete execution is saturated at the proved actual horizon', chain +
             ''': CompleteThrough c.chain.execution (@v@) := by exact c.chain.complete
''', 'T', 'T+1'),
        pair('final active gain refers to the same cells own birth gain', chain +
             '''(i : Fin (n+1)) : c.chain.final.x i (.z (cadenceActivePort n i))=
    (bornCells i).x 0 (.z (cadenceActivePort n i))+@v@ := by exact c.chain.gain_target i
''', '12/5', '3/5'),
        pair('both physical phases retain own recovery accumulation', chain +
             '''(i : Fin (n+1)) : c.chain.final.x i .b=(bornCells i).x 0 .b+@v@ := by
  exact c.chain.recovery i
''', '3/10', '1/5'),
        pair('actual fast counts follow physical root-first indices', chain +
             '''(i : Fin (n+1)) : (c.chain.fastExecution.emissionTimes i).length=@v@ := by
  exact c.chain.fast_count i
''', 'K-5-2*(n-i.val)', 'K-5-2*i.val'),
        pair('complete count includes every real preparatory emission', chain +
             ''': c.chain.execution.ledger.emissions.length=@v@ := by exact c.chain.total_emission_count
''', '(n+1)*(K-(n+1)+8)+2', '(n+1)*(K-(n+1)-4)'),
        pair('terminal energy is the actual retained local physical energy', chain +
             '''(i : Fin (n+1)) : c.chain.final.x i .energy=@v@ := by exact c.chain.energy_actual i
''', '(c.chain.fast.stage.cells i).2.final.x 0 .energy', '100'),
        pair('terminal snapshot has consumed all actual pending tokens', chain +
             ''': c.chain.final.pending=@v@ := by exact c.chain.pending
''', '[]', 'sourceTrain (Fin.last n) 0 160 4 K'),
    ]


def main():
    controls = cases()
    with tempfile.TemporaryDirectory(prefix='hybrid-indexed-chain-', dir=ROOT) as tmp:
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

        check('\n'.join(good for _, good, _ in controls), True, 'all positive prescribed-error physical contracts')
        print(f'All{len(controls)} positive prescribed-error physical contracts accepted.', flush=True)
        for name, _, bad in controls:
            check(bad, False, name)
            print(f'{name}: physical conclusion accepted; altered claim rejected.', flush=True)
        print(f'{len(controls)} paired prescribed-error physical controls passed.', flush=True)


if __name__ == '__main__':
    main()
