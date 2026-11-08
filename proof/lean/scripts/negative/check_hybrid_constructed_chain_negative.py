#!/usr/bin/env python3
"""Paired actual prepared-chain construction and complete birth-chain controls."""
from pathlib import Path
import subprocess
import tempfile

from scripts.lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[2]
PREFIX = '''import KernelR.HybridBirthCadenceChain
open KernelR.Hybrid
noncomputable section
'''


def pair(label, template, good, bad):
    assert '@v@' in template and good != bad
    return label, template.replace('@v@', good), template.replace('@v@', bad)


def cases():
    domain = '''example {d ε n K sigma centre delay}
    (domain : PreparedCadenceChainDomain d ε n K sigma centre delay) '''
    stage = '''example {d K T depth m L J}
    (c : ConstructedCadenceChainStage d K T depth m L J) '''
    extension = '''example {d T n} {stage : FiniteCausalChainStage d T n}
    {head : FiniteCausalCell (d.headParameters n) stage.nextSource T}
    (extension : FiniteCausalExtension stage head) '''
    born = '''example {n θ bornCells K sigma centre delay T}
    (c : @ConstructedBirthCadenceChain n θ bornCells K sigma centre delay T) '''
    factory = domain + ''': ∃ c : ConstructedCadenceChainStage d K
      (cadenceChainTerminal n K) n (KernelR.Chain.prefixLength n)
      (KernelR.Chain.tailLength K n) (KernelR.Chain.pathJitter sigma n),
      c.stage.final.time=cadenceChainTerminal n K+@v@ ∧
      PhysicalInvariant (d.parameters n) c.stage.final ∧ RawValid c.stage.final := by
  obtain ⟨c⟩ := domain.construct_exists
  exact ⟨c,by simpa using c.stage.complete.1,c.stage.physical,c.stage.raw_valid⟩
'''
    step = domain + '''{j m L J} (hj : j<n) (hL : 5≤L) (hJ : J+sigma j≤3/20)
    (old : ConstructedCadenceChainStage d K (cadenceChainTerminal n K) j m L J) :
    Nonempty (ConstructedCadenceChainStage d K (cadenceChainTerminal n K)
      (j+1) (m+2) (L-4) (@v@)) := by
  exact domain.step_exists hj hL hJ old
'''
    birth_factory = '''example {n θ bornCells K ε}
    (hborn : ∀ i : Fin (n+1), BirthState (bornCells i))
    (hb : @PhysicalBox (n+1) θ ε) (ha : ∀ i q, (bornCells i).aux 0 q=.ready)
    (hqueue : ∀ i, (bornCells i).pending=sourceTrain 0 (finiteChainPreparationPort n i) 0 8 16)
    (sigma centre : ℕ → ℝ) (delay : ℕ → ℝ → ℝ)
    (hK : 4*(n+1)+12≤K) (hsigma : ∀ j, 0≤sigma j)
    (hbudget : KernelR.Chain.pathJitter sigma n≤3/20)
    (hcentre : ∀ j, j<n → (3/10:ℝ)+sigma j≤centre j ∧ centre j≤2/5-sigma j)
    (herror : ∀ j, j<n → ∀ time, -sigma j≤delay j time-centre j ∧ delay j time-centre j≤sigma j) :
    ∃ c : ConstructedBirthCadenceChain θ bornCells K sigma centre delay (cadenceChainTerminal n K),
      CompleteThrough c.execution (cadenceChainTerminal n K+@v@) := by
  obtain ⟨c⟩ := birth_cadence_chain_exists hborn hb ha hqueue sigma centre delay
    hK hsigma hbudget hcentre herror
  exact ⟨c,by simpa using c.complete⟩
'''
    return [
        pair('the static prepared domain constructs an actual physical terminal at every finite depth',
             factory, '0', '1'),
        pair('the inductive physical constructor retains cumulative link jitter', step, 'J+sigma j', 'J'),
        pair('actual per-cell FIRE counts use the reversed physical index', stage +
             '''(i : Fin (depth+1)) : (c.stage.execution.emissionTimes i).length=@v@ := by exact c.counts i
''', 'K-5-2*(depth-i.val)', 'K-5-2*i.val'),
        pair('the actual root loses exactly two FIREs per physical extension', stage +
             ': (c.stage.execution.emissionTimes 0).length=@v@ := by exact c.root_emission_count_nodes\n',
             'K-2*(depth+1)-3', 'K-2*(depth+1)-2'),
        pair('the complete actual fast ledger has the finite quadratic total', stage +
             '''(hK : 4*(depth+1)+12≤K) : c.stage.execution.ledger.emissions.length=@v@ := by
  exact c.actual_emission_count hK
''', '(depth+1)*(K-(depth+1)-4)', '(depth+1)*(K-(depth+1)-3)'),
        pair('the retained root packet counts precisely the actual output occurrences', stage +
             ': m+L=@v@ := by exact c.packet_count\n', 'K-5-2*depth', 'K-4-2*depth'),
        pair('the constructor calendar contains actual dates rather than ideal dates', stage +
             ''': c.stage.execution.emissionTimes 0=List.ofFn (fun i : Fin (m+L) => c.packet.@v@ i.val) := by
  exact c.calendar
''', 'actual', 'ideal'),
        pair('own gain separates the actual leaf dose from each receiving head dose', stage +
             '''(i : Fin (depth+1)) : c.stage.final.x i (.z (cadenceActivePort depth i))=
    (d.source depth).x i (.z (cadenceActivePort depth i))+@v@ := by exact c.gain_target i
''', '(if i.val=depth then (12/5 : ℝ) else 3/5)', '(12/5 : ℝ)'),
        pair('other gains retain their own source values', stage +
             '''(i : Fin (depth+1)) (p : Port) (hp : p≠cadenceActivePort depth i) :
    c.stage.final.x i (.z p)=(d.source depth).x i (.z p)@v@ := by exact c.gain_other i p hp
''', '', '+3/5'),
        pair('each fast physical cell retains exactly two recovery doses', stage +
             '''(i : Fin (depth+1)) : c.stage.final.x i .b=(d.source depth).x i .b+@v@ := by exact c.recovery i
''', '1/5', '1/10'),
        pair('terminal energy comes from the actual retained local endpoint', stage +
             '''(i : Fin (depth+1)) : c.stage.final.x i .energy=@v@ := by exact c.actual_energy i
''', '(c.stage.cells i).2.final.x 0 .energy', '100'),
        pair('the complete physical chain has absent RAW on every port', stage +
             '''(i : Fin (depth+1)) (p : Port) : c.stage.final.raw i p=@v@ := by exact c.stage.raw_none i p
''', 'none', 'some T'),
        pair('the completed physical chain has no leftover wire token', stage +
             ': c.stage.final.pending=@v@ := by exact c.stage.pending\n', '[]', '[⟨0,2,T⟩]'),
        pair('the global initial queue contains precisely K external source occurrences', domain +
             '''(j : ℕ) : (d.source j).pending.length=@v@ := by exact domain.external_source_count j
''', 'K', 'K+j'),
        pair('every pre-existing external token is assigned to the shifted leaf', domain +
             '''(j : ℕ) (token : Delivery (j+1)) (ht : token∈(d.source j).pending) :
    token.cell=@v@ := by exact d.source_external_only j token ht
''', 'Fin.last j', '0'),
        pair('the next head receives its actual causal wire queue without a preload', stage +
             ''': c.stage.nextSource.pending=@v@ := by rfl
''', 'c.stage.execution.headInputQueue (d.contacts depth)', '(d.headSource depth).pending'),
        pair('prepared receiver source queues are empty before actual wire emission', domain +
             '''(j : ℕ) (hj : j<n) : (d.headSource j).pending=@v@ := by exact domain.head_queue j hj
''', '[]', '[⟨0,2,160⟩]'),
        pair('native delay is evaluated at the actual emission time rather than replaced by its centre', domain +
             '''{m L J} (packet : KernelR.Chain.Packet m L J) (j : ℕ) (hj : j<n) (i : ℕ) :
    (packet.sampleWireDelay (delay j) (centre j) (sigma j) (domain.sigma_nonneg j)
      (domain.error_bounds j hj)).actual i=packet.actual i+@v@ := by
  exact packet.sample_wire_delay_actual _ _ _ _ _ i
''', 'delay j (packet.actual i)', 'centre j'),
        pair('native delay bounds preserve the full three tenths to two fifths domain', domain +
             '''(j : ℕ) (hj : j<n) (time : ℝ) : @v@ := by exact domain.delay_bounds j hj time
''', '(3/10 : ℝ)≤delay j time ∧ delay j time≤2/5',
             '(1/3 : ℝ)≤delay j time ∧ delay j time≤2/5'),
        pair('the cumulative domain budget is three twentieths rather than one tenth', domain +
             ': KernelR.Chain.pathJitter sigma n≤@v@ := by exact domain.jitter_budget\n', '3/20', '1/10'),
        pair('the actual packet envelope starts at the common fast opening', stage +
             '''(i : Fin (m+L)) : @v@≤c.packet.actual i.val := by exact c.envelope.lower i
''', '160', '161'),
        pair('the actual upper envelope retains the depth-dependent latency allowance', stage +
             '''(i : Fin (m+L)) : c.packet.actual i.val≤
    160+4*((K-1 : ℕ) : ℝ)+(11/10)*(depth : ℝ)+@v@ := by exact c.envelope.upper i
''', '9/10', '0'),
        pair('the physical packet is inside the open gate with a strict closing margin', stage +
             '''(i : Fin (m+L)) : 160≤c.packet.actual i.val ∧
    c.packet.actual i.val<finiteCadenceTerminal 160 (depth+1) K+@v@ := by
  exact c.envelope.gate (by omega : depth<depth+1) i
''', '1', '-8'),
        pair('sampled actual arrivals leave the complete physical receiver return margin', stage +
             '''(delay : ℝ→ℝ) (centre sigma : ℝ) (hsigma : 0≤sigma)
    (herr : ∀ time, -sigma≤delay time-centre ∧ delay time-centre≤sigma)
    (hd : ∀ time, (3/10 : ℝ)≤delay time ∧ delay time≤2/5) (i : Fin (m+L)) :
    (c.packet.sampleWireDelay delay centre sigma hsigma herr).actual i.val+@v@≤
      finiteCadenceTerminal 160 (depth+1) K := by
  exact c.envelope.received_terminal (by omega : depth<depth+1) delay centre sigma hsigma herr hd i
''', '19/5', '8'),
        pair('strong extension retains the actual newly constructed head FIRE calendar', extension +
             ''': extension.next.execution.emissionTimes 0=@v@ := by exact extension.head_times
''', 'head.execution.emissionTimes 0', 'stage.execution.emissionTimes 0'),
        pair('strong extension shifts each retained old FIRE calendar exactly once', extension +
             '''(i : Fin (n+1)) : extension.next.execution.emissionTimes i.succ=@v@ := by exact extension.tail_times i
''', 'stage.execution.emissionTimes i', 'head.execution.emissionTimes 0'),
        pair('strong extension preserves actual head and tail endpoint energies', extension +
             '''(i : Fin (n+1)) : (extension.next.final.x 0 .energy,extension.next.final.x i.succ .energy)=@v@ := by
  exact Prod.ext extension.head_energy_actual (extension.tail_energy_actual i)
''', '(head.final.x 0 .energy,stage.final.x i .energy)', '(100,100)'),
        pair('strong extension retains the complete weave execution including FIRE metadata', extension +
             ': HEq extension.next.execution @v@ := by exact extension.execution_eq\n',
             'extension.weave.execution', 'stage.execution'),
        pair('the independent birth factory constructs the complete one-router global history', birth_factory, '0', '1'),
        pair('the complete global source directly retains every independent birth coordinate', born +
             '''(i : Fin (n+1)) : c.source.x i=@v@ := by exact c.source_values i
''', '(bornCells i).x 0', 'c.final.x i'),
        pair('the actual whole-birth endpoint is ready with resting charge and empty RAW and queue', born +
             ''': c.final.time=T ∧ (∀ i, ReadyCoordinates c.final i) ∧
    (∀ i,c.final.x i .q=@v@) ∧ (∀ i q,c.final.raw i q=none) ∧ c.final.pending=[] := by
  exact ⟨c.date,c.ready,c.charge,c.raw_none,c.pending⟩
''', '1/10', '1/4'),
        pair('whole-history cell FIRE counts include the actual preparatory FIREs', born +
             '''(i : Fin (n+1)) : (c.execution.emissionTimes i).length=@v@+(K-5-2*(n-i.val)) := by
  exact c.cumulative_count i
''', 'finiteChainPreparationCount n i', '0'),
        pair('each complete birth chain learns exactly its own twelve-fifths gain', born +
             '''(i : Fin (n+1)) : c.final.x i (.z (cadenceActivePort n i))=
    (bornCells i).x 0 (.z (cadenceActivePort n i))+@v@ := by exact c.gain_target i
''', '12/5', '3/5'),
        pair('each complete birth chain retains its own three-tenths recovery increase', born +
             '''(i : Fin (n+1)) : c.final.x i .b=(bornCells i).x 0 .b+@v@ := by exact c.recovery i
''', '3/10', '1/5'),
        pair('the complete physical ledger includes preparation and fast ERROR MARK and FIRE data', born +
             ''': c.execution.ledger=@v@ := by exact c.ledger
''', 'c.preparation.execution.ledger.add c.fast.stage.execution.ledger', 'c.fast.stage.execution.ledger'),
        pair('the actual whole-birth FIRE total includes the preparatory count', born +
             ': c.execution.ledger.emissions.length=@v@ := by exact c.total_emission_count\n',
             '(n+1)*(K-(n+1)+8)+2', '(n+1)*(K-(n+1)-4)'),
    ]


def main():
    controls = cases()
    assert len(controls) == 36
    with tempfile.TemporaryDirectory(prefix='hybrid-constructed-chain-', dir=ROOT) as tmp:
        path = Path(tmp) / 'Check.lean'
        command = lean_check_command(tmp)

        def check(source, expected, name):
            path.write_text(PREFIX + source)
            result = subprocess.run([*command, str(path)], cwd=ROOT, text=True,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=240)
            if (result.returncode == 0) != expected:
                raise SystemExit(f'{name}: unexpected result:\n{result.stdout}')
            if not expected and 'error:' not in result.stdout:
                raise SystemExit(f'{name}: failed without a Lean diagnostic:\n{result.stdout}')

        check('\n'.join(good for _, good, _ in controls), True, 'all positive constructed-chain contracts')
        print('All36 positive constructed-chain contracts accepted.', flush=True)
        for name, _, bad in controls:
            check(bad, False, name)
            print(f'{name}: physical conclusion accepted; altered claim rejected.', flush=True)
        print(f'{len(controls)} paired constructed-chain controls passed.', flush=True)


if __name__ == '__main__':
    main()
