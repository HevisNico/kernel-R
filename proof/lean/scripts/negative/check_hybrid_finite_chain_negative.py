#!/usr/bin/env python3
"""Paired actual finite-chain, signal, weak-prefix and full-budget controls."""
from pathlib import Path
import subprocess
import tempfile

from scripts.lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[2]
PREFIX = '''import KernelR.HybridCadenceSignalRefinement
import KernelR.HybridFiniteCausalChain
import KernelR.HybridCadenceWeakWarmupK
import KernelR.HybridFiniteCadencePacketGaps
import KernelR.HybridLocalCadenceTailK
import KernelR.HybridIndependentHeadProduct
open KernelR.Hybrid
noncomputable section
'''


def pair(label, template, good, bad):
    assert '@v@' in template and good != bad
    return label, template.replace('@v@', good), template.replace('@v@', bad)


def cases():
    receiver = '''example {θ s port m L J} {packet : KernelR.Chain.Packet m L J} {T}
    (r : LocalCadenceReceiver θ s port packet T) '''
    link = '''example {m L J} {packet : KernelR.Chain.Packet m L J}
    (link : CadencePhysicalLink packet) (previous : KernelR.Chain.Signal)
    (hp : KernelR.Chain.RealizesPacket previous packet) '''
    path = '''example {K N : ℕ} (hN : 0<N) (hK : 4*N+12 ≤ K)
    {packet : KernelR.Chain.Packet 3 (K-8) 0}
    (path : CadenceReceiverPath packet (N-1)) (leaf : KernelR.Chain.Signal)
    (hp : KernelR.Chain.RealizesPacket leaf packet)
    (budget : KernelR.Chain.pathJitter path.jitterSchedule (N-1) ≤ 1/10) '''
    stage = '''example {d : FiniteCausalChainData} {T : ℝ} {n : ℕ}
    (stage : FiniteCausalChainStage d T n) '''
    weak = '''example {θ route s port K}
    (w : ConstructedCadenceWeakWarmupK θ route s port K) '''
    gaps = '''example {m L J} (packet : KernelR.Chain.Packet m L J) (hJ : J ≤ 3/20) '''
    chain_factory = '''example (d : FiniteCausalChainData) (T : ℝ) {ε}
    (leaf : FiniteCausalCell d.leafParameters d.leafSource T)
    (hb : ∀ n,PhysicalBox (d.parameters n) ε)
    (hf : ∀ n,PhysicalInvariant (d.parameters n) (d.source n))
    (hv : ∀ n,RawValid (d.source n))
    (constructHead : ∀ n (stage : FiniteCausalChainStage d T n),
      Nonempty (FiniteCausalCell (d.headParameters n) stage.nextSource T)) (n : ℕ) :
    ∃ stage : FiniteCausalChainStage d T n,
      stage.final.time=T+@v@ ∧ stage.final.pending=[] ∧
      PhysicalInvariant (d.parameters n) stage.final ∧ RawValid stage.final := by
  obtain ⟨stage⟩ := finite_causal_chain_exists d T leaf hb hf hv constructHead n
  exact ⟨stage,by simpa using stage.complete.1,stage.pending,stage.physical,stage.raw_valid⟩
'''
    weak_factory = '''example {θ ε route} (hb : PhysicalBox θ ε) (s : Snapshot 1) (port : Port)
    (hf : PhysicalInvariant θ s) (hv : RawValid s) (hs : PreparedSection s 0)
    (hq : s.x 0 .q=1/10) (hz : s.x 0 (.z port) ≤ Real.log (3/10)+1/100000)
    (hr : s.raw 0 port=some s.time) (ho : ∀ q,q ≠ port→s.raw 0 q=none)
    (hqueue : s.pending=sourceTrain 0 port (s.time+4) 4 3) :
    ∃ w : ConstructedCadenceWeakWarmupK θ route s port 4,
      w.final.time=s.time+12 ∧ w.final.pending=@v@ ∧
      w.execution.ledger.emissions=[] ∧ CompleteThrough w.execution (s.time+12) := by
  obtain ⟨w⟩ := constructed_cadence_weak_warmup_k_exists (route:=route) hb s port 4
    (by norm_num) hf hv hs hq hz hr ho hqueue
  refine ⟨w,w.date,?_,w.emissions,w.complete⟩
  rw [w.final_eq]
  simpa [sourceTrain] using w.pending
'''
    tailk = '''example {θ source port n T} (t : LocalCadenceTailK θ source port n T) '''
    product = '''example {n θ θH route s u a b}
    {tail : @Execution n θ route s u} {head : @Execution 1 θH (fun _ _ => []) a b}
    (product : IndependentHeadProduct tail head) '''
    return [
        pair('actual receiver output signal has the exact relay event count', receiver +
             ': r.outputSignal.count=@v@ := by exact r.output_signal_realizes.1\n',
             '(m+2)+(L-4)', '(m+2)+(L-4)+1'),
        pair('physical input signal includes every actual source token', receiver +
             ': r.inputSignal.count=@v@ := by exact r.input_signal_realizes.1\n', 'm+L', 'm+L-1'),
        pair('input packet refinement cannot be transferred to an unrelated outgoing signal', receiver +
             '''(other : KernelR.Chain.Signal) (i : ℕ) (hi : i<m+L) :
    @v@.time i=packet.actual i := by exact r.input_signal_realizes.2 i hi
''', 'r.inputSignal', 'other'),
        pair('output refinement retains actual rather than ideal event dates', receiver +
             '''(i : ℕ) (hi : i<(m+2)+(L-4)) :
    r.outputSignal.time i=r.outputPacket.@v@ i := by exact r.output_signal_realizes.2 i hi
''', 'actual', 'ideal'),
        pair('wide residual high timing does not assert the older narrow margins', receiver +
             ''': @v@ := by exact r.signal_witness.first_bounds
''', '4/25 ≤ r.signal_witness.firstHigh ∧ r.signal_witness.firstHigh ≤ 13/50',
             '1/5 ≤ r.signal_witness.firstHigh ∧ r.signal_witness.firstHigh ≤ 1/4'),
        pair('wire refinement keeps each physical delay error', link +
             '''(i : ℕ) (hi : i<previous.count) : link.receiver.inputSignal.time i=
    previous.time i+link.delay@v@ := by exact (link.wire_dates previous hp).2 i hi
''', '+link.error i', ''),
        pair('arbitrary depth node count follows from actual dependent receiver paths', path +
             '''(i : ℕ) (hi : i<N) : (path.signals leaf i).count=@v@ := by
  exact (path.realized_counts hN hK leaf hp budget).1 i hi
''', 'K-5-2*i', 'K-4-2*i'),
        pair('the physical root count is K minus twice N minus three', path +
             ''': (path.signals leaf (N-1)).count=@v@ := by
  exact path.realized_root_count hN hK leaf hp budget
''', 'K-2*N-3', 'K-2*N-2'),
        pair('the arbitrary finite total retains the exact quadratic count', path +
             ''': (Finset.range N).sum (fun i => (path.signals leaf i).count)=@v@ := by
  exact (path.realized_counts hN hK leaf hp budget).2
''', 'N*(K-N-4)', 'N*(K-N-3)'),
        pair('path budget is the proved one tenth rather than a smaller invented bound', path +
             '''(i : ℕ) (hi : i<N) : KernelR.Chain.pathJitter path.jitterSchedule i ≤ @v@ := by
  exact (path.realized_chain hN leaf hp budget i hi).2
''', '1/10', '1/20'),
        pair('every node retains its cumulative jitter instead of resetting it', path +
             '''(i : ℕ) (hi : i<N) : KernelR.Chain.HasPacket (path.signals leaf i)
    (KernelR.Chain.prefixLength i) (KernelR.Chain.tailLength K i) @v@ := by
  exact (path.realized_chain hN leaf hp budget i hi).1
''', '(KernelR.Chain.pathJitter path.jitterSchedule i)', '0'),
        pair('actual receiver witness does not give a law for a different outgoing stream', receiver +
             '''(other : KernelR.Chain.Signal) : Nonempty
    (KernelR.Chain.CadenceRelayWitness packet r.tail_size @v@) := by exact ⟨r.signal_witness⟩
''', 'r.outputSignal', 'other'),
        pair('dependent path jitter adds the next real link budget',
             '''example {m L J} {packet : KernelR.Chain.Packet m L J} {n}
    (link : CadencePhysicalLink packet) (rest : CadenceReceiverPath link.outputPacket n) (i : ℕ) :
    KernelR.Chain.pathJitter (CadenceReceiverPath.jitterSchedule (.cons link rest)) (i+1)=
      @v@+KernelR.Chain.pathJitter rest.jitterSchedule i := by exact rest.jitter_head link i
''', 'link.sigma', '0'),
        pair('the only globally pre-existing sources belong to the shifted leaf',
             '''example (d : FiniteCausalChainData) (n : ℕ) (token : Delivery (n+1))
    (ht : token ∈ (d.source n).pending) : token.cell=@v@ := by exact d.source_external_only n token ht
''', 'Fin.last n', '0'),
        pair('global initial queue comes from the original leaf rather than a local head queue',
             '''example (d : FiniteCausalChainData) (n : ℕ) : (d.source n).pending=
    @v@.pending.map (FiniteCausalChainData.liftLeafDelivery n) := by exact d.source_pending n
''', 'd.leafSource', '(d.headSource n)'),
        pair('two extensions shift actual external tokens twice without retargeting them',
             '''example (token : Delivery 1) : FiniteCausalChainData.liftLeafDelivery 2 token=@v@ := by rfl
''', 'token.succ.succ', '(⟨0,token.port,token.due⟩ : Delivery 3)'),
        pair('adding physical cells inserts no further external source occurrence',
             '''example (d : FiniteCausalChainData) (n : ℕ) :
    (d.source n).pending.length=d.leafSource.pending.length@v@ := by exact d.source_queue_length n
''', '', '+n'),
        pair('each new physical head receives the preceding actual FIRE ledger queue', stage +
             ''': stage.nextSource.pending=@v@ := by rfl
''', 'stage.execution.headInputQueue (d.contacts n)', 'd.leafSource.pending'),
        pair('the global per-cell emission list is its retained actual local trace', stage +
             '''(i : Fin (n+1)) : stage.execution.emissionTimes i=@v@ := by exact stage.emission_times i
''', '(stage.cells i).2.execution.emissionTimes 0', '[]'),
        pair('global cell energy is its own actual local endpoint energy', stage +
             '''(i : Fin (n+1)) : stage.final.x i .energy=@v@ := by exact stage.energy_actual i
''', '(stage.cells i).2.final.x 0 .energy', '100'),
        pair('the complete finite causal endpoint has no leftover wire queue', stage +
             ': stage.final.pending=@v@ := by exact stage.pending\n', '[]', '[⟨0,2,T⟩]'),
        pair('true induction constructs every finite stage without a supplied global reaching trace',
             chain_factory, '0', '1'),
        pair('weak warmup gains exactly three own ERROR doses', weak +
             ': w.final.x 0 (.z port)=s.x 0 (.z port)+@v@ := by exact w.gain_target\n', '9/5', '12/5'),
        pair('weak warmup ledger contains the full actual ERROR dose', weak +
             ': w.execution.ledger.error 0 port=@v@ := by exact w.error_target\n', '9/5', '3/5'),
        pair('weak warmup adds no protected MARK', weak +
             '(q : Port) : w.execution.ledger.mark 0 q=@v@ := by exact w.mark_zero q\n', '0', '1/10'),
        pair('arbitrary K retains exactly the remaining K minus four source occurrences', weak +
             ': w.final.pending=sourceTrain 0 port (s.time+16) 4 (@v@) := by exact w.pending\n', 'K-4', 'K-3'),
        pair('three actual new weak source deliveries keep their original dates', weak +
             ''': w.execution.deliveries=[⟨0,port,s.time+4⟩,⟨0,port,s.time+8⟩,⟨0,port,s.time+@v@⟩] := by
  exact w.deliveries
''', '12', '16'),
        pair('weak warmup reaches the actual third new source date', weak +
             ': w.final.time=s.time+@v@ := by exact w.date\n', '12', '16'),
        pair('weak warmup preserves own recovery instead of adding a MARK increment', weak +
             ': w.final.x 0 .b=s.x 0 .b@v@ := by exact w.recovery\n', '', '+1/10'),
        pair('minimum K four is physically constructed and leaves an empty future queue',
             weak_factory, '[]', '[⟨0,port,s.time+16⟩]'),
        pair('full jitter budget prefix gaps use the proved seven point one to eight point six range', gaps +
             '''(i : ℕ) (hi : i+1<m) : @v@ := by exact packet.full_budget_prefix_gap hJ i hi
''', '71/10 ≤ packet.actual (i+1)-packet.actual i ∧ packet.actual (i+1)-packet.actual i ≤ 43/5',
             '36/5 ≤ packet.actual (i+1)-packet.actual i ∧ packet.actual (i+1)-packet.actual i ≤ 17/2'),
        pair('full jitter transition admits three point seven to four point four', gaps +
             ''': @v@ := by exact packet.full_budget_transition_gap hJ
''', '37/10 ≤ packet.actual m-packet.actual (m-1) ∧ packet.actual m-packet.actual (m-1) ≤ 22/5',
             '19/5 ≤ packet.actual m-packet.actual (m-1) ∧ packet.actual m-packet.actual (m-1) ≤ 43/10'),
        pair('full jitter tail range does not reuse the one tenth budget bounds', gaps +
             '''(i : ℕ) (hi : m ≤ i) : @v@ := by exact packet.full_budget_tail_gap hJ i hi
''', '37/10 ≤ packet.actual (i+1)-packet.actual i ∧ packet.actual (i+1)-packet.actual i ≤ 43/10',
             '19/5 ≤ packet.actual (i+1)-packet.actual i ∧ packet.actual (i+1)-packet.actual i ≤ 21/5'),
        pair('symbolic tail gap accounts for both independent phase errors',
             '''example {m L J} (packet : KernelR.Chain.Packet m L J) (i : ℕ) (hi : m ≤ i) :
    @v@ ≤ packet.actual (i+1)-packet.actual i := by exact (packet.finite_tail_gap i hi).1
''', '4-2*J', '4-J'),
        pair('every actual full-budget input gap is at least three point seven', gaps +
             '''(i : ℕ) : @v@ ≤ packet.actual (i+1)-packet.actual i := by exact packet.full_budget_actual_gap hJ i
''', '37/10', '4'),
        pair('full-budget actual event dates increase rather than run backwards', gaps +
             ': @v@ packet.actual := by exact packet.full_budget_strict_mono hJ\n', 'StrictMono', 'StrictAnti'),
        pair('arbitrary tail length retains the actual second and high FIRE count', tailk +
             ': (t.execution.emissionTimes 0).length=@v@ := by exact t.emission_count\n', 'n+2', 'n+3'),
        pair('tail construction consumes every remaining regular source occurrence', tailk +
             ': t.execution.deliveries=sourceTrain 0 port (source.time+4) 4 (@v@) := by exact t.deliveries\n',
             'n+2', 'n+1'),
        pair('the mixed tail learns only the own additional ERROR dose', tailk +
             ': t.final.x 0 (.z port)=source.x 0 (.z port)+@v@ := by exact t.gain_target\n', '3/5', '6/5'),
        pair('tail mixed MARK adds exactly one tenth own recovery', tailk +
             ': t.final.x 0 .b=source.x 0 .b@v@ := by exact t.recovery_gain\n', '+1/10', ''),
        pair('the true high train reaches source plus twelve plus four n', tailk +
             ': t.high.final.time=source.time+@v@+4*(n:ℝ) := by exact t.high_date\n', '12', '8'),
        pair('the terminal tail is READY at rest with empty queue and absent RAW', tailk +
             ''': t.final.pending=[] ∧ t.final.main 0=.ready ∧ t.final.x 0 .q=1/10 ∧
    (∀ q,t.final.raw 0 q=@v@) := by
  exact ⟨t.pending,(t.ready 0).ready,t.charge,t.raw_none 0⟩
''', 'none', 'some T'),
        pair('quiet tail endpoint energy is the actual retained relaxation', tailk +
             ''': t.final.x 0 .energy=@v@ := by rw [t.final_state]
''', '(quietAt t.high.final T).x 0 .energy', '100'),
        pair('independent product keeps the real external head sources as well as shifted tail sources', product +
             ''': (s.prependQueued a (independentHeadQueue s a)).pending=@v@ := by rfl
''', 'a.pending.map (Delivery.head (n:=n)) ++ s.pending.map Delivery.succ',
             's.pending.map Delivery.succ'),
        pair('two emitting physical sides both contribute their actual FIREs', product +
             '''(hTail : tail.ledger.emissions ≠ []) (hHead : head.ledger.emissions ≠ []) :
    product.execution.ledger.emissions.length=@v@ := by exact product.emission_count
''', 'tail.ledger.emissions.length+head.ledger.emissions.length', 'head.ledger.emissions.length'),
        pair('independent weaving retains real deliveries on both sides', product +
             ': product.execution.deliveries.length=@v@ := by exact product.delivery_count\n',
             'tail.deliveries.length+head.deliveries.length', 'tail.deliveries.length'),
        pair('independent product retains each ordered local FIRE calendar', product +
             '''(i : Fin n) : (product.execution.emissionTimes 0,product.execution.emissionTimes i.succ)=
    (head.emissionTimes 0,@v@) := by
  exact Prod.ext product.head_emission_times (product.tail_emission_times i)
''', 'tail.emissionTimes i', 'head.emissionTimes 0'),
        pair('independent product preserves each actual physical energy endpoint', product +
             '''(i : Fin n) : ((u.prependQueued b product.pending).x 0 .energy,
      (u.prependQueued b product.pending).x i.succ .energy)=@v@ := by
  exact Prod.ext (congrFun product.head_values .energy) (congrFun (product.tail_values i) .energy)
''', '(b.x 0 .energy,u.x i .energy)', '(100,100)'),

    ]


def main():
    controls = cases()
    assert len(controls) == 48
    with tempfile.TemporaryDirectory(prefix='hybrid-finite-chain-', dir=ROOT) as tmp:
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

        check('\n'.join(good for _, good, _ in controls), True, 'all positive finite physical-chain contracts')
        print('All48 positive finite physical-chain contracts accepted.', flush=True)
        for name, _, bad in controls:
            check(bad, False, name)
            print(f'{name}: physical conclusion accepted; altered claim rejected.', flush=True)
        print(f'{len(controls)} paired finite physical-chain controls passed.', flush=True)


if __name__ == '__main__':
    main()
