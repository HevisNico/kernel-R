#!/usr/bin/env python3
"""Paired controls for direct leaf preparation and initial-program restriction."""
from pathlib import Path
import subprocess
import tempfile

from scripts.lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[2]
PREFIX = '''import KernelR.HybridFiniteChainLeafPreparation
import KernelR.HybridLocalSourceRestriction
import KernelR.HybridCadenceLeafFirstMarkK
import KernelR.HybridBirthCadenceLeafK
import KernelR.HybridFiniteChainRelayPreparation
open KernelR.Hybrid
noncomputable section
attribute [local instance] Classical.propDecidable
'''


def pair(label, template, good, bad):
    assert '@v@' in template and good != bad
    return label, template.replace('@v@', good), template.replace('@v@', bad)


def cases():
    leaf = '''example {θ born future} (c : FiniteChainLeafPreparation θ born future) '''
    mark = '''example {θ s p K}
    {w : ConstructedCadenceWeakWarmupK θ (fun _ _=>[]) s p K}
    (c : ConstructedCadenceLeafFirstMarkK w) '''
    factory = '''example {θ ε born} (hborn : @BirthState 1 born)
    (hb : PhysicalBox θ ε) (ha : ∀ p,born.aux 0 p=.ready)
    (future : List (Delivery 1))
    (hqueue : born.pending=sourceTrain 0 1 0 8 16++future)
    (hf : ∀ d∈future,(160:ℝ)≤d.due) :
    ∃ c : FiniteChainLeafPreparation θ born future,
      CompleteThrough c.execution (@v@) := by
  obtain ⟨c⟩ := finite_chain_leaf_preparation_exists hborn hb ha future hqueue hf
  exact ⟨c,c.complete⟩
'''
    restriction = '''example {θ s u}
    (e : @Execution 1 θ (fun _ _=>[]) s u) (cutoff : ℝ) (ht : u.time≤cutoff) :
    ∃ f : Execution θ (fun _ _=>[]) (retainSourcesThrough cutoff s)
      (retainSourcesThrough cutoff u), @v@ := by
  obtain ⟨f,hL,hD⟩ := e.retainSourcesThrough_emptyRoute cutoff ht
  exact ⟨f,PROOF⟩
'''
    born_leaf = '''example {θ born K terminal}
    (c : ConstructedBirthCadenceLeafK θ born K terminal) '''
    relay = '''example {θ born} (r : FiniteChainRelayPreparation θ born) '''
    born_factory = '''example {θ ε born} (hborn : @BirthState 1 born)
    (hb : PhysicalBox θ ε) (ha : ∀ p,born.aux 0 p=.ready)
    (K : ℕ) (terminal : ℝ) (hK : 9≤K)
    (hqueue : born.pending=sourceTrain 0 1 0 8 16++sourceTrain 0 0 160 4 K)
    (hterminal : (160:ℝ)+4*(K:ℝ)<terminal) :
    ∃ c : ConstructedBirthCadenceLeafK θ born K terminal,
      (c.execution.emissionTimes 0).length=@v@ := by
  obtain ⟨c⟩ := birth_cadence_leaf_k_exists hborn hb ha K terminal hK hqueue hterminal
  exact ⟨c,c.emission_count⟩
'''
    relay_factory = '''example {θ ε born} (hborn : @BirthState 1 born)
    (hb : PhysicalBox θ ε) (ha : ∀ p,born.aux 0 p=.ready)
    (hqueue : born.pending=sourceTrain 0 2 0 8 16) :
    ∃ r : FiniteChainRelayPreparation θ born,
      Nonempty (@Execution 1 @v@ (fun _ _=>[]) born r.final) := by
  obtain ⟨r⟩ := finite_chain_relay_preparation_exists hborn hb ha hqueue
  exact ⟨r,⟨r.execution⟩⟩
'''
    return [
        pair('the direct birth factory constructs a complete preparation without a reaching trace',
             factory, '1599/10', '160'),
        pair('sixteen actual inputs produce fourteen FIREs rather than one output per input',
             leaf+': (c.execution.emissionTimes 0).length=@v@ := by exact c.emission_count\n',
             '14', '16'),
        pair('the direct source program includes the genuine source at birth', leaf+
             ': c.execution.deliveries=sourceTrain 0 1 @v@ 8 16 := by exact c.deliveries\n',
             '0', '8'),
        pair('the nominal fast preparation port receives exactly one ERROR dose', leaf+
             ': c.final.x 0 (.z 1)=born.x 0 (.z 1)+@v@ := by exact c.gain_target\n',
             '3/5', '9/5'),
        pair('inactive ports retain their own birth gains', leaf+
             '(p : Port) (hp : p≠1) : c.final.x 0 (.z p)=born.x 0 (.z p)@v@ := by exact c.gain_other p hp\n',
             '', '+3/5'),
        pair('the one protected preparation input adds one own recovery dose', leaf+
             ': c.final.x 0 .b=born.x 0 .b+@v@ := by exact c.recovery\n',
             '1/10', '3/10'),
        pair('the true SLOW return supplies exact resting main charge', leaf+
             ': c.final.x 0 .q=@v@ := by exact c.charge\n', '1/10', '1/4'),
        pair('every completed preparation RAW current is absent', leaf+
             '(p : Port) : c.final.raw 0 p=@v@ := by exact c.raw_none 0 p\n',
             'none', 'some 120'),
        pair('the initial future program is retained occurrence for occurrence', leaf+
             ': c.final.pending=@v@ := by exact c.pending\n', 'future', '[]'),
        pair('the common preparation cut is strictly before the fast source at160', leaf+
             ': c.final.time=@v@ := by exact c.date\n', '1599/10', '160'),
        pair('the learned prefix actually consumes the last preparation source120', leaf+
             ': c.learnedPrefix.final.time=@v@ := by exact c.source120_date\n', '120', '112'),
        pair('the final source receives its own short physical return before quiet waiting', leaf+
             ': c.lastCycle.returned.final.time=@v@ := by exact c.returned_date\n',
             '1269/10', '255/2'),
        pair('terminal energy is the true forced-ODE quiet endpoint rather than a reset', leaf+
             ': c.final.x 0 .energy=@v@ := by rfl\n',
             '(quietAt c.lastCycle.returned.final (1599/10)).x 0 .energy', '100'),
        pair('the actual first FIRE and last FIRE surround the retained learned-prefix calendar', leaf+
             ': c.execution.emissionTimes 0=@v@ := by exact c.calendar\n',
             '[c.fire.final.time]++c.learnedPrefix.execution.emissionTimes 0++[c.lastCycle.fire.final.time]',
             '[c.fire.final.time]++c.learnedPrefix.execution.emissionTimes 0'),
        pair('the next prepared source at24 retains its new physical RAW origin', leaf+
             ': c.source24.final.raw 0 1=some @v@ := by\n'
             '  simpa only [c.source24.date] using c.source24.raw_active\n',
             '24', '16'),
        pair('the low-recovery source16 retains its actual exponential SLOW charge', leaf+
             ': c.slow16.final.x 0 .q=@v@ := by exact c.slow16.charge_clock\n',
             '(1/4)*Real.exp (-c.source8.final.x 0 .b*(16-(c.source8.final.time+c.fire.latency+1)))',
             '1/10'),
        pair('completion saturates the actual quiet endpoint and future queue', leaf+
             ': CompleteThrough c.execution (@v@) := by exact c.complete\n',
             '1599/10', '1599/10+1'),
        pair('initial-program restriction preserves the full actual ledger including FIREs',
             restriction.replace('PROOF', 'hL'), 'f.ledger=e.ledger', 'f.ledger=Ledger.zero'),
        pair('initial-program restriction preserves every actual delivered occurrence',
             restriction.replace('PROOF', 'hD'), 'f.deliveries=e.deliveries', 'f.deliveries=[]'),
        pair('restriction retains a source exactly on the inclusive cutoff',
             '''example (s : Snapshot 1) (cutoff : ℝ) :
    (retainSourcesThrough cutoff {s with pending:=[⟨0,0,cutoff⟩]}).pending=@v@ := by
  simp [retainSourcesThrough]
''', '[⟨0,0,cutoff⟩]', '[]'),
        pair('restricting the initial program preserves physical energy coordinates',
             '''example (s : Snapshot 1) (cutoff : ℝ) :
    (retainSourcesThrough cutoff s).x 0 .energy=@v@ := by rfl
''', 's.x 0 .energy', '100'),
        pair('the first strong and protected MARK prefix contains exactly one actual FIRE', mark+
             ': (c.execution.emissionTimes 0).length=@v@ := by exact c.emission_count\n',
             '1', '2'),
        pair('the first MARK prefix consumes the actual fourth and fifth successor sources', mark+
             ': c.execution.deliveries=[⟨0,p,s.time+@v@⟩,⟨0,p,s.time+20⟩] := by exact c.deliveries\n',
             '16', '12'),
        pair('the first MARK prefix retains the three weak ERROR doses and adds one own MARK', mark+
             ': c.final.x 0 (.z p)=s.x 0 (.z p)+@v@ ∧ c.final.x 0 .b=s.x 0 .b+1/10 := by\n'
             '  exact ⟨c.gain_target,c.recovery_own⟩\n', '9/5', '12/5'),
        pair('the native birth-to-leaf factory derives all preparation and fast FIREs without a reaching trace',
             born_factory, 'K+9', 'K-5'),
        pair('the complete birth-to-leaf run consumes sixteen preparation sources and all K cadence sources', born_leaf+
             ': c.execution.deliveries.length=@v@ := by exact c.delivery_count\n',
             '16+K', 'K'),
        pair('the weak leaf port learns four own ERROR doses across its real cadence', born_leaf+
             ': c.final.x 0 (.z 0)=born.x 0 (.z 0)+@v@ := by exact c.gain_port0\n',
             '12/5', '9/5'),
        pair('the original preparation memory on port1 survives the entire leaf cadence', born_leaf+
             ': c.final.x 0 (.z 1)=born.x 0 (.z 1)+@v@ := by exact c.gain_port1\n',
             '3/5', '9/5'),
        pair('the native leaf recovery includes one preparation and two cadence MARK doses', born_leaf+
             ': c.final.x 0 .b=born.x 0 .b+@v@ := by exact c.recovery\n',
             '3/10', '1/5'),
        pair('the completed native leaf has no RAW and no remaining cadence source tokens', born_leaf+
             ': (∀ j p,c.final.raw j p=none) ∧ c.final.pending=@v@ := by\n'
             '  exact ⟨c.raw_none,c.pending⟩\n', '[]', 'sourceTrain 0 0 160 4 K'),
        pair('the full native leaf reaches and saturates the caller-supplied terminal horizon', born_leaf+
             ': c.final.time=(@v@) ∧ CompleteThrough c.execution (@v@) := by\n'
             '  exact ⟨c.date,c.complete⟩\n', 'terminal', 'terminal+1'),
        pair('the derived fast packet is the actual filtered FIRE ledger excluding the fourteen preparation outputs', born_leaf+
             ': @v@=List.ofFn (fun i : Fin (3+(K-8))=>c.packet.actual i.val) := by\n'
             '  exact c.packet_calendar\n',
             '(c.execution.emissionTimes 0).filter (fun t=>(160:ℝ)≤t)',
             'c.execution.emissionTimes 0'),
        pair('all initial source occurrences are actually delivered across both phases', born_leaf+
             ': c.execution.deliveries=@v@ := by exact c.delivered_sources\n',
             'born.pending', 'sourceTrain 0 0 160 4 K'),
        pair('the native leaf terminal charge is exact physical rest', born_leaf+
             ': c.final.x 0 .q=@v@ := by exact c.charge\n', '1/10', '1/10+1/100000'),
        pair('the relay factory restores the original fabrication rows in its actual execution',
             relay_factory, 'θ', '(permuteParameters θ swapLowPorts)'),
        pair('the relay prepares its own actual port2 with three complete ERROR doses', relay+
             ': r.final.x 0 (.z 2)=born.x 0 (.z 2)+@v@ := by exact r.gain_target\n',
             '9/5', '3/5'),
        pair('the relay learns exactly one protected recovery dose', relay+
             ': r.final.x 0 .b=born.x 0 .b+@v@ := by exact r.recovery\n',
             '1/10', '1/5'),
        pair('the sixteen direct low-port preparation inputs produce twelve relay FIREs', relay+
             ': (r.execution.emissionTimes 0).length=@v@ := by exact r.emission_count\n',
             '12', '14'),
        pair('the port-transported relay arrivals remain actual port2 source occurrences', relay+
             ': r.execution.deliveries=sourceTrain 0 @v@ 0 8 16 := by exact r.deliveries\n',
             '2', '0'),
        pair('restoring the relay ports preserves each unused own birth gain', relay+
             '(p : Port) (hp : p≠2) : r.final.x 0 (.z p)=born.x 0 (.z p)@v@ := by\n'
             '  exact r.gain_other p hp\n', '', '+3/5'),
    ]


def main():
    controls = cases()
    assert len(controls) == 40
    assert len({name for name, _, _ in controls}) == len(controls)
    with tempfile.TemporaryDirectory(prefix='hybrid-finite-preparation-', dir=ROOT) as tmp:
        path = Path(tmp) / 'Check.lean'
        command = lean_check_command(tmp)

        def check(source, expected, name):
            path.write_text(PREFIX + source)
            result = subprocess.run([*command, str(path)], cwd=ROOT, text=True,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=180)
            if (result.returncode == 0) != expected:
                raise SystemExit(f'{name}: unexpected result:\n{result.stdout}')
            if not expected and 'error:' not in result.stdout:
                raise SystemExit(f'{name}: failed without a Lean diagnostic:\n{result.stdout}')

        check('\n'.join(good for _, good, _ in controls), True,
              'all positive direct preparation, source restriction, native leaf and relay contracts')
        print(f'All {len(controls)} positive finite-preparation contracts accepted.', flush=True)
        for name, _, bad in controls:
            check(bad, False, name)
            print(f'{name}: valid conclusion accepted; altered claim rejected.', flush=True)
        print(f'{len(controls)} paired finite-preparation controls passed.', flush=True)


if __name__ == '__main__':
    main()
