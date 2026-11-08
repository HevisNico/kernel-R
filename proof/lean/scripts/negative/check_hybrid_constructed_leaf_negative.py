#!/usr/bin/env python3
"""Paired exact autonomous projection and constructed C leaf contracts."""
from pathlib import Path
import subprocess
import tempfile

from scripts.lean_check import lean_check_command

ROOT=Path(__file__).resolve().parents[2]
PREFIX='''import KernelR.HybridConstructedCadenceLeafPacket
open KernelR.Hybrid
noncomputable section
'''


def pair(label,template,good,bad):
    assert '@v@' in template
    assert good!=bad
    return label,template.replace('@v@',good),template.replace('@v@',bad)


def cases():
    projected='''example {n θ route s u} {e : @Execution n θ route s u} {i : Fin n}
    (p : AutonomousCellProjection e i) '''
    full='''example {θ born freshB freshC newbornB newbornC forward backward delay cascadeForward cascadeBackward}
    {c : ConstructedCadenceFirstMarkReturn θ born freshB freshC newbornB newbornC forward backward delay
      cascadeForward cascadeBackward} (full : ConstructedCadenceLocalC c) '''
    wire=full+'''(wireDelay : ℝ → ℝ)
    (hd : ∀ t, (3/10:ℝ)≤wireDelay t ∧ wireDelay t≤2/5) '''
    factory='''example {θ born freshB freshC newbornB newbornC forward backward delay cascadeForward cascadeBackward ε}
    (c : ConstructedCadenceFirstMarkReturn θ born freshB freshC newbornB newbornC forward backward delay
      cascadeForward cascadeBackward)
    (hb : @PhysicalBox 3 (extendParameters (extendParameters θ freshB) freshC) ε) :
    ∃ full : ConstructedCadenceLocalC c,
      full.final.time=@v@ ∧ full.final.pending=[] ∧ (full.execution.emissionTimes 0).length=20 ∧
      (∀ q, full.final.raw 0 q=none) := by
  obtain ⟨full⟩ := c.local_c_full_exists hb
  exact ⟨full,full.date,full.pending,full.emission_count,full.raw_none 0⟩
'''
    return [
        pair('autonomous view retains the actual selected-cell energy',
             '''example {n} (s : Snapshot n) (i : Fin n) :
    (s.autonomousView i).x 0 .energy=@v@ := by rfl
''','s.x i .energy','100'),
        pair('autonomous view filters the actual queue instead of deleting external sources',
             '''example {n} (s : Snapshot n) (i : Fin n) :
    (s.autonomousView i).pending=@v@ := by rfl
''','cellQueue i s.pending','[]'),
        pair('autonomous execution retains exactly the selected actual FIRE times',projected+
             ': p.execution.emissionTimes 0=@v@ := by exact p.emission_times\n','e.emissionTimes i','[]'),
        pair('autonomous execution retains selected actual delivery occurrences',projected+
             ': p.execution.deliveries=@v@ := by exact p.deliveries\n','cellQueue i e.deliveries','[]'),
        pair('autonomous execution preserves every selected real MARK exposure',projected+
             '(q : Port) : p.execution.ledger.mark 0 q=@v@ := by exact p.mark q\n','e.ledger.mark i q','0'),
        pair('autonomous execution preserves every selected real ERROR exposure',projected+
             '(q : Port) : p.execution.ledger.error 0 q=@v@ := by exact p.error q\n','e.ledger.error i q','0'),
        pair('full C factory extracts the actual global prefix without a new reaching premise',
             factory,'7899/10','660'),
        pair('full C starts with all twenty-five actual external sources still queued',full+
             ': (c.wave.cadence.teaching.final.autonomousView 2).pending=sourceTrain 0 0 640 4 @v@ := by exact ConstructedCadenceLocalC.source_pending (c:=c)\n','25','19'),
        pair('full C trace contains its genuine twenty cadence outputs',full+
             ': (full.execution.emissionTimes 0).length=@v@ := by exact full.emission_count\n','20','19'),
        pair('full C trace consumes exactly the original twenty-five source occurrences',full+
             ': full.execution.deliveries=sourceTrain 0 0 640 4 @v@ := by exact full.deliveries\n','25','24'),
        pair('full C terminal queue is genuinely empty after all real arrivals',full+
             ': full.final.pending=@v@ := by exact full.pending\n','[]','sourceTrain 0 0 736 4 1'),
        pair('full C gain remains tied to its own independent newborn',full+
             ': full.final.x 0 (.z 0)=@v@+12/5 := by exact full.c_gain_own\n',
             'newbornC.x (.z 0)','newbornB.x (.z 0)'),
        pair('full C recovery retains its own newborn plus three real MARK doses',full+
             ': full.final.x 0 .b=@v@+3/10 := by exact full.c_recovery_own\n',
             'newbornC.x .b','newbornB.x .b'),
        pair('full autonomous completion is certified at its true789point9 horizon',full+
             ': CompleteThrough full.execution (@v@) := by exact full.complete\n','7899/10','660'),
        pair('derived leaf has exactly three prefix FIREs and seventeen regular FIREs with J0',full+
             ': KernelR.Chain.Packet 3 @v@ 0 := full.leafPacket\n','17','18'),
        pair('all leaf packet dates are conclusions about the actual C emission ledger',full+
             ': full.execution.emissionTimes 0=List.ofFn (fun i : Fin @v@ => full.leafPacket.actual i.val) := by exact full.leaf_packet_calendar\n','20','19'),
        pair('received leaf exposes the true point05 jitter envelope',wire+
             ': KernelR.Chain.Packet 3 17 (@v@) := full.receivedLeafPacket wireDelay hd\n','1/20','0'),
        pair('received leaf samples each delay at its actual issuing FIRE',wire+
             '''(i : Fin 20) : (full.receivedLeafPacket wireDelay hd).actual i.val=
    full.leafPacket.actual i.val+wireDelay (@v@) := by exact full.received_leaf_actual wireDelay hd i.val
''','full.leafPacket.actual i.val','640+4*(i.val:ℝ)'),
        pair('real leaf tokens match exactly twenty B-port2 receiving dates',wire+
             ''': full.leafTokens wireDelay=List.ofFn (fun i : Fin @v@ =>
    (⟨1,2,(full.receivedLeafPacket wireDelay hd).actual i.val⟩ : Delivery 3)) := by
  exact full.leaf_tokens_received_calendar wireDelay hd
''','20','21'),
        pair('every leaf token originates in the actual selected emission ledger',full+
             '''(wireDelay : ℝ → ℝ) (d : Delivery 3) (h : d∈full.leafTokens wireDelay) :
    ∃ time, time∈@v@ ∧ d=(ConstructedCadenceLocalC.leafContact wireDelay).token time := by
  exact full.leaf_token_provenance wireDelay d h
''','full.execution.emissionTimes 0','[]'),
    ]


def main():
    controls=cases()
    with tempfile.TemporaryDirectory(prefix='hybrid-constructed-leaf-',dir=ROOT) as tmp:
        path=Path(tmp)/'Check.lean'
        command=lean_check_command(tmp)

        def check(source,expected,name):
            path.write_text(PREFIX+source)
            result=subprocess.run([*command,str(path)],cwd=ROOT,text=True,
                                  stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=180)
            if (result.returncode==0)!=expected:
                raise SystemExit(f'{name}: unexpected result:\n{result.stdout}')
            if not expected and 'error:' not in result.stdout:
                raise SystemExit(f'{name}: failed without a Lean diagnostic:\n{result.stdout}')

        check('\n'.join(good for _,good,_ in controls),True,'valid constructed-leaf controls')
        print(f'All{len(controls)} positive constructed-leaf contracts accepted.',flush=True)
        for name,_,bad in controls:
            check(bad,False,name)
            print(f'{name}: physical conclusion accepted; altered claim rejected.',flush=True)
        print(f'{len(controls)} paired constructed-leaf controls passed.',flush=True)


if __name__=='__main__':
    main()
