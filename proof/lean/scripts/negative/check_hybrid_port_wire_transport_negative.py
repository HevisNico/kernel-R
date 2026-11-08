#!/usr/bin/env python3
"""Paired whole-execution port transport and indexed native-delay contracts."""
from pathlib import Path
import subprocess
import tempfile
from scripts.lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[2]
PREFIX = '''import KernelR.HybridPortPermutation
import KernelR.HybridIndexedWireDelay
open KernelR.Hybrid
noncomputable section
'''


def pair(label, template, good, bad):
    assert '@v@' in template and good != bad
    return label, template.replace('@v@', good), template.replace('@v@', bad)


def cases():
    snap = '''example {n} (s : Snapshot n) (σ : Equiv.Perm Port) (i : Fin n) '''
    execution = '''example {n θ s u} (e : @Execution n θ (fun _ _ => []) s u)
    (σ : Equiv.Perm Port) '''
    packet = '''example {m L J} (packet : KernelR.Chain.Packet m L J) (hJ : J ≤ 3/20)
    (d σ : ℝ) (hσ : 0 ≤ σ) (error : ℕ → ℝ)
    (he : ∀ i,-σ ≤ error i ∧ error i ≤ σ) '''
    physical = '''example (dates : List ℝ) (d σ : ℝ) (error : ℕ → ℝ)
    (hc : 3/10+σ ≤ d ∧ d ≤ 2/5-σ)
    (he : ∀ i,-σ ≤ error i ∧ error i ≤ σ) '''
    tokens = '''example {n θ route s u m L J} (e : @Execution n θ route s u)
    (source : Fin n) (port : Port) (packet : KernelR.Chain.Packet m L J)
    (hcalendar : e.emissionTimes source=List.ofFn (fun i : Fin (m+L) => packet.actual i.val))
    (hJ : J ≤ 3/20) (d σ : ℝ) (hσ : 0 ≤ σ) (error : ℕ → ℝ)
    (he : ∀ i,-σ ≤ error i ∧ error i ≤ σ) '''
    factory = '''example {m L J} (packet : KernelR.Chain.Packet m L J) (hJ : J ≤ 3/20)
    (d σ : ℝ) (error : ℕ → ℝ) (hc : 3/10+σ ≤ d ∧ d ≤ 2/5-σ)
    (he : ∀ i,-σ ≤ error i ∧ error i ≤ σ) :
    ∃ delay : ℝ → ℝ,
      delay=@v@ ∧
      (∀ time,3/10 ≤ delay time ∧ delay time ≤ 2/5) ∧
      (∀ i : Fin (m+L),delay (packet.actual i.val)=d+error i.val) := by
  let dates := List.ofFn (fun i : Fin (m+L) => packet.actual i.val)
  refine ⟨indexedWireDelay dates d error,rfl,?_,?_⟩
  · exact indexedWireDelay_physical_bounds dates d σ error hc he
  · intro i
    exact indexedWireDelay_packet_at packet hJ d error i
'''
    return [
        pair('port permutation retains actual energy rather than resetting it', snap +
             ': (s.permutePorts σ).x i .energy=@v@ := by exact s.permutePorts_energy σ i\n',
             's.x i .energy', '100'),
        pair('new sensor and gain coordinates both read the corresponding old port', snap +
             '''(p : Port) : ((s.permutePorts σ).x i (.m p),(s.permutePorts σ).x i (.z p))=
    (s.x i (.m (@v@)),s.x i (.z (@v@))) := by
  exact Prod.ext (s.permutePorts_m σ i p) (s.permutePorts_z σ i p)
''', 'σ p', 'σ.symm p'),
        pair('heterogeneous fabrication cap rate and input follow the same old port',
             '''example {n} (θ : Fin n → Parameters) (σ : Equiv.Perm Port) (i : Fin n) (p : Port) :
    (((permuteParameters θ σ) i).cap p,((permuteParameters θ σ) i).lm p,
      ((permuteParameters θ σ) i).inputGain p)=
    ((θ i).cap (@v@),(θ i).lm (@v@),(θ i).inputGain (@v@)) := by rfl
''', 'σ p', 'σ.symm p'),
        pair('real delivery tokens use the inverse port permutation',
             '''example {n} (token : Delivery n) (σ : Equiv.Perm Port) :
    (token.permutePorts σ).port=@v@ := by rfl
''', 'σ.symm token.port', 'σ token.port'),
        pair('RAW origins are relabeled rather than restarted at the current clock', snap +
             '(p : Port) : (s.permutePorts σ).raw i p=@v@ := by exact s.permutePorts_raw σ i p\n',
             's.raw i (σ p)', 'some s.time'),
        pair('the complete physical vector field obeys the same coordinate permutation',
             '''example {n} (θ : Fin n → Parameters) (s : Snapshot n) (x : Values n)
    (σ : Equiv.Perm Port) (t : ℝ) (i : Fin n) (c : Coord) :
    field (permuteParameters θ σ) (s.permutePorts σ) (x.permutePorts σ) t i c=
      field θ s x t i @v@ := by exact field_permutePorts θ s x σ t i c
''', '(c.permutePorts σ)', 'c'),
        pair('every time on a relabeled FLOW keeps its actual physical energy path',
             '''example {n θ s u} (flow : @Flow n θ s u) (σ : Equiv.Perm Port) (t : ℝ) (i : Fin n) :
    (flow.permutePorts σ).path t i .energy=@v@ := by exact flow.permutePorts_energy σ t i
''', 'flow.path t i .energy', '100'),
        pair('whole physical execution retains every actual FIRE date unchanged', execution +
             '''(i : Fin n) : (e.permutePorts σ).emissionTimes i=@v@ := by exact e.permutePorts_emissionTimes σ i
''', 'e.emissionTimes i', '(e.emissionTimes i).map (fun time => time+1)'),
        pair('whole physical delivery history relabels every inverse port exactly', execution +
             ''': (e.permutePorts σ).deliveries=@v@ := by exact e.permutePorts_deliveries σ
''', 'e.deliveries.map (fun token => token.permutePorts σ)', 'e.deliveries'),
        pair('actual ERROR and MARK doses move with their own physical port', execution +
             '''(i : Fin n) (p : Port) :
    ((e.permutePorts σ).ledger.error i p,(e.permutePorts σ).ledger.mark i p)=
    (e.ledger.error i (@v@),e.ledger.mark i (@v@)) := by
  exact Prod.ext (e.permutePorts_error σ i p) (e.permutePorts_mark σ i p)
''', 'σ p', 'p'),
        pair('birth permits swapping low ports zero and two but not the high nominal port',
             '''example {n s} (birth : @BirthState n s) : BirthState (s.permutePorts @v@) := by
  exact birth.swapLowPorts
''', 'swapLowPorts', '(Equiv.swap 0 1)'),
        pair('terminal saturation survives port transport at the actual same horizon', execution +
             '''(T : ℝ) (hc : CompleteThrough e T) : CompleteThrough (e.permutePorts σ) (@v@) := by
  exact hc.permutePorts σ
''', 'T', 'T+1'),
        pair('distinct real event dates recover the exact supplied error index',
             '''example (dates : List ℝ) (d : ℝ) (error : ℕ → ℝ) (hn : dates.Nodup)
    (i : ℕ) (hi : i<dates.length) : indexedWireDelay dates d error dates[i]=d+error (@v@) := by
  exact indexedWireDelay_at dates d error hn i hi
''', 'i', 'i+1'),
        pair('absent real times use the bounded fallback error rather than dropping jitter',
             '''example (dates : List ℝ) (d : ℝ) (error : ℕ → ℝ) (time : ℝ) (ht : time ∉ dates) :
    indexedWireDelay dates d error time=@v@ := by exact indexedWireDelay_absent dates d error time ht
''', 'd+error dates.length', 'd'),
        pair('native delay remains physically bounded at every real time including future padding', physical +
             '''(time : ℝ) : @v@ := by exact indexedWireDelay_physical_bounds dates d σ error hc he time
''', '3/10 ≤ indexedWireDelay dates d error time ∧ indexedWireDelay dates d error time ≤ 2/5',
             '31/100 ≤ indexedWireDelay dates d error time ∧ indexedWireDelay dates d error time ≤ 39/100'),
        pair('duplicate dates recover the first occurrence and cannot pretend to distinguish two errors',
             '''example (time d : ℝ) (error : ℕ → ℝ) :
    indexedWireDelay [time,time] d error time=d+error @v@ := by
  classical
  simp [indexedWireDelay]
''', '0', '1'),
        pair('native router delay realizes packet actual dates without erasing phase', packet +
             '''(i : Fin (m+L)) : (packet.wire d σ hσ error he).@v@ i.val=
    packet.actual i.val+indexedWireDelay
      (List.ofFn (fun k : Fin (m+L) => packet.actual k.val)) d error (packet.actual i.val) := by
  exact indexedWireDelay_wire_actual packet hJ d σ hσ error he i
''', 'actual', 'ideal'),
        pair('head tokens from the real emission ledger match the complete wired packet', tokens +
             ''': e.headInputQueue (indexedHeadContact source port (e.indexedWireDelay source d error))=
    List.ofFn (fun i : Fin (m+L) => (⟨0,port,@v@⟩ : Delivery 1)) := by
  exact e.indexedWire_head_tokens source port packet hcalendar hJ d σ hσ error he
''', '(packet.wire d σ hσ error he).actual i.val', 'packet.actual i.val'),
        pair('native indexed contacts are strictly causal even at unlisted real times', physical +
             '''{n} (source : Fin n) (port : Port) :
    StrictHeadRoutes (indexedHeadContact source port @v@) := by
  exact indexedHeadContact_strict source port (indexedWireDelay dates d error)
    (fun time => by linarith [(indexedWireDelay_physical_bounds dates d σ error hc he time).1])
''', '(indexedWireDelay dates d error)', '(fun _ => -(1 : ℝ))'),
        pair('bounded per-event errors construct one native function without replacing it by a fixed delay',
             factory, '(indexedWireDelay (List.ofFn (fun i : Fin (m+L) => packet.actual i.val)) d error)', '(fun _ => d)'),
    ]


def main():
    controls = cases()
    assert len(controls) == 20
    with tempfile.TemporaryDirectory(prefix='hybrid-port-wire-transport-', dir=ROOT) as tmp:
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

        check('\n'.join(good for _, good, _ in controls), True, 'all positive physical port and indexed-wire contracts')
        print('All20 positive physical port and indexed-wire contracts accepted.', flush=True)
        for name, _, bad in controls:
            check(bad, False, name)
            print(f'{name}: physical conclusion accepted; altered claim rejected.', flush=True)
        print(f'{len(controls)} paired physical port and indexed-wire controls passed.', flush=True)


if __name__ == '__main__':
    main()
