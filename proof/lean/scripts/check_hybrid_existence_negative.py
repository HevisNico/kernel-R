#!/usr/bin/env python3
"""Guard source-driven existence without a supplied reaching execution."""
from pathlib import Path
import subprocess
import tempfile

from lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[1]
PREFIX = '''import KernelR.HybridFirstInputMark
open KernelR.Hybrid
'''


def cases():
    contract = """example {{θ ε route born}}
    (hs : @BirthState 1 born) (hb : PhysicalBox θ ε)
    (ha : ∀ p, born.aux 0 p = .ready)
    (hq : born.pending = sourceTrain 0 0 0 8 {count} ++ sourceTrain 0 0 160 8 16) :
    ∃ f : FirstInputMark θ (birthProtocolFirstAfter born) 0 0,
      ∃ e : Execution θ route born f.final,
        CompleteThrough e f.final.time ∧
        1/100 < f.final.time ∧ f.final.time < 1/40 ∧
        e.deliveries = [⟨0,0,0⟩] ∧ e.ledger.emissions = [] ∧
        f.final.pending.length = 31 ∧
        (∀ p, f.final.x 0 (.z p) = born.x 0 (.z p)) ∧
        f.final.x 0 .b = born.x 0 .b ∧ PhysicalInvariant θ f.final ∧ RawValid f.final := by
  exact birth_protocol_first_mark_exists hs hb ha hq
"""
    context = """example {{n θ s i p}} (f : @FirstInputMark n θ s i p) """
    latency = context + """: 1/100 < f.latency ∧ f.latency < {upper} := by
  exact ⟨f.early,f.deadline⟩
"""
    charge = context + """: f.final.x i (.m p) = {value} := by
  exact f.sensor_threshold
"""
    gain = context + """(q : Port) : f.final.x i (.z q) = s.x i (.z q) {extra} := by
  rfl
"""
    recovery = context + """: f.final.x i .b = s.x i .b {extra} := by
  rfl
"""
    delivery = context + """(route : Router n) : (f.execution route).deliveries = {value} := by
  rfl
"""
    output = context + """(route : Router n) : ((f.execution route).signal i).count = {value} := by
  rfl
"""
    raw = context + """: f.final.raw i p = {value} := by
  exact f.raw_active
"""
    pending = """example {{θ born}} (f : FirstInputMark θ (birthProtocolFirstAfter born) 0 0) :
    f.final.pending.length = {value} := by
  simp [FirstInputMark.final,setAux,readyInputEnd,birthProtocolFirstAfter,sourceTrain]
"""
    quiet = """example {{n}} (s : Snapshot n) (i : Fin n) :
    (quietAt s s.time).x i .energy = {value} := by
  simp [quietAt,quietValues,relax_initial]
"""
    nojump = """example {{n route s}} (hg : @BeforeGuards n s s.x)
    (hr : ∀ i p o, s.raw i p = some o → s.time < o+1)
    (hp : ∀ d ∈ s.pending, s.time {comparison} d.due) (u : Snapshot n) : IsEmpty (Jump route s u) := by
  exact hg.no_jump hr hp u
"""
    energy = """example (initial coeff start t : ℝ) :
    HasDerivAt (readyInputEnergy initial coeff start)
      (10*(100-readyInputEnergy initial coeff start t) - {forcing}) t := by
  exact readyInputEnergy_derivative initial coeff start t
"""
    return [
        ('the source-driven factory needs the actual full birth queue', contract.format(count='16'), contract.format(count='15')),
        ('the first constructed sensor cutoff retains its physical bracket', latency.format(upper='1/40'), latency.format(upper='1/100')),
        ('the first actual MARK occurs at charge one', charge.format(value='1'), charge.format(value='4/5')),
        ('the source-driven prefix does not invent a gain dose', gain.format(extra=''), gain.format(extra='+3/5')),
        ('the first READY-main MARK does not invent recovery', recovery.format(extra=''), recovery.format(extra='+1/10')),
        ('the constructed flow-to-MARK adds no delivery', delivery.format(value='[]'), delivery.format(value='[⟨i,p,s.time⟩]')),
        ('the constructed first-input prefix has no output', output.format(value='0'), output.format(value='1')),
        ('the raw origin survives the first MARK', raw.format(value='some s.time'), raw.format(value='none')),
        ('all thirty-one future sources remain queued', pending.format(value='31'), pending.format(value='30')),
        ('quiescent construction retains the initial reserve', quiet.format(value='s.x i .energy'), quiet.format(value='100')),
        ('terminal saturation requires strict future delivery deadlines', nojump.format(comparison='<'), nojump.format(comparison='≤')),
        ('the constructed energy pays for the actual input work', energy.format(forcing='coeff*a*Real.exp (-a*(t-start))'), energy.format(forcing='0')),
    ]


def main():
    controls = cases()
    with tempfile.TemporaryDirectory(prefix='hybrid-existence-negative-', dir=ROOT) as tmp:
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

        check('\n'.join(good for _,good,_ in controls), True, 'valid constructive existence controls')
        for name,_,bad in controls:
            check(bad, False, name)
            print(f'{name}: physical conclusion accepted; altered claim rejected.', flush=True)


if __name__ == '__main__':
    main()
