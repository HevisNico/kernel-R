#!/usr/bin/env python3
"""Paired full3/20-budget endpoints and actual source arrivals at wider gaps."""
from pathlib import Path
import subprocess
import tempfile

from lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[1]
PREFIX = '''import KernelR.HybridCadenceFirstStrongBudgetNextSource
import KernelR.HybridCadenceSecondStrongBudgetNextSource
import KernelR.HybridCadenceMarkOnlyBudgetNextSource
import KernelR.HybridLocalCadenceHighBudgetTrain
open KernelR.Hybrid
noncomputable section
'''


def pair(label, template, good, bad):
    assert '@v@' in template
    assert good != bad
    return label, template.replace('@v@', good), template.replace('@v@', bad)


def strong_factory(kind, gap, conclusion, proof):
    first = kind == 'first'
    name = 'CadenceFirstStrongJitterNextSource' if first else 'CadenceSecondStrongBudgetNextSource'
    lo, hi = ('17999', '18001') if first else ('27999', '28001')
    return f'''example {{θ ε}} (hb : PhysicalBox θ ε) (s : Snapshot 1) (p : Port)
    (later : List (Delivery 1)) (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (hs : CadenceReadyCoordinates s 0 (3/10)) (hq : s.x 0 .q=1/10)
    (hz : Real.log (3/10)+9/5-1/100000≤s.x 0 (.z p) ∧
      s.x 0 (.z p)≤Real.log (3/10)+9/5+1/100000)
    (hB : {lo}/100000≤s.x 0 .b ∧ s.x 0 .b≤{hi}/100000)
    (hr : s.raw 0 p=some s.time) (ho : ∀ q,q≠p→s.raw 0 q=none)
    (hqueue : s.pending=⟨0,p,s.time+{gap}⟩::later)
    (hLater : ∀ d∈later,s.time+{gap}<d.due) :
    ∃ r : {name} θ s p (s.time+{gap}) later,{conclusion} := by
  obtain ⟨r⟩ := cadence_{kind}_strong_full_budget_next_source_exists hb s p (s.time+{gap}) later
    hf hv hs hq hz hB hr ho hqueue (by constructor <;> linarith) hLater
  exact ⟨r,{proof}⟩
'''


def cases():
    first = '''example {θ s p H later} (r : CadenceFirstStrongJitterNextSource θ s p H later) '''
    second = '''example {θ s p H later} (r : CadenceSecondStrongBudgetNextSource θ s p H later) '''
    mark_factory = '''example {θ ε} (hb : PhysicalBox θ ε) (s : Snapshot 1) (p : Port)
    (later : List (Delivery 1)) (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (hm : s.main 0=.slow) (hq : 37/250≤s.x 0 .q ∧ s.x 0 .q≤1/4)
    (hB : 17999/100000≤s.x 0 .b ∧ s.x 0 .b≤18001/100000)
    (ha : ∀ q,s.aux 0 q=.ready ∧ RestBand (s.x 0 (.m q)))
    (hr : s.raw 0 p=some s.time) (ho : ∀ q,q≠p→s.raw 0 q=none)
    (hqueue : s.pending=⟨0,p,s.time+37/10⟩::later)
    (hLater : ∀ d∈later,s.time+37/10<d.due) :
    ∃ r : CadenceMarkOnlyJitterNextSource θ s p (s.time+37/10) later,
      r.final.x 0 .q=@v@ ∧ r.final.raw 0 p=some (s.time+37/10) := by
  obtain ⟨r⟩ := cadence_mark_only_full_budget_next_source_exists hb s p (s.time+37/10) later
    hf hv hm hq hB ha hr ho hqueue (by linarith) hLater
  exact ⟨r,r.charge,r.raw_active⟩
'''
    high_factory = '''example {θ ε} (hb : PhysicalBox θ ε) (s : Snapshot 1) (p : Port)
    (later : List (Delivery 1)) (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (hs : CadenceReadyCoordinates s 0 (8/25)) (hq : 1/10≤s.x 0 .q)
    (hg : 16/5≤Real.exp (s.x 0 (.z p)) ∧ Real.exp (s.x 0 (.z p))≤7/2)
    (hB : 37999/100000≤s.x 0 .b ∧ s.x 0 .b≤38001/100000)
    (hr : s.raw 0 p=some s.time) (ho : ∀ q,q≠p→s.raw 0 q=none)
    (hqueue : s.pending=⟨0,p,s.time+37/10⟩::later)
    (hLater : ∀ d∈later,s.time+37/10<d.due) :
    ∃ r : CadenceHighJitterNextSource θ s p (s.time+37/10) later,
      r.final.time=s.time+37/10 ∧ r.final.x 0 .q=@v@ := by
  obtain ⟨r⟩ := cadence_high_full_budget_next_source_exists hb s p (s.time+37/10) later
    hf hv hs hq hg hB hr ho hqueue (by linarith) hLater
  exact ⟨r,r.date,r.charge⟩
'''
    return [
        pair('first full-budget factory reaches a real source at4.4 with the retained MARK band',
             strong_factory('first', '22/5', '@v@≤r.final.x 0 .q', 'r.charge.1'), '37/250', '1/5'),
        pair('second full-budget factory at4.3 uses its genuinely wider lower charge',
             strong_factory('second', '43/10', '@v@≤r.final.x 0 .q', 'r.charge.1'), '59/500', '61/500'),
        pair('second full-budget factory at3.7 uses its genuinely wider upper charge',
             strong_factory('second', '37/10', 'r.final.x 0 .q≤@v@', 'r.charge.2'), '71/500', '7/50'),
        pair('protected MARK constructs the next source at the new minimum gap3.7',
             mark_factory, '1/10', '1/4'),
        pair('high response constructs a real next source already at gap3.7', high_factory, '1/10', '1/4'),
        pair('full-budget first strong retains its actual emitted occurrence', first +
             ': r.execution.ledger.emissions=@v@ := by exact r.emissions\n', '[(0,r.fire.final.time)]', '[]'),
        pair('full-budget second strong retains its actual variable receipt clock', second +
             ': r.final.time=@v@ := by exact r.date\n', 'H', 's.time+4'),
        pair('full-budget second strong consumes exactly the declared next token', second +
             ': r.execution.deliveries=@v@ := by exact r.deliveries\n', '[⟨0,p,H⟩]', '[]'),
        pair('full-budget second strong retains every later occurrence', second +
             ': r.final.pending=@v@ := by exact r.pending\n', 'later', '[]'),
        pair('full-budget second strong retains the actual protected energy path', second +
             ': r.final.x 0 .energy=@v@ := by exact r.energy\n', 'r.span.final.x 0 .energy', '100'),
        pair('full-budget second strong retains own acquired recovery', second +
             ': r.final.x 0 .b=s.x 0 .b@v@ := by exact r.recovery 0\n', '', '+1/10'),
        pair('full-budget second strong preserves saturation at its real receipt clock', second +
             ': CompleteThrough r.execution @v@ := by exact r.complete\n', 'H', 's.time+4'),
        pair('actual high root returns before3.68 without an assumed future execution',
             '''example {B S latency R : ℝ} (hB : 37999/100000≤B) (hlat : latency<13/50)
    (hclock : R=S+latency+1+Real.log (5/2:ℝ)/B) : R<S+@v@ := by
  exact full_budget_high_reopen_bound hB hlat hclock
''', '92/25', '18/5'),
        pair('actual protected MARK clock returns before3.35',
             '''example {B S M q R : ℝ} (hB : 27999/100000≤B) (hM : M<S+1/20)
    (hq : 0<q ∧ q≤1/4) (hclock : R=M+Real.log (q/(1/10:ℝ))/B) : R<S+@v@ := by
  exact full_budget_mark_reopen_bound hB hM hq hclock
''', '67/20', '3'),
        pair('the old actual protected-MARK witness supports the stronger true return',
             '''example {θ route s p} (m : CadenceMarkOnlyResponse θ route s p)
    (hbown : 17999/100000≤s.x 0 .b) : m.returnState.time<s.time+@v@ := by
  exact m.return_before_full_budget_gap hbown
''', '67/20', '3'),
    ]


def main():
    controls = cases()
    with tempfile.TemporaryDirectory(prefix='hybrid-cadence-full-budget-', dir=ROOT) as tmp:
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

        check('\n'.join(good for _, good, _ in controls), True, 'valid full-budget contracts')
        print(f'All {len(controls)} positive full-budget contracts accepted.', flush=True)
        for name, _, bad in controls:
            check(bad, False, name)
            print(f'{name}: valid conclusion accepted; altered claim rejected.', flush=True)
        print(f'{len(controls)} paired full-budget controls passed.', flush=True)


if __name__ == '__main__':
    main()
