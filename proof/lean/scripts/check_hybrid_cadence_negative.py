#!/usr/bin/env python3
"""Guard actual cadence initiation, mixed doses, residual tails and high-gain returns."""
from pathlib import Path
import subprocess
import tempfile

from lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[1]
PREFIX = '''import KernelR.HybridCadencePrelude
import KernelR.HybridCadenceMixedPulse
import KernelR.HybridCadenceMarkOnly
import KernelR.HybridCadenceHighTrain
import KernelR.HybridCadenceRestRoot
open KernelR.Hybrid
'''


def cases():
    prelude = """example {{θ ε s u}} (forward backward : ℝ → ℝ)
    (e : @Execution 3 θ (cadenceRouter forward backward) s u)
    (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (ha : PreparedSection s 0) (hqa : s.x 0 .q = 1/10) (hra : ∀ p, s.raw 0 p = none)
    (hbs : PreparedSection s 1) (hqb : s.x 1 .q = 1/10) (hrb : ∀ p, s.raw 1 p = none)
    (hc : PreparedSection s 2) (hqc : s.x 2 .q = 1/10) (hrc : ∀ p, s.raw 2 p = none)
    (hz : s.x 2 (.z 0) ≤ Real.log (3/10)+1/100000)
    (hA : s.pending.filter (fun d => d.cell = 0) = [])
    (hB : s.pending.filter (fun d => d.cell = 1) = [])
    (hC : (s.pending.filter (fun d => d.cell = 2)).Perm (sourceTrain 2 0 640 4 {count}))
    (hu : u.time = 7899/10) (hpf : PendingFuture s)
    (hfw : ∀ t, 0 ≤ forward t) (hbw : ∀ t, 0 ≤ backward t) : Nonempty (CadencePrelude e) := by
  exact e.cadence_prelude forward backward hb hf hv ha hqa hra hbs hqb hrb hc hqc hrc hz hA hB hC hu hpf hfw hbw
"""
    pre_context = """example {{θ route s u}} {{e : @Execution 3 θ route s u}} (h : CadencePrelude e) :
"""
    pre_error = pre_context + """    h.head.ledger.error 2 0 = {value} := by
  have hd := h.c_error
  linarith
"""
    pre_queue = pre_context + """    (h.entry.pending.filter (fun d => d.cell = 2)).Perm (sourceTrain 2 0 656 4 {count}) := by
  exact h.c_pending
"""
    pre_charge = pre_context + """    h.entry.x 2 .q {relation} {value} := by
  exact h.c_coordinates.charge.2
"""
    pre_raw = pre_context + """    h.entry.raw 2 0 = {value} := by
  exact h.c_raw_active
"""
    pre_quiet = pre_context + """    h.head.emissionTimes 1 = {value} := by
  exact h.downstream.b_idle.emissions
"""
    mixed = """example {{n θ ε route s u}} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (i : Fin n) (p : Port) (hs : s.main i = .slow)
    (hq : {lower} ≤ s.x i .q ∧ s.x i .q ≤ 7/50)
    (hbr : 27999/100000 ≤ s.x i .b ∧ s.x i .b ≤ 28001/100000)
    (ha : ∀ q, s.aux i q = .ready ∧ RestBand (s.x i (.m q)))
    (hz : Real.log (3/10)+9/5-1/100000 ≤ s.x i (.z p) ∧ s.x i (.z p) ≤ Real.log (3/10)+9/5+1/100000)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q) (ht : s.time+19/5 ≤ u.time) :
    Nonempty (CadenceMixedPulse e i p) := by
  exact e.cadence_mixed_pulse hb hf hv i p hs hq hbr ha hz hr ho hno ht
"""
    mix_context = """example {{n θ route s u i p}} {{e : @Execution n θ route s u}} (h : CadenceMixedPulse e i p) :
"""
    mix_error = mix_context + """    e.ledger.error i p = {value} := by
  have hd := h.error_dose
  linarith
"""
    mix_mark = mix_context + """    e.ledger.mark i p = {value} := by
  have hd := h.mark_case.mark_dose
  linarith
"""
    mix_recovery = mix_context + """    u.x i .b = s.x i .b+{value} := by
  have hb := h.recovery_gain
  linarith
"""
    mix_charge = mix_context + """    u.x i .q {relation} {value} := by
  exact h.charge.2
"""
    mark_context = """example {{n θ route s u i p}} {{e : @Execution n θ route s u}} (h : CadenceMarkOnlyPulse e i p) :
"""
    mark_error = mark_context + """    e.ledger.error i p = {value} := by
  have hd := h.error_zero p
  linarith
"""
    mark_charge = mark_context + """    u.x i .q = {value} := by
  have hq := h.charge_rest
  linarith
"""
    high = """example {{n θ ε route s u}} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hi : UpperRegion s) (hv : RawValid s) (i : Fin n) (p : Port)
    (hm : s.main i = .ready) (hq : 1/10-1/100000 ≤ s.x i .q ∧ s.x i .q ≤ 1/2)
    (hz : 16/5 ≤ Real.exp (s.x i (.z p)) ∧ Real.exp (s.x i (.z p)) ≤ 7/2)
    (hbr : {recovery} ≤ s.x i .b ∧ s.x i .b ≤ 11/10)
    (ha : ∀ q, s.aux i q = .ready ∧ RestBand (s.x i (.m q)))
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q) (ht : s.time+19/5 ≤ u.time) :
    Nonempty (CadenceLearnedPulse e i) := by
  exact e.high_gain_pulse_of_valid hb hi hv i p hm hq hz hbr ha hr ho hno ht
"""
    high_context = """example {{n θ route s u i}} {{e : @Execution n θ route s u}} (h : CadenceLearnedPulse e i) :
"""
    high_count = high_context + """    (e.emissionTimes i).length = {value} := by
  rw [h.emissions]
  rfl
"""
    high_return = high_context + """    h.admission_return.afterReturn.time < s.time+{value} := by
  exact h.return_deadline
"""
    early = """example {{n θ route s u i}} {{e : @Execution n θ route s u}} (h : HighGainTrigger e i) :
    s.time+{value} < h.afterFire.time := by
  exact h.early
"""
    root = """example {{z : ℝ}}
    (hl : Real.log (3/10)+9/5-1/100000 ≤ z) (hu : z ≤ Real.log (3/10)+9/5+1/100000) :
    restLatency (Real.exp z) < {upper} := by
  have hb := (restLatency_three_doses_bounds hl hu).2
  linarith
"""
    clock = """example {{n θ route s u i p}} {{e : @Execution n θ route s u}} (h : ShortMarkPulse e i p) :
    h.cycle.phases.markPhase.span.accumulatedRecovery i =
      (h.cycle.trigger.afterMark.x i .b+1/2)*KernelR.Cadence.markDuration ((θ i).lm p) {correction} := by
  exact h.mark_integral
"""
    train = """example {{n θ route s u i count}} {{e : @Execution n θ route s u}} (h : CadenceHighTrain e i count) :
    (e.emissionTimes i).length = count+{extra} := by
  simpa only [Nat.add_zero] using h.emissions
"""
    return [
        ('cadence retains all twenty-five external C inputs', prelude.format(count='25'), prelude.format(count='24')),
        ('four consumed sources contain only three completed ERROR doses', pre_error.format(value='9/5'), pre_error.format(value='12/5')),
        ('the fresh fourth source leaves twenty-one future C tokens', pre_queue.format(count='21'), pre_queue.format(count='22')),
        ('period-four carry cannot reuse the period-eight charge cap', pre_charge.format(relation='≤',value='3/10'), pre_charge.format(relation='≤',value='7/50')),
        ('source652 is fresh rather than erased', pre_raw.format(value='some h.entry.time'), pre_raw.format(value='none')),
        ('B stays silent before the first C firing', pre_quiet.format(value='[]'), pre_quiet.format(value='[640]')),
        ('the mixed case requires its proved SLOW input lower bound', mixed.format(lower='61/500'), mixed.format(lower='3/25')),
        ('the mixed case gives one full ERROR dose', mix_error.format(value='3/5'), mix_error.format(value='0')),
        ('the mixed case also gives one full MARK dose', mix_mark.format(value='1/10'), mix_mark.format(value='0')),
        ('mixed recovery increases by one MARK dose', mix_recovery.format(value='1/10'), mix_recovery.format(value='1/5')),
        ('the mixed raw tail does not reset final charge to rest', mix_charge.format(relation='≤',value='1/2'), mix_charge.format(relation='=',value='1/10')),
        ('the earlier protected MARK case gives no ERROR', mark_error.format(value='0'), mark_error.format(value='3/5')),
        ('the earlier protected return restores exact resting charge', mark_charge.format(value='1/10'), mark_charge.format(value='1/5')),
        ('the high-gain short return needs the final recovery band', high.format(recovery='37999/100000'), high.format(recovery='27999/100000')),
        ('one isolated high-gain input emits once', high_count.format(value='1'), high_count.format(value='2')),
        ('the high-gain return keeps its justified time bound', high_return.format(value='19/5'), high_return.format(value='3')),
        ('high gain does not reuse the old lower firing time', early.format(value='1/10'), early.format(value='3/10')),
        ('the three-dose rest root retains its real enclosure', root.format(upper='33/50'), root.format(upper='13/20')),
        ('the finite MARK ramp is integrated rather than made instantaneous', clock.format(correction='-1/(10*(θ i).lm p)'), clock.format(correction='')),
        ('high-gain trains have no extra emission', train.format(extra='0'), train.format(extra='1')),
    ]


def main():
    controls = cases()
    with tempfile.TemporaryDirectory(prefix='hybrid-cadence-negative-', dir=ROOT) as tmp:
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

        check('\n'.join(good for _, good, _ in controls), True, 'valid physical cadence controls')
        for name, _, bad in controls:
            check(bad, False, name)
            print(f'{name}: physical conclusion accepted; altered claim rejected.', flush=True)


if __name__ == '__main__':
    main()
