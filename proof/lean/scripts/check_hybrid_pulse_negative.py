#!/usr/bin/env python3
"""Check physical pulse conclusions and reject altered chronology or doses."""
from pathlib import Path
import subprocess
import tempfile

from lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[1]
PREFIX = '''import KernelR.HybridFiring
import KernelR.HybridSingleOutput
import KernelR.HybridInputBalance
open KernelR.Hybrid
'''


def cases():
    response = '''example {{t : ℝ}} (ht : 0 ≤ t) : response t ≤ {bound} := by
  have h := response_global_upper ht
  linarith
'''
    gain = '''example {{n θ ε route s u i p}} {{e : @Execution n θ route s u}}
    (cycle : SensorCycle e i p) (hb : PhysicalBox θ ε) :
    e.AllFlows (fun {{v w}} f => ∀ t ∈ Set.Icc v.time w.time, t ≤ s.time + 1 →
      f.path t i (.z p) ≤ s.x i (.z p) + {bound}) := by
  exact cycle.gain_during_raw hb
'''
    frozen = '''example {{n θ route s u i p}} {{e : @Execution n θ route s u}}
    (cycle : SensorCycle e i p) :
    e.AllFlows (fun {{v w}} f => ∀ t ∈ Set.Icc v.time w.time, t ≤ s.time + {deadline} →
      f.path t i (.z p) = s.x i (.z p)) := by
  exact cycle.gain_before_error
'''
    firing = '''example {{n θ route s u i}} {{e : @Execution n θ route s u}}
    (tr : MainTrigger e i) : {claim} := by
  have h := tr.{field}
  linarith
'''
    ready = '''example {{n θ route s u}} (e : @Execution n θ route s u)
    (i : Fin n) (h : {states}) : e.emissionTimes i = [] := by
  exact e.no_emissions_of_ready_states i h
'''
    total_dose = '''example {{n θ ε route born s u i p}} {{e : @Execution n θ route s u}}
    (cycle : SensorCycle e i p) (past : Execution θ route born s)
    (hborn : BirthState born) (hb : PhysicalBox θ ε)
    (hm : e.AllStates (fun v => v.main i = .ready))
    (hz : s.x i (.z p) ≤ Real.log (3/10) + 6/5 + 1/100000)
    (hr : s.raw i p = some s.time) (hn : NoArrivalAt e i p) :
    e.ledger.error i p = {dose} := by
  have h := (cycle.total_error_dose_when_ready past hborn hb hm hz hr hn).1
  linarith
'''
    balance = '''example {{n θ route s u}} (e : @Execution n θ route s u) :
    (u.pending : Multiset (Delivery n)) + (e.deliveries : Multiset (Delivery n)) =
      (s.pending : Multiset (Delivery n)) {routed} := by
  exact e.token_balance
'''
    sources = '''example {{n θ route s u}} (e : @Execution n θ route s u)
    (T : ℝ) (hc : {complete}) (hs : ∀ d ∈ s.pending, d.due ≤ T)
    (hr : ∀ i t, route i t = []) : e.deliveries.Perm s.pending := by
  exact e.deliveries_perm_sources T hc hs hr
'''
    single = '''example {{n θ route born s u i}} {{e : @Execution n θ route s u}}
    (tr : MainTrigger e i) (past : Execution θ route born s) (hborn : BirthState born)
    (p : Port) (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hn : ∀ q, NoArrivalAt e i q) : e.emissionTimes i = {events} := by
  exact tr.only_emission past hborn p hr ho hn
'''
    fast = '''example {{n θ route s u}} (e : @Execution n θ route s u)
    (i : Fin n) (origin : ℝ) (hs : s.main i = .fast) (hq : s.x i .q = 1) (ht : {date})
    (hr : e.AllStates (fun v => origin+1 < v.time → ∀ p, v.raw i p = none))
    (hn : ∀ p, NoArrivalAt e i p) : e.emissionTimes i = [] := by
  exact e.fast_tail_no_emissions i origin hs hq ht hr hn
'''
    quiet = '''example {{n θ route s u}} (e : @Execution n θ route s u)
    (i : Fin n) (hs : s.main i = .ready) (hx : s.x i .q ≤ 1/10)
    (hr : ∀ p, s.raw i p = none) (hn : {arrivals}) :
    e.AllStates (fun v => v.main i = .ready) := by
  exact e.ready_without_input i hs hx hr hn
'''
    return [
        ('global response bound', response.format(bound='3/4'), response.format(bound='1/2')),
        ('late raw-window gain increase', gain.format(bound='11/125'), gain.format(bound='0')),
        ('gain freezing ends before raw cutoff', frozen.format(deadline='99/100'), frozen.format(deadline='1')),
        ('learned first-firing lower date',
         firing.format(claim='s.time + 3/10 < tr.afterFire.time', field='early'),
         firing.format(claim='s.time + 2/5 < tr.afterFire.time', field='early')),
        ('learned first-firing upper date',
         firing.format(claim='tr.afterFire.time < s.time + 9/10', field='deadline'),
         firing.format(claim='tr.afterFire.time < s.time + 4/5', field='deadline')),
        ('terminal zero-time fires remain visible',
         ready.format(states='e.AllStates (fun v => v.main i = .ready)'),
         ready.format(states='e.MainFlows i .ready')),
        ('total silent ERROR dose', total_dose.format(dose='3/5'), total_dose.format(dose='1/2')),
        ('routed token multiplicities',
         balance.format(routed='+ (e.ledger.emissions.flatMap (fun ev => route ev.1 ev.2) : Multiset (Delivery n))'),
         balance.format(routed='')),
        ('source exhaustion needs terminal saturation',
         sources.format(complete='CompleteThrough e T'), sources.format(complete='True')),
        ('exact learned emission count', single.format(events='[tr.beforeFire.time]'), single.format(events='[]')),
        ('FAST exit must follow the raw origin', fast.format(date='origin < s.time'), fast.format(date='True')),
        ('zero-input quiescence needs arrival isolation',
         quiet.format(arrivals='∀ p, NoArrivalAt e i p'), quiet.format(arrivals='True')),
    ]


def main():
    controls = cases()
    with tempfile.TemporaryDirectory(prefix='hybrid-pulse-negative-', dir=ROOT) as tmp:
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

        # Compile independent valid examples together, then reject each altered
        # contract separately. This avoids repeated dependency loading.
        check('\n'.join(good for _, good, _ in controls), True, 'valid pulse controls')
        for name, _, bad in controls:
            check(bad, False, name)
            print(f'{name}: physical conclusion accepted; altered claim rejected.', flush=True)


if __name__ == '__main__':
    main()
