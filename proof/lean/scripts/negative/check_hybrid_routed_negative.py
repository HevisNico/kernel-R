#!/usr/bin/env python3
"""Reject lost routed inputs, future source loss, wrong contacts and erased jitter."""
from pathlib import Path
import subprocess
import tempfile

from scripts.lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[2]
PREFIX = '''import KernelR.HybridPreparedContact
open KernelR.Hybrid
'''


def cases():
    opening = """example (delay : ℝ → ℝ) : (teachingContact delay).route 0 160 = {value} := by
  norm_num [teachingContact,Contact.route]
"""
    closing = """example (delay : ℝ → ℝ) : (teachingContact delay).route 0 310 = {value} := by
  norm_num [teachingContact,Contact.route]
"""
    jitter = """example {{n}} (c : Contact n) (t latency : ℝ)
    (h₁ : 3/10 ≤ c.delay (t+latency) ∧ c.delay (t+latency) ≤ 2/5)
    (h₂ : 3/10 ≤ c.delay (t+8+latency) ∧ c.delay (t+8+latency) ≤ 2/5) :
    {value} ≤ (c.token (t+8+latency)).due - (c.token (t+latency)).due := by
  have h := (c.period_eight_gap t latency h₁ h₂).1
  linarith
"""
    projection = """example {{n θ route s u}} (e : @Execution n θ route s u) (c : Contact n)
    (hw : ∀ event ∈ e.ledger.emissions,
      (route event.1 event.2).filter (fun d => d.cell = c.target) = c.route event.1 event.2) :
    e.issuedTo c.target = ((e.emissionTimes c.{value}).filter
      (fun t => c.opens ≤ t ∧ t < c.closes)).map c.token := by
  exact e.issuedTo_contact c hw
"""
    port = """example {{n}} (c : Contact n) (p : Port) (t : ℝ) : (c.token t).port = {value} := by
  rfl
"""
    routed = """example {{n θ route s u}} (e : @Execution n θ route s u) (i : Fin n)
    (hf : PendingFuture u) (hs : ∀ d ∈ s.pending, d.cell = i → u.time < d.due)
    (hr : ∀ event ∈ e.ledger.emissions, ∀ d ∈ route event.1 event.2,
      d.cell = i → d.due {relation} u.time) : {deliveries}.Perm (e.issuedTo i) := by
  exact e.cell_deliveries_perm_issued i hf hs hr
"""
    pending = """example {{n θ route s u}} (e : @Execution n θ route s u)
    (i : Fin n) (past later : List (Delivery n))
    (hq : (s.pending.filter (fun d => d.cell = i)).Perm (past ++ later))
    (hd : (e.cellDeliveries i).Perm past)
    (hr : ∀ event ∈ e.ledger.emissions, ∀ d ∈ route event.1 event.2, d.cell ≠ i) :
    {value}.Perm later := by
  exact e.cell_pending_perm_of_prefix i past later hq hd hr
"""
    count = """example {{θ ε route s u}} (e : @Execution 2 θ route s u)
    (hb : PhysicalBox θ ε) (hi : UpperRegion s) (hv : RawValid s)
    (hs : PreparedSection s 0) (hq : s.x 0 .q = 1/10)
    (hz : 9/5 ≤ Real.exp (s.x 0 (.z 0)) ∧ Real.exp (s.x 0 (.z 0)) ≤ 12/5)
    (hr : s.raw 0 0 = some s.time) (ho : ∀ q, q ≠ 0 → s.raw 0 q = none)
    (hqueue : (s.pending.filter (fun d => d.cell = 0)).Perm (sourceTrain 0 0 168 8 15))
    (hclosed : ∀ event ∈ e.ledger.emissions, ∀ d ∈ route event.1 event.2, d.cell ≠ 0)
    (ht : s.time = 160) (hu : u.time = 3199/10) (hf : PendingFuture u)
    (hfuture : ∀ d ∈ s.pending, d.cell = 1 → 320 ≤ d.due)
    (delay : ℝ → ℝ) (hd : ∀ t, 3/10 ≤ delay t ∧ delay t ≤ 2/5)
    (hw : ∀ event ∈ e.ledger.emissions,
      (route event.1 event.2).filter (fun d => d.cell = 1) = (teachingContact delay).route event.1 event.2) :
    (e.cellDeliveries 1).length = {value} := by
  have h := e.teaching_contact_sources hb hi hv hs hq hz hr ho hqueue hclosed ht hu hf hfuture delay hd hw
  have hl := congrArg List.length h
  simp only [List.length_ofFn] at hl
  omega
"""
    date = """example {{G : ℝ}} (hg : 9/5 ≤ G ∧ G ≤ 12/5)
    (delay : ℝ → ℝ) (hd : ∀ t, 3/10 ≤ delay t ∧ delay t ≤ 2/5) (k : Fin 16) :
    {value} < ((teachingContact delay).token (160+8*k.val+restLatency G)).due := by
  have h := (teachingContact.date_bounds hg delay hd k).1
  linarith
"""
    return [
        ('the contact includes its opening date', opening.format(value='[(teachingContact delay).token 160]'), opening.format(value='[]')),
        ('the contact excludes its closing date', closing.format(value='[]'), closing.format(value='[(teachingContact delay).token 310]')),
        ('fresh wire jitter survives common-latency cancellation', jitter.format(value='79/10'), jitter.format(value='8')),
        ('wire tokens originate at the actual sending cell', projection.format(value='source'), projection.format(value='target')),
        ('sender input and receiver port are distinct data', port.format(value='c.port'), port.format(value='p')),
        ('routed arrivals are local to the receiving cell', routed.format(relation='<',deliveries='(e.cellDeliveries i)'), routed.format(relation='<',deliveries='e.deliveries')),
        ('a terminal-date routed token may still be pending', routed.format(relation='<',deliveries='(e.cellDeliveries i)'), routed.format(relation='≤',deliveries='(e.cellDeliveries i)')),
        ('future queues at other cells remain present', pending.format(value='(u.pending.filter (fun d => d.cell = i))'), pending.format(value='u.pending')),
        ('sixteen B deliveries are derived from actual A sources', count.format(value='16'), count.format(value='15')),
        ('coarse real latency cannot claim the sharper certificate lower bound', date.format(value='803/5'), date.format(value='804/5')),
    ]


def main():
    controls = cases()
    with tempfile.TemporaryDirectory(prefix='hybrid-routed-negative-', dir=ROOT) as tmp:
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

        construction = '''example : CausalRouter (teachingContact (fun _ => 7/20)).route :=
  (teachingContact (fun _ => 7/20)).causal (by intro t; norm_num [teachingContact])
example : FanoutBound (teachingContact (fun _ => 7/20)).route 1 :=
  (teachingContact (fun _ => 7/20)).fanout
'''
        check(construction + '\n'.join(good for _, good, _ in controls), True, 'valid routed controls')
        for name, _, bad in controls:
            check(bad, False, name)
            print(f'{name}: physical conclusion accepted; altered claim rejected.', flush=True)


if __name__ == '__main__':
    main()
