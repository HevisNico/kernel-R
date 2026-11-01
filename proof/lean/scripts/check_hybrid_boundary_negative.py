#!/usr/bin/env python3
"""Reject lost cut events, consumed boundary tokens and altered birth preparation."""
from pathlib import Path
import subprocess
import tempfile

from lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[1]
PREFIX = '''import KernelR.HybridBirthPreparation
open KernelR.Hybrid
'''


def cases():
    cutoff = """example {{n θ route s u}} (e : @Execution n θ route s u)
    (hf : PendingFuture u) (hr : ∀ i t, route i t = []) :
    (e.deliveries.filter (fun d => d.due {value} u.time)).Perm
      (s.pending.filter (fun d => d.due {value} u.time)) := by
  exact e.deliveries_before_perm_sources hf hr
"""
    deliveries = """example {{n θ route s u v}} {{e : @Execution n θ route s u}}
    {{cut : Execution θ route s v}} (c : e.Continuation cut) :
    e.deliveries = {value} := by
  exact c.deliveries
"""
    balance = """example {{n θ route s u v}} {{e : @Execution n θ route s u}}
    {{cut : Execution θ route s v}} (c : e.Continuation cut) (i : Fin n) (p : Port) :
    e.ledger.error i p = {value} := by
  exact c.error_balance i p
"""
    pending = """example {{n θ route s u}} (e : @Execution n θ route s u)
    (past later : List (Delivery n)) (hq : s.pending = past ++ later)
    (hd : e.deliveries.Perm past) (hr : ∀ i t, route i t = []) : u.pending.Perm {value} := by
  exact e.pending_perm_of_prefix past later hq hd hr
"""
    zero_ready = """example {{n θ route s u}} (e : @Execution n θ route s u)
    (ht : u.time = s.time) (i : Fin n) (hm : s.main i = .ready) (hq : s.x i .q ≠ {value}) :
    e.AllStates (fun v => v.main i = .ready) := by
  exact e.zero_duration_ready_main ht i hm hq
"""
    raw = """example {{n θ route s u}} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) (hr : s.raw i p = none)
    (hdates : ∀ d ∈ e.deliveries, d.due = u.time) : {value} := by
  exact e.raw_none_or_terminal i p hr hdates
"""
    count = """example {{n θ route born u i p}} {{e : @Execution n θ route born u}}
    (phase : BirthPreparedBoundary e i p) : (e.emissionTimes i).length = {value} := by
  have h := phase.emissions
  omega
"""
    resting = """example {{n θ route born u i p}} {{e : @Execution n θ route born u}}
    (phase : BirthPreparedBoundary e i p) : u.x i .q = {value} := by
  have h := phase.charge_rest
  linarith
"""
    staged_gain = """example {{n θ fresh routeBefore routeAfter born u i p}}
    {{e : @StagedExecution n θ fresh routeBefore routeAfter born u}}
    (phase : StagedPreparation e i p) :
    e.afterBirth.x i.castSucc (.z p) = born.x i (.z p) + {value} := by
  have h := phase.gain_target
  linarith
"""
    full_contract = """example {{n θ ε route born u}} (e : @Execution n θ route born u)
    (hborn : BirthState born) (hb : PhysicalBox θ ε) (i : Fin n) (p : Port) (hp : p ≠ 1)
    (ha : ∀ q, born.aux i q = .ready)
    (hq : born.pending = sourceTrain i p 0 8 16 ++ sourceTrain i p 160 8 16)
    (hr : ∀ i t, route i t = []) (ht : u.time = {value}) :
    Nonempty (BirthPreparedBoundary e i p) := by
  exact e.birth_prepared_at_second_train hborn hb i p hp ha hq hr ht
"""
    return [
        ('a source due at the terminal date need not be consumed', cutoff.format(value='<'), cutoff.format(value='≤')),
        ('cutting a flow retains all actual deliveries', deliveries.format(value='cut.deliveries ++ c.tail.deliveries'), deliveries.format(value='c.tail.deliveries')),
        ('cutting a flow retains past learning', balance.format(value='cut.ledger.error i p + c.tail.ledger.error i p'), balance.format(value='c.tail.ledger.error i p')),
        ('later tokens remain in the pending queue', pending.format(value='later'), pending.format(value='[]')),
        ('zero-time READY preservation needs exclusion of its real threshold', zero_ready.format(value='1'), zero_ready.format(value='0')),
        ('a terminal source may still be pending', raw.format(value='u.raw i p = none ∨ u.raw i p = some u.time'), raw.format(value='u.raw i p = some u.time')),
        ('the complete first phase still emits twelve times', count.format(value='12'), count.format(value='13')),
        ('the charge at the boundary is exactly resting', resting.format(value='1/10'), resting.format(value='7/50')),
        ('the existing cell retains its acquired gain at birth', staged_gain.format(value='9/5'), staged_gain.format(value='0')),
        ('the 160 boundary contract cannot be moved to the next input at 168', full_contract.format(value='160'), full_contract.format(value='168')),
    ]


def main():
    controls = cases()
    with tempfile.TemporaryDirectory(prefix='hybrid-boundary-negative-', dir=ROOT) as tmp:
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

        # At zero duration a source due now can remain pending. Its presence
        # does not force an arrival or invalidate the strictly-past theorem.
        construction = '''example (θ : Fin 1 → Parameters) :
    let s : Snapshot 1 := { Newborn.nominal.snapshot with pending := [⟨0,0,0⟩] }
    PendingFuture s ∧ (Execution.nil s : Execution θ (fun _ _ => []) s s).deliveries = [] := by
  dsimp [PendingFuture,Newborn.snapshot]
  constructor
  · intro d hd
    simp only [List.mem_singleton] at hd
    subst d
    exact le_rfl
  · rfl
'''
        check(construction + '\n'.join(good for _, good, _ in controls), True, 'valid boundary controls')
        for name, _, bad in controls:
            check(bad, False, name)
            print(f'{name}: physical conclusion accepted; altered claim rejected.', flush=True)


if __name__ == '__main__':
    main()
