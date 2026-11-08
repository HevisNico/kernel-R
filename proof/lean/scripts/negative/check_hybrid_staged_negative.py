#!/usr/bin/env python3
"""Reject altered staged-birth state, source queues and memory balances."""
from pathlib import Path
import subprocess
import tempfile

from scripts.lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[2]
PREFIX = '''import KernelR.HybridStagedBirth
open KernelR.Hybrid
'''


def cases():
    old_gain = """example {{n s u}} (birth : @BirthStep n s u) (i : Fin n) (p : Port) :
    u.x i.castSucc (.z p) = s.x i (.z p) + {value} := by
  have h := congrFun (birth.old_coordinates i) (.z p)
  linarith
"""
    old_recovery = """example {{n s u}} (birth : @BirthStep n s u) (i : Fin n) :
    u.x i.castSucc .b = s.x i .b + {value} := by
  have h := congrFun (birth.old_coordinates i) .b
  linarith
"""
    date = """example {{n s u}} (birth : @BirthStep n s u) : u.time = s.time + {value} := by
  have h := birth.time_unchanged
  linarith
"""
    pending = """example {{n s u}} (birth : @BirthStep n s u) :
    u.pending.filter (fun d => d.cell ≠ Fin.last n) = {value} := by
  exact birth.old_pending_exact
"""
    mode = """example {{n s u}} (birth : @BirthStep n s u) : u.main (Fin.last n) = .{value} := by
  exact birth.new_ready.ready
"""
    recovery = """example {{n s u}} (birth : @BirthStep n s u) : {value} ≤ u.x (Fin.last n) .b := by
  have h := birth.new_recovery
  linarith
"""
    gain = """example {{n s u}} (birth : @BirthStep n s u) (p : Port) :
    Real.log (nominalGain p) + {value} - 1/100000 ≤ u.x (Fin.last n) (.z p) := by
  have h := birth.new_gain p
  linarith
"""
    target = """example {{n s u}} (birth : @BirthStep n s u) (i : Fin n)
    (d : Delivery (n+1)) (hd : d ∈ birth.sources) : d.cell = {value} := by
  exact birth.source_cell d hd
"""
    future = """example {{n s u}} (birth : @BirthStep n s u)
    (d : Delivery (n+1)) (hd : d ∈ birth.sources) : s.time + {value} ≤ d.due := by
  have h := birth.source_future d hd
  linarith
"""
    old_balance = """example {{n θ fresh routeBefore routeAfter s u}}
    (e : @StagedExecution n θ fresh routeBefore routeAfter s u) (i : Fin n) (p : Port) :
    u.x i.castSucc (.z p) = {value} := by
  exact e.old_gain_balance i p
"""
    new_balance = """example {{n θ fresh routeBefore routeAfter s u}}
    (e : @StagedExecution n θ fresh routeBefore routeAfter s u) (i : Fin n) (p : Port) :
    u.x (Fin.last n) (.z p) = {value} := by
  exact e.new_gain_balance p
"""
    reserve = """example {{n θ fresh ε routeBefore routeAfter s u}}
    (e : @StagedExecution n θ fresh routeBefore routeAfter s u)
    (hb : PhysicalBox (extendParameters θ fresh) ε) (hs : PhysicalInvariant θ s) (i : Fin (n+1)) :
    {value} ≤ u.x i .energy := by
  have h := (e.physical_invariant hb hs).reserve i
  linarith
"""
    return [
        ('birth preserves every existing gain', old_gain.format(value='0'), old_gain.format(value='3/5')),
        ('birth gives no recovery dose to existing cells', old_recovery.format(value='0'), old_recovery.format(value='1/10')),
        ('birth does not advance the clock', date.format(value='0'), date.format(value='1')),
        ('birth retains every old pending token', pending.format(value='s.pending.map liftDelivery'), pending.format(value='[]')),
        ('the fresh main mode is READY', mode.format(value='ready'), mode.format(value='fast')),
        ('the fresh recovery is in its birth band', recovery.format(value='7999/100000'), recovery.format(value='17999/100000')),
        ('the fresh gains are nominal birth gains', gain.format(value='0'), gain.format(value='3/5')),
        ('birth sources target only the new cell', target.format(value='Fin.last n'), target.format(value='i.castSucc')),
        ('birth sources retain their declared due dates', future.format(value='0'), future.format(value='1')),
        ('old learning survives the birth boundary', old_balance.format(value='s.x i (.z p) + e.before.ledger.error i p + e.after.ledger.error i.castSucc p'), old_balance.format(value='s.x i (.z p) + e.after.ledger.error i.castSucc p')),
        ('the new cell has no pre-birth learning ledger', new_balance.format(value='e.birth.newborn.x (.z p) + e.after.ledger.error (Fin.last n) p'), new_balance.format(value='e.birth.newborn.x (.z p) + e.before.ledger.error i p + e.after.ledger.error (Fin.last n) p')),
        ('staged executions preserve the reserve floor', reserve.format(value='50'), reserve.format(value='60')),
    ]


def main():
    controls = cases()
    with tempfile.TemporaryDirectory(prefix='hybrid-staged-negative-', dir=ROOT) as tmp:
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

        construction = '''example : BirthState Newborn.nominal.snapshot := Newborn.nominal_birth_state
example {n} (s : Snapshot n) : Nonempty (BirthStep s (addNewborn s Newborn.nominal [])) := by
  exact birth_step_exists _ [] (by simp) (by simp)
'''
        check(construction + '\n'.join(good for _, good, _ in controls), True, 'valid staged controls')
        for name, _, bad in controls:
            check(bad, False, name)
            print(f'{name}: physical conclusion accepted; altered claim rejected.', flush=True)


if __name__ == '__main__':
    main()
