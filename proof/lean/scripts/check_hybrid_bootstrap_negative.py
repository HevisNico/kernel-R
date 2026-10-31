#!/usr/bin/env python3
"""Keep low-recovery firing separate from the later protected MARK bootstrap."""
from pathlib import Path
import subprocess
import tempfile

from lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[1]
PREFIX = '''import KernelR.HybridLowRecovery
import KernelR.HybridMarkBudget
open KernelR.Hybrid
'''


def cases():
    mode = '''example {{n θ route s u i}} {{e : @Execution n θ route s u}}
    (pulse : LowRecoveryPulse e i) : u.main i = .{mode} := by
  exact pulse.mark_entry.slow
'''
    charge = '''example {{n θ route s u i}} {{e : @Execution n θ route s u}}
    (pulse : LowRecoveryPulse e i) : {lower} ≤ u.x i .q := by
  have h := pulse.mark_entry.charge.1
  linarith
'''
    error = '''example {{n θ route s u i}} {{e : @Execution n θ route s u}}
    (pulse : LowRecoveryPulse e i) (p : Port) : e.ledger.error i p = {dose} := by
  have h := pulse.error_zero p
  linarith
'''
    memory = '''example {{n θ route s u i}} {{e : @Execution n θ route s u}}
    (pulse : LowRecoveryPulse e i) : u.x i .b = s.x i .b + {dose} := by
  have h := pulse.recovery_preserved
  linarith
'''
    budget = '''example {{n θ ε route s u i p}} {{e : @Execution n θ route s u}}
    (cycle : SensorCycle e i p) (hb : PhysicalBox θ ε) (hv : RawValid s)
    (hr : s.raw i p = some s.time) (hn : NoArrivalAt e i p) : {claim} := by
  exact cycle.mark_budget hb hv hr hn
'''
    upper = '''example {{n θ ε route s u i p}} (e : @Execution n θ route s u)
    (cycle : SensorCycle e i p) (hb : PhysicalBox θ ε) (hv : RawValid s)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hn : ∀ q, NoArrivalAt e i q)
    (ha : ∀ q, q ≠ p → s.aux i q = .ready ∧ s.x i (.m q) ≤ 1/40+1/100000) :
    u.x i .b ≤ s.x i .b + {dose} := by
  have h := e.recovery_one_input_budget cycle hb hv hr ho hn ha
  linarith
'''
    return [
        ('low recovery has not returned at the next input', mode.format(mode='slow'), mode.format(mode='ready')),
        ('actual charge at the next protected input', charge.format(lower='7/50'), charge.format(lower='3/20')),
        ('first strong ERROR is protected', error.format(dose='0'), error.format(dose='3/5')),
        ('first strong firing does not prepare recovery', memory.format(dose='0'), memory.format(dose='1/10')),
        ('a MARK budget does not assume full exposure', budget.format(claim='e.ledger.mark i p ≤ 1/10'), budget.format(claim='e.ledger.mark i p = 1/10')),
        ('the next input may increase recovery', upper.format(dose='1/10'), upper.format(dose='0')),
    ]


def main():
    controls = cases()
    with tempfile.TemporaryDirectory(prefix='hybrid-bootstrap-negative-', dir=ROOT) as tmp:
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

        check('\n'.join(good for _, good, _ in controls), True, 'valid bootstrap controls')
        for name, _, bad in controls:
            check(bad, False, name)
            print(f'{name}: physical conclusion accepted; altered claim rejected.', flush=True)


if __name__ == '__main__':
    main()
