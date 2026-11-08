#!/usr/bin/env python3
"""Reject altered conclusions of the actual protected MARK preparation case."""
from pathlib import Path
import subprocess
import tempfile

from scripts.lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[2]
PREFIX = '''import KernelR.HybridProtectedPulse
open KernelR.Hybrid
'''


def cases():
    dose = """example {{n θ route s u i p}} {{e : @Execution n θ route s u}}
    (pulse : ProtectedPulse e i p) : e.ledger.mark i p = {value} := by
  have h := pulse.mark_dose
  linarith
"""
    recovery = """example {{n θ route s u i p}} {{e : @Execution n θ route s u}}
    (pulse : ProtectedPulse e i p) : u.x i .b = s.x i .b + {value} := by
  have h := pulse.recovery_gain
  linarith
"""
    error = """example {{n θ route s u i p}} {{e : @Execution n θ route s u}}
    (pulse : ProtectedPulse e i p) (q : Port) : e.ledger.error i q = {value} := by
  have h := pulse.error_zero q
  linarith
"""
    outputs = """example {{n θ route s u i p}} {{e : @Execution n θ route s u}}
    (pulse : ProtectedPulse e i p) : {value} := by
  exact pulse.emissions
"""
    gain = """example {{n θ route s u i p}} {{e : @Execution n θ route s u}}
    (pulse : ProtectedPulse e i p) (q : Port) : u.x i (.z q) = s.x i (.z q) + {value} := by
  have h := pulse.gain_preserved q
  linarith
"""
    mode = """example {{n θ route s u i p}} {{e : @Execution n θ route s u}}
    (pulse : ProtectedPulse e i p) : u.main i = .{value} := by
  exact pulse.prepared.ready
"""
    charge = """example {{n θ route s u i p}} {{e : @Execution n θ route s u}}
    (pulse : ProtectedPulse e i p) : u.x i .q = {value} := by
  have h := pulse.charge_rest
  linarith
"""
    return [
        ('protected MARK is full', dose.format(value='1/10'), dose.format(value='0')),
        ('protected recovery increases once', recovery.format(value='1/10'), recovery.format(value='1/5')),
        ('protected ERROR is zero on every port', error.format(value='0'), error.format(value='3/5')),
        ('protected input emits nothing', outputs.format(value='e.emissionTimes i = []'), outputs.format(value='e.emissionTimes i = [s.time]')),
        ('protected input preserves every gain', gain.format(value='0'), gain.format(value='3/5')),
        ('protected input restores READY', mode.format(value='ready'), mode.format(value='slow')),
        ('protected return has exact resting charge', charge.format(value='1/10'), charge.format(value='7/50')),
    ]


def main():
    controls = cases()
    with tempfile.TemporaryDirectory(prefix='hybrid-protected-negative-', dir=ROOT) as tmp:
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

        check('\n'.join(good for _, good, _ in controls), True, 'valid protected controls')
        for name, _, bad in controls:
            check(bad, False, name)
            print(f'{name}: physical conclusion accepted; altered claim rejected.', flush=True)


if __name__ == '__main__':
    main()
