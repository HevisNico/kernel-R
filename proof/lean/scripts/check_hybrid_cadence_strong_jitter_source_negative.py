#!/usr/bin/env python3
"""Paired true strong responses, variable source framing and actual arrivals."""
from pathlib import Path
import subprocess
import tempfile

from lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[1]
PREFIX = '''import KernelR.HybridCadenceSecondStrongJitterNextSource
open KernelR.Hybrid
noncomputable section
'''


def pair(label, template, good, bad):
    assert '@v@' in template
    assert good != bad
    return label, template.replace('@v@', good), template.replace('@v@', bad)


def cases():
    result = []
    for name, lower, upper in [('First', '37/250', '1/4'), ('Second', '61/500', '7/50')]:
        pre = f'''example {{θ s p H later}} (r : Cadence{name}StrongJitterNextSource θ s p H later) '''
        tests = [
            pair('retains the true variable next-source clock', pre +
                 ': r.final.time=@v@ := by exact r.date\n', 'H', 's.time+4'),
            pair('takes the actual next arrival on the intended port', pre +
                 ': r.execution.deliveries=@v@ := by exact r.deliveries\n', '[⟨0,p,H⟩]', '[]'),
            pair('retains all later source occurrences', pre +
                 ': r.final.pending=@v@ := by exact r.pending\n', 'later', '[]'),
            pair('keeps the carried main mode SLOW at the actual arrival', pre +
                 ': r.final.main 0=.@v@ := by exact r.main_slow\n', 'slow', 'ready'),
            pair('starts fresh RAW at the true next clock', pre +
                 ': r.final.raw 0 p=some (@v@) := by exact r.raw_active\n', 'H', 's.time'),
            pair('preserves the derived lower charge band', pre +
                 ': @v@≤r.final.x 0 .q := by exact r.charge.1\n', lower, '1/2'),
            pair('preserves the derived upper charge band', pre +
                 ': r.final.x 0 .q≤@v@ := by exact r.charge.2\n', upper, '1/10'),
            pair('retains the real emitted FIRE under future framing', pre +
                 ': r.execution.ledger.emissions=@v@ := by exact r.emissions\n', '[(0,r.fire.final.time)]', '[]'),
            pair('constructs exactly one true emitted occurrence', pre +
                 ': (r.execution.emissionTimes 0).length=@v@ := by exact r.emission_count\n', '1', '2'),
            pair('preserves the entire physical ledger during source framing', pre +
                 ': r.framed.ledger=@v@ := by exact r.framed_ledger\n', 'r.offline.ledger', 'Ledger.zero'),
            pair('retains every own acquired gain', pre +
                 '(q : Port) : r.final.x 0 (.z q)=s.x 0 (.z q)@v@ := by exact r.gains 0 q\n', '', '+3/5'),
            pair('retains own acquired recovery', pre +
                 ': r.final.x 0 .b=s.x 0 .b@v@ := by exact r.recovery 0\n', '', '+1/10'),
            pair('has no fictitious ERROR exposure during the protected response', pre +
                 '(q : Port) : r.execution.ledger.error 0 q=@v@ := by exact r.error_zero q\n', '0', '3/5'),
            pair('has no fictitious MARK dose during the strong response', pre +
                 '(q : Port) : r.execution.ledger.mark 0 q=@v@ := by exact r.mark_zero q\n', '0', '1/10'),
            pair('retains the exact physical energy endpoint before arrival', pre +
                 ': r.final.x 0 .energy=@v@ := by exact r.energy\n', 'r.span.final.x 0 .energy', '100'),
            pair('is complete at the actual next-source clock', pre +
                 ': CompleteThrough r.execution @v@ := by exact r.complete\n', 'H', 's.time+4'),
            pair('uses the true exact-rest three-dose root lower window', pre +
                 ': s.time+@v@<r.fire.final.time := by exact r.fire_window.1\n', '13/20', '7/10'),
        ]
        result.extend((name.lower() + ' strong: ' + label, good, bad) for label, good, bad in tests)
    return result


def main():
    controls = cases()
    with tempfile.TemporaryDirectory(prefix='hybrid-strong-jitter-source-', dir=ROOT) as tmp:
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

        check('\n'.join(good for _, good, _ in controls), True, 'valid strong-jitter source controls')
        print(f'All {len(controls)} positive strong-jitter contracts accepted.', flush=True)
        for name, _, bad in controls:
            check(bad, False, name)
            print(f'{name}: valid conclusion accepted; altered claim rejected.', flush=True)
        print(f'{len(controls)} paired strong-jitter source controls passed.', flush=True)


if __name__ == '__main__':
    main()
