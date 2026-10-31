#!/usr/bin/env python3
"""Check physical analytic theorems and reject changed durations/bounds/tails."""
from pathlib import Path
import subprocess
import tempfile

from lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[1]
PREFIX = '''import KernelR.HybridReady
import KernelR.HybridWork
open KernelR.Hybrid
'''


def main():
    fast = '''example {{n θ s u}} (f : @Flow n θ s u) (i : Fin n)
    (hm : s.main i = .fast) (hs : s.x i .q = 1) (hu : u.x i .q = 1 / 4) :
    u.time - s.time = {duration} := by
  exact f.fast_duration i hm hs hu
'''
    mark = '''example {{n θ ε s u}} (f : @Flow n θ s u) (i : Fin n) (p : Port)
    (hb : PhysicalBox θ ε) (hm : s.aux i p = .mark)
    (hs : s.x i (.m p) = 1) (hu : u.x i (.m p) = 4 / 5) :
    u.time - s.time = Real.log ({ratio}) / (θ i).lm p := by
  exact f.mark_duration i p hb hm hs hu
'''
    energy = '''example {{n θ ε route s u}} (e : @Execution n θ route s u)
    (hs : BirthState s) (hb : PhysicalBox θ ε) (i : Fin n) :
    {floor} ≤ u.x i .energy := by
  have h := e.reserve_birth_invariant hs hb i
  linarith
'''
    tail = '''example {{n θ s u}} (f : @Flow n θ s u) (i : Fin n) (p : Port)
    (origin : ℝ) (hm : s.main i = .ready) (hr : s.raw i p = some origin)
    (ho : ∀ j, j ≠ p → s.raw i j = none) (ha : s.aux i p ≠ .error) :
    ∀ t ∈ Set.Icc s.time u.time, f.path t i .q =
      readyPulse (s.x i .q) ({amplitude}) s.time t := by
  exact f.ready_single_pulse_solution i p origin hm hr ho ha
'''
    cases = [
        ('FAST exit duration', fast.format(duration='1'), fast.format(duration='3 / 2')),
        ('physical MARK duration', mark.format(ratio='5 / 4'), mark.format(ratio='4')),
        ('birth reserve floor', energy.format(floor='50'), energy.format(floor='51')),
        ('raw-tail attenuation',
         tail.format(amplitude='Real.exp (s.x i (.z p)) * Real.exp (-a * (s.time - origin))'),
         tail.format(amplitude='Real.exp (s.x i (.z p))')),
    ]
    with tempfile.TemporaryDirectory(prefix='hybrid-analytic-negative-', dir=ROOT) as tmp:
        path = Path(tmp) / 'Check.lean'
        command = lean_check_command(tmp)
        for name, good, bad in cases:
            for expected, source in [(True, good), (False, bad)]:
                path.write_text(PREFIX + source)
                result = subprocess.run([*command, str(path)], cwd=ROOT,
                                        text=True, stdout=subprocess.PIPE,
                                        stderr=subprocess.STDOUT, timeout=120)
                if (result.returncode == 0) != expected:
                    raise SystemExit(f'{name}: unexpected result:\n{result.stdout}')
                if not expected and 'error:' not in result.stdout:
                    raise SystemExit(f'{name}: failed without a Lean diagnostic:\n{result.stdout}')
            print(f'{name}: physical conclusion accepted; altered claim rejected.', flush=True)


if __name__ == '__main__':
    main()
