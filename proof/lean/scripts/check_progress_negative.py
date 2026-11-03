#!/usr/bin/env python3
"""Compile semantic controls before rejecting stronger, false progress claims."""
from pathlib import Path
import subprocess
import tempfile

from lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[1]
PREFIX = '''import KernelR.HybridProgressControls
open KernelR.Hybrid KernelR.Hybrid.Controls
'''

CASES = [
    (
        'all infinite move presentations need not have divergent time',
        '''example (θ : Fin 1 → Parameters) :
    ¬ (∀ run : InfiniteExecution θ (fun _ _ => []),
      BirthState (run.state 0) → ∀ horizon : ℝ, ∃ index,
        horizon < (run.state index).time) := by
  exact unrestricted_infinite_progress_false θ
''',
        '''example (θ : Fin 1 → Parameters) :
    (∀ run : InfiniteExecution θ (fun _ _ => []),
      BirthState (run.state 0) → ∀ horizon : ℝ, ∃ index,
        horizon < (run.state index).time) := by
  exact unrestricted_infinite_progress_false θ
''',
    ),
    (
        'flow subdivisions are not infinitely many physical jumps',
        '''example (θ : Fin 1 → Parameters) :
    ¬ (boundedFlowRun θ).InfinitelyManyJumps := by
  exact boundedFlowRun_not_infinitely_many_jumps θ
''',
        '''example (θ : Fin 1 → Parameters) :
    (boundedFlowRun θ).InfinitelyManyJumps := by
  exact boundedFlowRun_not_infinitely_many_jumps θ
''',
    ),
    (
        'a continuation cannot return to an earlier horizon',
        '''example (θ : Fin 1 → Parameters) :
    ¬ (∃ final, ∃ tail : Execution θ (fun _ _ => []) (restingState 2) final,
      CompleteThrough tail 1) := by
  exact no_past_horizon_continuation θ
''',
        '''example (θ : Fin 1 → Parameters) :
    (∃ final, ∃ tail : Execution θ (fun _ _ => []) (restingState 2) final,
      CompleteThrough tail 1) := by
  exact no_past_horizon_continuation θ
''',
    ),
]


def main():
    with tempfile.TemporaryDirectory(prefix='progress-negative-', dir=ROOT) as directory:
        path = Path(directory) / 'Check.lean'
        command = lean_check_command(directory)
        for name, valid, invalid in CASES:
            for expected, source in ((True, valid), (False, invalid)):
                path.write_text(PREFIX + source)
                result = subprocess.run(
                    [*command, str(path)], cwd=ROOT, text=True,
                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=180,
                )
                if (result.returncode == 0) != expected:
                    raise SystemExit(f'{name}: unexpected result:\n{result.stdout}')
                if not expected and 'error:' not in result.stdout:
                    raise SystemExit(f'{name}: failed without a Lean diagnostic:\n{result.stdout}')
            print(f'PASS {name}: valid control compiles, false claim rejected.', flush=True)
    print(f'{len(CASES)} paired semantic progress controls passed.', flush=True)


if __name__ == '__main__':
    main()
