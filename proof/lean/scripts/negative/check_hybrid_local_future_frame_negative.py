#!/usr/bin/env python3
"""Local empty-route suffix framing retains actual FIREs and queue order."""
from pathlib import Path
import subprocess
import tempfile

from scripts.lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[2]
PREFIX = '''import KernelR.HybridLocalFutureFrame
open KernelR.Hybrid
noncomputable section
'''


def pair(label, template, good, bad):
    assert '@v@' in template
    assert good != bad
    return label, template.replace('@v@', good), template.replace('@v@', bad)


def cases():
    trace = '''example {n θ s u} (e : @Execution n θ (fun _ _ => []) s u)
    (future : List (Delivery n)) (hf : ∀ d∈future,u.time≤d.due) '''
    fired = '''example {n} (s : Snapshot n) (i : Fin n) (hm : s.main i=.ready)
    (hq : s.x i .q=1) (future : List (Delivery n)) '''
    fireProof = ''' := by
  let j : Jump (fun _ _ => []) s {setMain s i .fast with pending:=s.pending++[]} :=
    .fire s i hm hq
  obtain ⟨lifted,hL,hD⟩ := j.appendFuture_emptyRoute future
  exact ⟨lifted,hL⟩
'''
    return [
        pair('local suffix framing retains the full physical ledger including FIRE entries', trace +
             ''': ∃ lifted : Execution θ (fun _ _ => []) (appendPending s future) (appendPending u future),
      lifted.ledger=@v@ := by
  obtain ⟨lifted,hL,hD⟩ := e.appendFuture_emptyRoute future hf
  exact ⟨lifted,hL⟩
''', 'e.ledger', 'Ledger.zero'),
        pair('local suffix framing retains every old delivered occurrence', trace +
             ''': ∃ lifted : Execution θ (fun _ _ => []) (appendPending s future) (appendPending u future),
      lifted.deliveries=@v@ := by
  obtain ⟨lifted,hL,hD⟩ := e.appendFuture_emptyRoute future hf
  exact ⟨lifted,hD⟩
''', 'e.deliveries', '[]'),
        pair('a real local FIRE remains a true emitted occurrence under the queue frame', fired +
             ''': ∃ lifted : Jump (fun _ _ => []) (appendPending s future)
      (appendPending ({setMain s i .fast with pending:=s.pending++[]} : Snapshot n) future),
      lifted.ledger=@v@''' + fireProof,
             '(Jump.fire s i hm hq (route:=fun _ _=>[])).ledger', 'Ledger.zero'),
        pair('a local frame is appended after the old queue in exact operational order', trace +
             ': (appendPending u future).pending=@v@ := by rfl\n', 'u.pending++future', 'future++u.pending'),
        pair('a local queue frame preserves the actual energy endpoint', trace +
             '(i : Fin n) : (appendPending u future).x i .energy=@v@ := by rfl\n', 'u.x i .energy', '100'),
        pair('a local queue frame retains the actual raw-current history', trace +
             '(i : Fin n) (p : Port) : (appendPending u future).raw i p=@v@ := by rfl\n', 'u.raw i p', 'none'),
        pair('a local queue frame retains the actual physical clock', trace +
             ': (appendPending u future).time=@v@ := by rfl\n', 'u.time', 's.time'),
    ]


def main():
    controls = cases()
    with tempfile.TemporaryDirectory(prefix='hybrid-local-future-frame-', dir=ROOT) as tmp:
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

        check('\n'.join(good for _, good, _ in controls), True, 'valid local-frame controls')
        print(f'All {len(controls)} positive local-frame contracts accepted.', flush=True)
        for name, _, bad in controls:
            check(bad, False, name)
            print(f'{name}: valid conclusion accepted; altered claim rejected.', flush=True)
        print(f'{len(controls)} paired local-frame controls passed.', flush=True)


if __name__ == '__main__':
    main()
