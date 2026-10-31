#!/usr/bin/env python3
"""Compile positive physical controls and reject six corresponding false claims."""
from pathlib import Path
import subprocess
import tempfile

from lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[1]
PREFIX = '''import KernelR.Refinement
open KernelR.Hybrid
noncomputable def sample (q : ℝ) : Snapshot 1 :=
  { resting 0 with x := fun i c => match c with
      | .q => q | _ => (resting 0).x i c }
def route : Router 1 := fun _ _ => []
'''


def main():
    fire = '''example : Jump route (sample {q}) (setMain (sample {q}) 0 .fast) := by
  exact Jump.fire (sample {q}) 0 rfl (by norm_num [sample])
'''
    queue = '''def token : Delivery 1 := ⟨0, 0, 0⟩
noncomputable def queued : Snapshot 1 := {{ resting 0 with pending := [token] }}
example : Jump route queued {{ (setRaw queued 0 0 (some 0)) with pending := {out} }} := by
  exact Jump.arrive queued token [] [] rfl rfl rfl
'''
    cap = '''def pars : Fin 1 → Parameters := fun _ => ⟨fun _ => 1, fun _ => 1,
  fun _ => 1, fun _ => 1, fun _ => 1⟩
noncomputable def capped : Snapshot 1 := setAux (resting 0) 0 0 .error
example : errorAct pars capped capped.x 0 0 = {dose} := by
  norm_num [errorAct, capped, pars, setAux, resting]
'''
    energy = '''def pars : Fin 1 → Parameters := fun _ => ⟨fun _ => 4, fun _ => 1,
  fun _ => 1, fun _ => 1, fun _ => 1⟩
noncomputable def emptyReserve : Snapshot 1 :=
  {{ (setAux (resting 0) 0 0 .error) with x := fun i c =>
      if c = .energy then 0 else (resting 0).x i c }}
example : errorAct pars emptyReserve emptyReserve.x 0 0 = {dose} := by
  norm_num [errorAct, emptyReserve, resting]
'''
    partial = '''example : 8 * ((7 / 100 : ℝ) - 1 / 40) = {dose} := by norm_num
'''
    tail = '''example : {claim} := by
  have h : 0 < pulse 0 (1 / 2) := canonical_raw_tail_positive (by norm_num) (by norm_num)
  {proof}
'''
    cases = [
        ('threshold firing', fire.format(q='1'), fire.format(q='(9 / 10)')),
        ('delivery consumption', queue.format(out='[]'), queue.format(out='[token]')),
        ('closed gain cap', cap.format(dose='0'), cap.format(dose='(3 / 5)')),
        ('closed energy gate', energy.format(dose='0'), energy.format(dose='(3 / 5)')),
        ('partial dose', partial.format(dose='9 / 25'), partial.format(dose='3 / 5')),
        ('raw tail', tail.format(claim='0 < pulse 0 (1 / 2)', proof='exact h'),
         tail.format(claim='pulse 0 (1 / 2) = 0', proof='linarith')),
    ]
    with tempfile.TemporaryDirectory(prefix='hybrid-negative-', dir=ROOT) as tmp:
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
                    raise SystemExit(f'{name}: process failed without a Lean diagnostic:\n{result.stdout}')
            print(f'{name}: physical control accepted; false claim rejected.', flush=True)


if __name__ == '__main__':
    main()
