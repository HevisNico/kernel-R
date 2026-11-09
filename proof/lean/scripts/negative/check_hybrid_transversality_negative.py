#!/usr/bin/env python3
"""Check five transverse contact APIs and the flat-crossing boundary case."""
from pathlib import Path
import subprocess
import tempfile

from scripts.lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[2]
PREFIX = """import KernelR.HybridCadenceHighFireExistence
import KernelR.HybridMidLearnedFire
open KernelR.Hybrid Set
"""

CONTACTS = [
    (
        'sensor',
        'auxPulse_first_sensor_crossing_transversal',
        '''(hl : 1 / 40 - 1 / 100000 ≤ initial)
    (hu : initial ≤ 1 / 40 + 1 / 100000)
    (ha : 31 ≤ amplitude) (hb : amplitude ≤ 60)''',
        'auxPulse', '1 / 100', '1 / 40', 'hl hu ha hb',
    ),
    (
        'learned main',
        'readyPulse_first_learned_crossing_transversal',
        '''(hq : 1 / 10 - 1 / 100000 ≤ initial ∧ initial ≤ 7 / 50)
    (hg : 9 / 5 ≤ amplitude ∧ amplitude ≤ 2)''',
        'readyPulse', '3 / 10', '9 / 10', 'hq hg',
    ),
    (
        'mid-learned main',
        'readyPulse_first_mid_learned_crossing_transversal',
        '''(hq : 1 / 10 - 1 / 100000 ≤ initial ∧ initial ≤ 7 / 50)
    (hg : 9 / 5 ≤ amplitude ∧ amplitude ≤ 11 / 5)''',
        'readyPulse', '3 / 10', '9 / 10', 'hq hg',
    ),
    (
        'residual cadence',
        'readyPulse_cadence_residual_first_crossing_transversal',
        '''(hq : 1 / 10 - 1 / 100000 ≤ initial ∧ initial ≤ 3 / 10)
    (hg : 9 / 5 ≤ amplitude ∧ amplitude ≤ 19 / 10)''',
        'readyPulse', '2 / 5', '9 / 10', 'hq hg',
    ),
    (
        'high-gain cadence',
        'readyPulse_cadence_high_first_crossing_transversal',
        '''(hq : 1 / 10 ≤ initial ∧ initial ≤ 8 / 25)
    (hg : 16 / 5 ≤ amplitude ∧ amplitude ≤ 7 / 2)''',
        'readyPulse', '4 / 25', '13 / 50', 'hq hg',
    ),
]


def contact_sources(theorem, hypotheses, response, early, deadline, arguments):
    slope = f'deriv ({response} initial amplitude start) (start + latency)'
    template = f"""example {{initial amplitude start : ℝ}}
    {hypotheses} :
    ∃ latency : ℝ, {early} < latency ∧ latency < {deadline} ∧
      {response} initial amplitude start (start + latency) = 1 ∧
      (∀ t ∈ Ico start (start + latency), {response} initial amplitude start t < 1) ∧
      SLOPE := by
  exact {theorem} {arguments}
"""
    return template.replace('SLOPE', f'0 < {slope}'), template.replace('SLOPE', f'{slope} ≤ 0')


FLAT_PREFIX = """let f : ℝ → ℝ := fun t => 1 + (t - 1) ^ 3
  have derivative : HasDerivAt f 0 1 := by
    convert ((((hasDerivAt_id (1 : ℝ)).sub_const 1).pow 3).const_add 1) using 1 <;> norm_num [f]
  have before : ∀ t ∈ Ico (0 : ℝ) 1, f t < 1 := by
    intro t ht
    have negative : t - 1 < 0 := by linarith [ht.2]
    have cube : (t - 1) ^ 3 < 0 := by
      rw [show (3 : ℕ) = 2 + 1 by rfl, pow_succ]
      exact mul_neg_of_pos_of_neg (sq_pos_of_ne_zero (ne_of_lt negative)) negative
    change 1 + (t - 1) ^ 3 < 1
    linarith
  """


def main():
    cases = [
        (name, *contact_sources(theorem, hypotheses, response, early, deadline, arguments))
        for name, theorem, hypotheses, response, early, deadline, arguments in CONTACTS
    ]
    flat = """example :
    ∃ f : ℝ → ℝ, Continuous f ∧ f 0 < 1 ∧ f 2 > 1 ∧ f 1 = 1 ∧
      (∀ t ∈ Ico (0 : ℝ) 1, f t < 1) ∧ SLOPE := by
  """ + FLAT_PREFIX + """refine ⟨f, by dsimp [f]; fun_prop, by norm_num [f],
    by norm_num [f], by norm_num [f], before, ?_⟩
  exact derivative.deriv
"""
    cases.append((
        'a strict later horizon permits a flat first crossing',
        flat.replace('SLOPE', 'deriv f 1 = 0'),
        flat.replace('SLOPE', '0 < deriv f 1'),
    ))
    with tempfile.TemporaryDirectory(prefix='transversality-', dir=ROOT) as directory:
        path = Path(directory) / 'Check.lean'
        command = lean_check_command(directory, root_module='KernelR.HybridCadenceHighFireExistence')
        for name, valid, invalid in cases:
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
    print(f'{len(cases)} paired transversality controls passed.', flush=True)


if __name__ == '__main__':
    main()
