#!/usr/bin/env python3
"""Reject altered real latency roots and unsupported common physical calendars."""
from pathlib import Path
import subprocess
import tempfile

from lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[1]
PREFIX = '''import KernelR.HybridPreparedCalendar
open KernelR.Hybrid
'''


def cases():
    lower = """example {{G : ℝ}} (hg : 9/5 ≤ G ∧ G ≤ 12/5) : {value} < restLatency G := by
  have h := (restLatency_spec hg).1
  linarith
"""
    root = """example {{G : ℝ}} (hg : 9/5 ≤ G ∧ G ≤ 12/5) :
    readyPulse (1/10) G 0 (restLatency G) = {value} := by
  have h := (restLatency_spec hg).2.2
  linarith
"""
    unique = """example {{G t : ℝ}} (hg : 9/5 ≤ G ∧ G ≤ 12/5)
    (ht : t ∈ Set.Icc 0 (9/10)) (hroot : readyPulse (1/10) G 0 t = 1) :
    t = restLatency G + {value} := by
  have h := restLatency_unique hg ht hroot
  linarith
"""
    emission = """example {{n θ ε route s u i}} {{e : @Execution n θ route s u}}
    (pulse : LearnedPulse e i) (hb : PhysicalBox θ ε) (hi : UpperRegion s)
    (p : Port) (hs : PreparedSection s i) (hq : {rest})
    (hg : 9/5 ≤ Real.exp (s.x i (.z p)) ∧ Real.exp (s.x i (.z p)) ≤ 12/5)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q) (ht : s.time + 15/2 ≤ u.time) :
    e.emissionTimes i = [{value}] := by
  exact pulse.emission_at_rest hb hi p hs hq hg hr ho hno ht
"""
    calendar = """example {{n θ ε route s u}} (hb : @PhysicalBox n θ ε)
    (i : Fin n) (p : Port) (times : List ℝ) (e : Execution θ route s u)
    (hi : UpperRegion s) (hv : RawValid s) (hs : PreparedSection s i) (hq : s.x i .q = 1/10)
    (hz : 9/5 ≤ Real.exp (s.x i (.z p)) ∧ Real.exp (s.x i (.z p)) ≤ 12/5)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hcalendar : e.cellDeliveries i = times.map (fun t => ⟨i,p,t⟩))
    (hspace : (s.time :: times).Pairwise (fun t v => t + 15/2 ≤ v))
    (hquiet : ∀ t ∈ s.time :: times, t + 15/2 ≤ u.time) :
    e.emissionTimes i = ({value}).map (fun t => t + restLatency (Real.exp (s.x i (.z p)))) := by
  exact prepared_cell_calendar_of_valid hb i p times e hi hv hs hq hz hr ho hcalendar hspace hquiet
"""
    resting = 's.x i .q = 1/10'
    date = 's.time + restLatency (Real.exp (s.x i (.z p)))'
    return [
        ('the physical rest latency has its proved lower bracket', lower.format(value='3/10'), lower.format(value='1/2')),
        ('the chosen latency solves the real firing equation', root.format(value='1'), root.format(value='2')),
        ('the first-window latency root is unique', unique.format(value='0'), unique.format(value='1')),
        ('the output date retains its actual input origin', emission.format(rest=resting,value=date), emission.format(rest=resting,value='restLatency (Real.exp (s.x i (.z p)))')),
        ('the common calendar retains the initially active input', calendar.format(value='s.time :: times'), calendar.format(value='times')),
        ('common latency requires exact resting charge', emission.format(rest=resting,value=date), emission.format(rest='s.x i .q ≤ 7/50',value=date)),
    ]


def main():
    controls = cases()
    with tempfile.TemporaryDirectory(prefix='hybrid-calendar-negative-', dir=ROOT) as tmp:
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

        construction = '''example : ∃ t : ℝ, 3/10 < t ∧ t < 9/10 ∧ readyPulse (1/10) 2 0 t = 1 :=
  rest_latency_exists (by norm_num)
'''
        check(construction + '\n'.join(good for _, good, _ in controls), True, 'valid calendar controls')
        for name, _, bad in controls:
            check(bad, False, name)
            print(f'{name}: physical conclusion accepted; altered claim rejected.', flush=True)


if __name__ == '__main__':
    main()
