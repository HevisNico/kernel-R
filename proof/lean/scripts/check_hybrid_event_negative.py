#!/usr/bin/env python3
"""Compile physical event controls and reject altered bounds or chronology."""
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
PREFIX = 'import KernelR.HybridEventBudget\nopen KernelR.Hybrid\n'


def main():
    fire = '''example {{n θ ε route s u}} (e : @Execution n θ route s u)
    (hs : BirthState s) (hb : PhysicalBox θ ε) (i : Fin n) :
    ((e.signal i).count : ℝ) ≤ u.time + {allowance} := by
  exact e.fire_count_bound hs hb i
'''
    fast = '''example {{n θ ε route s u}} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hi : UpperRegion s) (i : Fin n)
    (hm : s.main i = .fast) (hq : s.x i .q = 1) (hu : u.main i ≠ .fast) :
    s.time + {duration} ≤ u.time := by
  exact e.fast_departure_not_early hb hi i hm hq hu
'''
    auxiliary = '''example {{n θ ε route s u}} (e : @Execution n θ route s u)
    (hs : BirthState s) (hb : PhysicalBox θ ε) (i : Fin n) (p : Port) :
    (e.auxCount i p : ℝ) ≤ {rate} * u.time + 10 := by
  exact e.aux_count_bound hs hb i p
'''
    queue = '''example {{n θ route s u}} (e : @Execution n θ route s u)
    (hr : CausalRouter route) (hs : PendingFuture s) (d : Delivery n)
    (hd : d ∈ u.pending) : u.time {order} d.due := by
  exact e.pending_future hr hs d hd
'''
    global_budget = '''example {{n θ ε route s u F}} (e : @Execution n θ route s u)
    (hs : BirthState s) (hb : PhysicalBox θ ε) (hr : FanoutBound route F)
    (T : ℝ) (ht : u.time ≤ T) :
    (e.jumpCount : ℝ) ≤ (n : ℝ) * (27 * T + 33) +
      2 * ((s.pending.length : ℝ) + {fanout} * (n : ℝ) * (T + 1)) := by
  exact e.jump_count_through hs hb hr T ht
'''
    cases = [
        ('unfinished FAST allowance', fire.format(allowance='1'), fire.format(allowance='0')),
        ('FAST departure lower bound', fast.format(duration='1'), fast.format(duration='3 / 2')),
        ('all auxiliary transitions', auxiliary.format(rate='8'), auxiliary.format(rate='4')),
        ('pending token may be due now', queue.format(order='≤'), queue.format(order='<')),
        ('routed delivery budget', global_budget.format(fanout='(F : ℝ)'),
         global_budget.format(fanout='0')),
    ]
    with tempfile.TemporaryDirectory(prefix='hybrid-event-negative-', dir=ROOT) as tmp:
        path = Path(tmp) / 'Check.lean'
        for name, good, bad in cases:
            for expected, source in [(True, good), (False, bad)]:
                path.write_text(PREFIX + source)
                result = subprocess.run(['lake', 'env', 'lean', str(path)], cwd=ROOT,
                                        text=True, stdout=subprocess.PIPE,
                                        stderr=subprocess.STDOUT, timeout=120)
                if (result.returncode == 0) != expected:
                    raise SystemExit(f'{name}: unexpected result:\n{result.stdout}')
                if not expected and 'error:' not in result.stdout:
                    raise SystemExit(f'{name}: failed without a Lean diagnostic:\n{result.stdout}')
            print(f'{name}: physical conclusion accepted; altered claim rejected.', flush=True)


if __name__ == '__main__':
    main()
