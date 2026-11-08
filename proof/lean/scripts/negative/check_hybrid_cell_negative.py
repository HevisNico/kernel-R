#!/usr/bin/env python3
"""Reject lost multicell traffic and weakened variable-gap input contracts."""
from pathlib import Path
import subprocess
import tempfile

from scripts.lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[2]
PREFIX = '''import KernelR.HybridCellSources
import KernelR.HybridCellPreparedTrain
open KernelR.Hybrid
'''


def cases():
    local_prefix = """example {{n θ route s u i d ds}} {{e : @Execution n θ route s u}}
    (cut : CellDeliveryStep e i d ds) : {value} = [] := by
  exact cut.no_earlier
"""
    isolation = """example {{n θ route s u i d ds}} {{e : @Execution n θ route s u}}
    (cut : CellDeliveryStep e i d ds) (j : Fin n) (p : Port) : NoArrivalAt cut.span {value} p := by
  exact cut.no_arrivals_before p
"""
    date = """example {{n θ route s u i d ds}} {{e : @Execution n θ route s u}}
    (cut : CellDeliveryStep e i d ds) : cut.afterArrival.time = d.due + {value} := by
  have h := cut.date.2
  linarith
"""
    pending = """example {{n θ route s u}} (e : @Execution n θ route s u)
    (i : Fin n) (T : ℝ) (hc : CompleteThrough e T)
    (hs : ∀ d ∈ s.pending, d.cell = i → d.due ≤ T)
    (hr : ∀ j t, t ∈ Set.Icc s.time u.time → ∀ d ∈ route j t, d.cell ≠ i) : {value} = [] := by
  exact e.cell_pending_empty i T hc hs hr
"""
    tokens = """example {{n θ route s u}} (e : @Execution n θ route s u)
    (i : Fin n) (T : ℝ) (hc : CompleteThrough e T)
    (hs : ∀ d ∈ s.pending, d.cell = i → d.due ≤ T)
    (hr : ∀ j t, t ∈ Set.Icc s.time u.time → ∀ d ∈ route j t, d.cell ≠ i) :
    {value}.Perm (s.pending.filter (fun d => d.cell = i)) := by
  exact e.cell_deliveries_perm_sources i T hc hs hr
"""
    train = """example {{n θ ε route born s u}} (e : @Execution n θ route s u)
    (past : Execution θ route born s) (hborn : BirthState born) (hb : PhysicalBox θ ε)
    (i : Fin n) (p : Port) (times : List ℝ) (hs : PreparedSection s i)
    (hz : 9/5 ≤ Real.exp (s.x i (.z p)) ∧ Real.exp (s.x i (.z p)) ≤ 12/5)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hcal : e.cellDeliveries i = times.map (fun t => ⟨i,p,t⟩))
    (hspace : ({initial}).Pairwise (fun t v => t + {gap} ≤ v))
    (hquiet : ∀ t ∈ s.time :: times, t + {quiet} ≤ u.time) :
    Nonempty (PreparedTrain e i (times.length + {count})) := by
  exact prepared_cell_train hborn hb i p times e past hs hz hr ho hcal hspace hquiet
"""
    good = dict(initial='s.time :: times', gap='15/2', quiet='15/2', count='1')
    return [
        ('other cells remain before the selected delivery', local_prefix.format(value='cut.span.cellDeliveries i'), local_prefix.format(value='cut.span.deliveries')),
        ('arrival isolation is local to the receiving cell', isolation.format(value='i'), isolation.format(value='j')),
        ('selected cell arrival has its real due date', date.format(value='0'), date.format(value='1')),
        ('other cells may retain future pending tokens', pending.format(value='u.pending.filter (fun d => d.cell = i)'), pending.format(value='u.pending')),
        ('cell token conservation retains other traffic', tokens.format(value='(e.cellDeliveries i)'), tokens.format(value='e.deliveries')),
        ('prepared variable-gap train counts actual inputs', train.format(**good), train.format(**dict(good, count='2'))),
        ('the first gap is part of the contract', train.format(**good), train.format(**dict(good, initial='times'))),
        ('short gaps need a separate physical case', train.format(**good), train.format(**dict(good, gap='1/2'))),
        ('the final input needs a quiet return horizon', train.format(**good), train.format(**dict(good, quiet='1/2'))),
    ]


def main():
    controls = cases()
    with tempfile.TemporaryDirectory(prefix='hybrid-cell-negative-', dir=ROOT) as tmp:
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

        check('\n'.join(good for _, good, _ in controls), True, 'valid cell controls')
        for name, _, bad in controls:
            check(bad, False, name)
            print(f'{name}: physical conclusion accepted; altered claim rejected.', flush=True)


if __name__ == '__main__':
    main()
