#!/usr/bin/env python3
"""Guard actual learned-source iteration and complete first-train existence."""
from pathlib import Path
import subprocess
import tempfile

from scripts.lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[2]
PREFIX = 'import KernelR.HybridBirthPreparationExists\nopen KernelR.Hybrid\n'


def cases():
    contract = """example {{θ ε born}} (hs : @BirthState 1 born) (hb : PhysicalBox θ ε)
    (ha : ∀ p, born.aux 0 p = .ready)
    (hq : born.pending = sourceTrain 0 0 0 8 {count} ++ sourceTrain 0 0 160 8 16) :
    ∃ c : ConstructedBirthPreparation θ born, CompleteThrough c.execution 128 := by
  obtain ⟨c,_⟩ := birth_protocol_preparation_exists hs hb ha hq
  exact ⟨c,c.complete⟩
"""
    ctx = """example {{θ born}} (c : ConstructedBirthPreparation θ born) """
    date = ctx + """: c.final.time = {value} := by exact c.date
"""
    complete = ctx + """: CompleteThrough c.execution {value} := by exact c.complete
"""
    calendar = ctx + """: c.execution.deliveries = sourceTrain 0 0 0 8 {count} := by exact c.deliveries
"""
    pending = ctx + """: c.final.pending = sourceTrain 0 0 160 8 {count} := by exact c.pending
"""
    charge = ctx + """: c.final.x 0 .q = {value} := by exact c.charge
"""
    raw = ctx + """(p : Port) : c.final.raw 0 p = {value} := by exact c.raw_none 0 p
"""
    outcome = """example {{θ ε born}} (c : ConstructedBirthPreparation θ born) (hb : PhysicalBox θ ε) """
    outputs = outcome + """: (c.execution.emissionTimes 0).length = {value} := by
  obtain ⟨train⟩ := c.outcome hb
  exact train.emissions
"""
    error = outcome + """: c.execution.ledger.error 0 0 = {value} := by
  obtain ⟨train⟩ := c.outcome hb
  exact train.error_target
"""
    mark = outcome + """: c.execution.ledger.mark 0 0 = {value} := by
  obtain ⟨train⟩ := c.outcome hb
  exact train.mark_target
"""
    recovery = outcome + """: c.final.x 0 .b = {value} := by
  obtain ⟨train⟩ := c.outcome hb
  exact train.recovery_gain
"""
    gain = outcome + """: c.final.x 0 (.z 0) = born.x 0 (.z 0)+{value} := by
  obtain ⟨train⟩ := c.outcome hb
  exact train.gain_target
"""
    main = outcome + """: c.final.main 0 = .{value} := by
  obtain ⟨train⟩ := c.outcome hb
  exact train.prepared.ready
"""
    tctx = """example {{θ s count later}} (t : PreparedLearnedTrain θ s count later) """
    tcount = tctx + """: t.execution.ledger.emissions.length = {value} := by exact t.emission_count
"""
    tcalendar = tctx + """: t.execution.deliveries = sourceTrain 0 0 (s.time+8) 8 {value} := by exact t.deliveries
"""
    tqueue = tctx + """: t.final.pending = {value} := by exact t.pending
"""
    tcharge = tctx + """: t.final.x 0 .q = {value} := by exact t.charge
"""
    tdate = tctx + """: t.final.time = s.time+8*(count:ℝ)+{value} := by exact t.date
"""
    cycle = """example {{θ s}} (c : PreparedLearnedCycle θ s) :
    c.execution.ledger.error 0 0 = {value} := by exact c.error_zero 0
"""
    fast = """example {{θ s}} {{c : FirstLearnedFire θ (fun _ _ => []) s 0 0}}
    (f : LearnedFastEnd c) : f.final.time = c.final.time+{value} := by exact f.date
"""
    return [
        ('the whole first-train factory retains the original source family', contract.format(count='16'), contract.format(count='15')),
        ('the constructed preparation reaches its actual horizon', date.format(value='128'), date.format(value='160')),
        ('terminal saturation precedes the next source train', complete.format(value='128'), complete.format(value='160')),
        ('only the original sixteen preparation sources are delivered', calendar.format(count='16'), calendar.format(count='17')),
        ('all sixteen second-train tokens are still pending', pending.format(count='16'), pending.format(count='15')),
        ('the real return and wait retain charge one tenth', charge.format(value='1/10'), charge.format(value='1/4')),
        ('every raw input has physically expired at preparation', raw.format(value='none'), raw.format(value='some 120')),
        ('the constructed birth train yields twelve actual outputs', outputs.format(value='12'), outputs.format(value='13')),
        ('learned-source iteration adds no further ERROR', error.format(value='9/5'), error.format(value='12/5')),
        ('the original protected MARK remains the only recovery dose', mark.format(value='1/10'), mark.format(value='1/5')),
        ('prepared recovery remains relative to its own birth', recovery.format(value='born.x 0 .b+1/10'), recovery.format(value='9/50')),
        ('the trained own gain is preserved', gain.format(value='9/5'), gain.format(value='12/5')),
        ('the main genuinely ends READY', main.format(value='ready'), main.format(value='slow')),
        ('the active raw is counted once in learned-source iteration', tcount.format(value='count+1'), tcount.format(value='count')),
        ('only future sources require new deliveries in the iteration', tcalendar.format(value='count'), tcalendar.format(value='count+1')),
        ('the arbitrary later queue is preserved exactly', tqueue.format(value='later'), tqueue.format(value='[]')),
        ('each actual learned return ends at one tenth', tcharge.format(value='1/10'), tcharge.format(value='1/4')),
        ('the train waits until the true seven-and-a-half section', tdate.format(value='15/2'), tdate.format(value='8')),
        ('a learned cycle does not restart the ERROR dose', cycle.format(value='0'), cycle.format(value='3/5')),
        ('generic FAST exit keeps its real one-unit duration', fast.format(value='1'), fast.format(value='1/2')),
    ]


def main():
    controls = cases()
    with tempfile.TemporaryDirectory(prefix='hybrid-preparation-existence-negative-', dir=ROOT) as tmp:
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

        check('\n'.join(good for _, good, _ in controls), True, 'valid constructed preparation controls')
        for name, _, bad in controls:
            check(bad, False, name)
            print(f'{name}: physical conclusion accepted; altered claim rejected.', flush=True)


if __name__ == '__main__':
    main()
