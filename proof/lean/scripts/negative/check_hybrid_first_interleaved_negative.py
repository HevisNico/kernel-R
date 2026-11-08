#!/usr/bin/env python3
"""Guard the real joint return, newborn learning dose and next source at168."""
from pathlib import Path
import subprocess
import tempfile

from scripts.lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[2]
PREFIX = 'import KernelR.HybridFirstInterleavedPair\nimport KernelR.HybridMidGainSchedule\nopen KernelR.Hybrid\n'


def cases():
    factory = """example {{θ fresh ε born}} (hs : @BirthState 1 born)
    (hb : @PhysicalBox 2 (extendParameters θ fresh) ε)
    (ha : ∀ p, born.aux 0 p = .ready)
    (hq : born.pending = sourceTrain 0 0 0 8 {count} ++ sourceTrain 0 0 160 8 16)
    (newborn : Newborn) (forward backward : ℝ → ℝ)
    (hd : ∀ t, (3/10:ℝ)≤forward t ∧ forward t≤2/5) :
    ∃ c : ConstructedBirthPreparation θ born,
      ∃ b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources,
        ∃ r : FirstWiredArrival b, ∃ s : FirstInterleavedPair r,
          CompleteThrough s.staged.after 168 ∧ s.final.pending.length=46 := by
  exact birth_protocol_first_interleaved_pair_exists hs hb ha hq newborn forward backward hd
"""
    ctx = """example {{θ born fresh newborn forward backward}}
    {{c : ConstructedBirthPreparation θ born}}
    {{b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}}
    {{r : FirstWiredArrival b}} (s : FirstInterleavedPair r) """
    date = ctx + """: s.final.time = {value} := by exact s.date
"""
    complete = ctx + """: CompleteThrough s.staged.after {value} := by exact s.staged_complete
"""
    length = ctx + """: s.final.pending.length = {value} := by exact s.pending_length
"""
    queue = ctx + """: s.final.pending = sourceTrain 0 0 {start} 8 {count} ++ constructedBBirthSources := by exact s.pending
"""
    deliveries = ctx + """: s.execution.deliveries = [⟨0,0,{value}⟩] := by exact s.deliveries
"""
    outputs = ctx + """: s.execution.ledger.emissions = {value} := by exact s.emissions
"""
    charge = ctx + """: s.final.x 0 .q = {value} := by exact s.a_charge
"""
    raw = ctx + """: s.final.raw 0 0 = some {value} := by exact s.raw_active
"""
    again = ctx + """(p : Port) : s.final.x 0 (.z p) = b.final.x 0 (.z p) {extra} := by exact s.a_gains p
"""
    arecovery = ctx + """: s.final.x 0 .b = b.final.x 0 .b {extra} := by exact s.a_recovery
"""
    brecovery = ctx + """: s.final.x 1 .b = {value} := by exact s.b_recovery
"""
    bmark = ctx + """(p : Port) : s.execution.ledger.mark 1 p = {value} := by exact s.b_mark_zero p
"""
    bmain = ctx + """: s.final.main 1 = .{value} := by exact s.b_main_ready
"""
    outcome = ctx + """{{ε}} (hb : @PhysicalBox 2 (extendParameters θ fresh) ε)
    (hd : ∀ t, (3/10:ℝ)≤forward t ∧ forward t≤2/5) """
    bgain = outcome + """: s.final.x 1 (.z 1) = newborn.x (.z 1)+{value} := by exact s.b_gain_target hb hd
"""
    berror = outcome + """: s.execution.ledger.error 1 1 = {value} := by exact s.b_error_dose hb hd
"""
    baux = outcome + """(p : Port) : s.final.aux 1 p = .{value} := by exact (s.b_aux_rest hb hd p).1
"""
    braw = ctx + """(hd : ∀ t, (3/10:ℝ)≤forward t ∧ forward t≤2/5) (p : Port) :
    s.final.raw 1 p = {value} := by exact s.b_raw_none hd p
"""
    gain_bound = """example {{z : ℝ}}
    (hl : Real.log (6/5)+3/5-1/100000≤z) (hu : z≤Real.log (6/5)+3/5+1/100000) :
    Real.exp z ≤ {value} := by exact (fast_learned_gain_sharp_bounds hl hu).2
"""
    early = """example {{q g start t : ℝ}} (hq : q≤7/50) (hg : g≤11/5)
    (ht : start≤t) (hr : readyPulse q g start t=1) : start+{value}<t := by
  exact readyPulse_mid_root_after_four_tenths hq hg ht hr
"""
    return [
        ('the original birth family constructs the joint response to168', factory.format(count='16'), factory.format(count='15')),
        ('the actual common endpoint is168', date.format(value='168'), date.format(value='176')),
        ('saturation follows the real next A source delivery', complete.format(value='168'), complete.format(value='176')),
        ('exactly forty-six external future tokens remain', length.format(value='46'), length.format(value='47')),
        ('the actual A168 head is removed rather than retained', queue.format(start='176',count='14'), queue.format(start='168',count='15')),
        ('the extension delivers the real A168 source', deliveries.format(value='168'), deliveries.format(value='176')),
        ('B learning does not invent a first output', outputs.format(value='[]'), outputs.format(value='[(1,168)]')),
        ('A keeps its real reopen charge through the wait', charge.format(value='1/10'), charge.format(value='1/4')),
        ('the new A raw retains source168 rather than160', raw.format(value='168'), raw.format(value='160')),
        ('A does not inherit B learning', again.format(extra=''), again.format(extra='+3/5')),
        ('A does not acquire a new recovery dose', arecovery.format(extra=''), arecovery.format(extra='+1/10')),
        ('B learns relative to its own newborn gain', bgain.format(value='3/5'), bgain.format(value='0')),
        ('the actual interleaved prefix gives one B ERROR dose', berror.format(value='3/5'), berror.format(value='6/5')),
        ('B READY-main MARK contributes no recovery', bmark.format(value='0'), bmark.format(value='1/10')),
        ('B retains its own perturbed recovery', brecovery.format(value='newborn.x .b'), brecovery.format(value='9/50')),
        ('the real silent response leaves B main READY', bmain.format(value='ready'), bmain.format(value='fast')),
        ('B auxiliary phases actually return to READY by168', baux.format(value='ready'), baux.format(value='error')),
        ('B raw actually expires before168', braw.format(value='none'), braw.format(value='some r.final.time')),
        ('the own fast-port learned gain needs its true2.2 bound', gain_bound.format(value='11/5'), gain_bound.format(value='2')),
        ('the actual mid-gain firing is after four tenths', early.format(value='2/5'), early.format(value='1/2')),
    ]


def main():
    controls = cases()
    with tempfile.TemporaryDirectory(prefix='hybrid-first-interleaved-negative-', dir=ROOT) as tmp:
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

        check('\n'.join(good for _, good, _ in controls), True, 'valid first interleaved response controls')
        for name, _, bad in controls:
            check(bad, False, name)
            print(f'{name}: physical conclusion accepted; altered claim rejected.', flush=True)


if __name__ == '__main__':
    main()
