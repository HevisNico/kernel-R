#!/usr/bin/env python3
"""Paired actual-event router congruence and fixed teaching/cadence closure."""
from pathlib import Path
import subprocess
import tempfile

from lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[1]
PREFIX = '''import KernelR.HybridTeachingCadenceRouter
open KernelR.Hybrid
noncomputable section
'''


def pair(label, template, good, bad):
    assert '@v@' in template
    assert good != bad
    return label, template.replace('@v@', good), template.replace('@v@', bad)


def cases():
    trace = '''example {n θ route s u} (e : @Execution n θ route s u) (newRoute : Router n)
    (hMatches : ∀ event∈e.ledger.emissions,route event.1 event.2=newRoute event.1 event.2) '''
    teaching = '''example {θ s u} (oldDelay cf cb : ℝ → ℝ)
    (e : @Execution 3 θ (cTeachingRouter oldDelay) s u) (hEnd : u.time<640) '''
    cadence = '''example {θ s u} (oldDelay cf cb : ℝ → ℝ)
    (e : @Execution 3 θ (cadenceRouter cf cb) s u) (hStart : 630≤s.time) '''
    joined = '''example {θ s v u T} (oldDelay cf cb : ℝ → ℝ)
    (old : @Execution 3 θ (cTeachingRouter oldDelay) s v)
    (next : Execution θ (cadenceRouter cf cb) v u)
    (hOld : v.time<640) (hNew : 630≤v.time) (hc : CompleteThrough next T) '''
    return [
        pair('router transport retains the complete ledger including issued counts and doses', trace +
             ''': ∃ lifted : Execution θ newRoute s u,lifted.ledger=@v@ := by
  obtain ⟨lifted,hL,hD⟩ := e.retarget_router newRoute hMatches
  exact ⟨lifted,hL⟩
''', 'e.ledger', 'Ledger.zero'),
        pair('router transport retains every actual delivery occurrence in order', trace +
             ''': ∃ lifted : Execution θ newRoute s u,lifted.deliveries=@v@ := by
  obtain ⟨lifted,hL,hD⟩ := e.retarget_router newRoute hMatches
  exact ⟨lifted,hD⟩
''', 'e.deliveries', '[]'),
        pair('completion is retained at the actual final clock', trace +
             '''{T} (hc : CompleteThrough e T) :
    ∃ lifted : Execution θ newRoute s u, CompleteThrough lifted @v@ := by
  obtain ⟨lifted,hL,hD,hC⟩ := e.retarget_router_complete newRoute hMatches hc
  exact ⟨lifted,hC⟩
''', 'T', 'T+1'),
        pair('a real FIRE must match routing at its actual clock rather than a later date',
             '''example {n} (route newRoute : Router n) (s : Snapshot n) (i : Fin n)
    (hm : s.main i=.ready) (hq : s.x i .q=1)
    (hr : route i (@v@)=newRoute i (@v@)) :
    ∃ lifted : Jump newRoute s {setMain s i .fast with pending:=s.pending++route i s.time},
      lifted.ledger=(Jump.fire s i hm hq (route:=route)).ledger := by
  let j : Jump route s {setMain s i .fast with pending:=s.pending++route i s.time} := .fire s i hm hq
  obtain ⟨lifted,hL,hD⟩ := j.retarget_router newRoute (by
    intro event he
    have heq : event=(i,s.time) := by simpa only [j,Jump.ledger,List.mem_singleton] using he
    subst event
    exact hr)
  exact ⟨lifted,hL⟩
''', 's.time', 's.time+1'),
        pair('the old teaching gate is already closed at630',
             '''example (delay : ℝ → ℝ) (i : Fin 3) {t : ℝ} (ht : @v@≤t) :
    cTeachingRouter delay i t=[] := by exact cTeachingRouter.after_close delay i ht
''', '630', '629'),
        pair('the cadence gate stays closed strictly before640',
             '''example (cf cb : ℝ → ℝ) (i : Fin 3) {t : ℝ} (ht : t<@v@) :
    cadenceRouter cf cb i t=[] := by exact cadenceRouter.before_open cf cb i ht
''', '640', '641'),
        pair('the fixed union has no preissued wire at the639.9 handoff',
             '''example (delay cf cb : ℝ → ℝ) (i : Fin 3) :
    teachingCadenceRouter delay cf cb i (6399/10)=@v@ := by
  rw [teachingCadenceRouter,cTeachingRouter.after_close delay i (by norm_num),
    cadenceRouter.before_open cf cb i (by norm_num)]
  rfl
''', '[]', '[⟨0,2,640⟩]'),
        pair('teaching is retained under the fixed combined router', teaching +
             ''': ∃ lifted : Execution θ (teachingCadenceRouter oldDelay cf cb) s u,
      lifted.ledger=@v@ := by
  obtain ⟨lifted,hL,hD⟩ := e.teaching_to_combined oldDelay cf cb hEnd
  exact ⟨lifted,hL⟩
''', 'e.ledger', 'Ledger.zero'),
        pair('cadence keeps all true deliveries under the same combined router', cadence +
             ''': ∃ lifted : Execution θ (teachingCadenceRouter oldDelay cf cb) s u,
      lifted.deliveries=@v@ := by
  obtain ⟨lifted,hL,hD⟩ := e.cadence_to_combined oldDelay cf cb hStart
  exact ⟨lifted,hD⟩
''', 'e.deliveries', '[]'),
        pair('the fixed-router concatenation preserves both full physical ledgers', joined +
             ''': ∃ e : Execution θ (teachingCadenceRouter oldDelay cf cb) s u,
      e.ledger=@v@ := by
  obtain ⟨e,hL,hD,hC⟩ := teaching_cadence_append_exists oldDelay cf cb old next hOld hNew hc
  exact ⟨e,hL⟩
''', 'old.ledger.add next.ledger', 'next.ledger'),
        pair('the fixed-router concatenation retains original delivery order', joined +
             ''': ∃ e : Execution θ (teachingCadenceRouter oldDelay cf cb) s u,
      e.deliveries=@v@ := by
  obtain ⟨e,hL,hD,hC⟩ := teaching_cadence_append_exists oldDelay cf cb old next hOld hNew hc
  exact ⟨e,hD⟩
''', 'old.deliveries++next.deliveries', 'next.deliveries++old.deliveries'),
        pair('the fixed-router concatenation remains complete at its real final horizon', joined +
             ''': ∃ e : Execution θ (teachingCadenceRouter oldDelay cf cb) s u,
      CompleteThrough e @v@ := by
  obtain ⟨e,hL,hD,hC⟩ := teaching_cadence_append_exists oldDelay cf cb old next hOld hNew hc
  exact ⟨e,hC⟩
''', 'T', 'T+1'),
    ]


def main():
    controls = cases()
    with tempfile.TemporaryDirectory(prefix='hybrid-router-transport-', dir=ROOT) as tmp:
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

        check('\n'.join(good for _, good, _ in controls), True, 'valid router-transport contracts')
        print(f'All {len(controls)} positive router-transport contracts accepted.', flush=True)
        for name, _, bad in controls:
            check(bad, False, name)
            print(f'{name}: valid conclusion accepted; altered claim rejected.', flush=True)
        print(f'{len(controls)} paired router-transport controls passed.', flush=True)


if __name__ == '__main__':
    main()
