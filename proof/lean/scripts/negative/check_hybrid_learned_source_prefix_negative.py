#!/usr/bin/env python3
"""Paired controls for real learned next sources and nonuniform same-own-root prefixes."""
from pathlib import Path
import subprocess
import tempfile

from scripts.lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[2]
PREFIX = '''import KernelR.HybridLearnedSourcePrefix
open KernelR.Hybrid
noncomputable section
'''


def pair(label, template, good, bad):
    assert '@v@' in template
    assert good != bad
    return label, template.replace('@v@', good), template.replace('@v@', bad)


def cases():
    short = """example {θ s p H later} (r : ShortLearnedNextSource θ s p H later) """
    first = """example {θ s p H later} (r : PreparedFirstSource θ s p H later) """
    pref = """example {θ s p times later} (r : LearnedSourcePrefix θ s p times later) """
    short_factory = """example {θ ε} (hb : PhysicalBox θ ε) (s : Snapshot 1) (p : Port)
    (later : List (Delivery 1)) (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (hs : PreparedSection s 0)
    (hg : 9/5≤Real.exp (s.x 0 (.z p)) ∧ Real.exp (s.x 0 (.z p))≤11/5)
    (hr : s.raw 0 p=some s.time) (ho : ∀ q,q≠p → s.raw 0 q=none)
    (hqueue : s.pending=⟨0,p,s.time+7⟩::later)
    (hLater : ∀ d∈later,s.time+7<d.due) :
    ∃ r : ShortLearnedNextSource θ s p (s.time+7) later,
      (r.execution.emissionTimes 0).length=@v@ := by
  obtain ⟨r⟩ := short_learned_next_source_exists hb s p (s.time+7) later
    hf hv hs hg hr ho hqueue (by linarith) hLater
  exact ⟨r,r.emission_count⟩
"""
    prefix_factory = """example {θ ε} (hb : PhysicalBox θ ε) (s : Snapshot 1) (p : Port)
    (later : List (Delivery 1)) (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (hs : PreparedSection s 0) (hq : s.x 0 .q=1/10)
    (hg : 9/5≤Real.exp (s.x 0 (.z p)) ∧ Real.exp (s.x 0 (.z p))≤11/5)
    (hr : s.raw 0 p=some s.time) (ho : ∀ q,q≠p → s.raw 0 q=none)
    (hqueue : s.pending=[⟨0,p,s.time+7⟩,⟨0,p,s.time+29/2⟩]++later)
    (hLater : ∀ d∈later,s.time+29/2<d.due) :
    ∃ r : LearnedSourcePrefix θ s p [s.time+7,s.time+29/2] later,
      r.execution.emissionTimes 0=
        [s.time+restLatency (Real.exp (s.x 0 (.z p))),
          (s.time+@v@)+restLatency (Real.exp (s.x 0 (.z p)))] := by
  obtain ⟨r⟩ := learned_source_prefix_exists hb s p [s.time+7,s.time+29/2] later
    hf hv hs hq hg hr ho hqueue
    (by
      constructor
      · linarith
      · constructor
        · linarith
        · trivial) hLater
  refine ⟨r,?_⟩
  simpa only [learnedPrefixResponses,List.map_cons,List.map_nil] using r.calendar
"""
    first_factory = """example {θ ε} (hb : PhysicalBox θ ε) (s : Snapshot 1) (p : Port)
    (H : ℝ) (later : List (Delivery 1)) (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (hs : PreparedSection s 0) (hq : s.x 0 .q=1/10) (hr : ∀ q,s.raw 0 q=none)
    (hqueue : s.pending=⟨0,p,H⟩::later) (hgap : s.time<H)
    (hLater : ∀ d∈later,H<d.due) :
    ∃ r : PreparedFirstSource θ s p H later,r.final.raw 0 p=some @v@ := by
  obtain ⟨r⟩ := prepared_first_source_exists hb s p H later hf hv hs hq hr hqueue hgap hLater
  exact ⟨r,r.raw_active⟩
"""
    return [
        pair('a genuine learned cycle serves a next input after7.0 without any7.75 premise',
             short_factory, '1', '0'),
        pair('two nonuniform dates retain the same own realized resting latency',
             prefix_factory, '7', '8'),
        pair('a quiet prepared source consumes its first token at the actual H',
             first_factory, 'H', 's.time'),
        pair('the short-cycle next arrival is at its actual date H', short+
             ': r.final.time=@v@ := by exact r.date\n', 'H', 's.time+8'),
        pair('the new input begins at the genuine resting charge', short+
             ': r.final.x 0 .q=@v@ := by exact r.charge\n', '1/10', '1/4'),
        pair('quiet continuation keeps the real returned energy rather than resetting it', short+
             ': r.final.x 0 .energy=@v@ := by exact congrFun (congrFun r.values 0) .energy\n',
             '(quietAt r.cycle.returned.final H).x 0 .energy', '100'),
        pair('framing carries the complete actual cycle ledger including FIRE', short+
             ': r.framed.ledger=@v@ := by exact r.framed_ledger\n', 'r.offline.ledger', 'Ledger.zero'),
        pair('exactly the constructed FIRE remains in the emission ledger', short+
             ': r.execution.ledger.emissions=@v@ := by exact r.emissions\n', '[(0,r.cycle.fire.final.time)]', '[]'),
        pair('the consumed queue head is removed and every later occurrence is retained', short+
             ': r.final.pending=@v@ := by exact r.pending\n', 'later', 's.pending'),
        pair('the short response preserves each own acquired gain', short+
             '(q : Port) : r.final.x 0 (.z q)=s.x 0 (.z q)@v@ := by exact r.gains 0 q\n', '', '+3/5'),
        pair('the short response preserves its own recovery', short+
             ': r.final.x 0 .b=s.x 0 .b@v@ := by exact r.recovery 0\n', '', '+1/10'),
        pair('complete saturation is at H with its real endpoint events consumed', short+
             ': CompleteThrough r.execution @v@ := by exact r.complete\n', 'H', 'H+1'),
        pair('the first-source quiet span creates no fictitious pulse', first+
             ': r.execution.ledger.emissions=@v@ := by exact r.emissions\n', '[]', '[(0,H)]'),
        pair('the first-source delivery is its actual queued occurrence at H', first+
             ': r.execution.deliveries=[⟨0,p,@v@⟩] := by exact r.deliveries\n', 'H', 's.time'),
        pair('the first-source energy follows the original quiet physical solution', first+
             ': r.final.x 0 .energy=@v@ := by exact congrFun (congrFun r.values 0) .energy\n',
             '(quietAt s H).x 0 .energy', '100'),
        pair('the learned prefix preserves its exact arbitrary later queue', pref+
             ': r.final.pending=@v@ := by exact r.pending\n', 'later', 's.pending'),
        pair('nonuniform prefix terminal time is the last actual source rather than a forced period', pref+
             ': r.final.time=@v@ := by exact r.date\n', 'learnedPrefixEnd s.time times', 's.time+8*(times.length:ℝ)'),
        pair('the output calendar is translated by the same own resting root', pref+
             ': r.execution.emissionTimes 0=(learnedPrefixResponses s.time times).map (fun T=>T+@v@) := by exact r.calendar\n',
             'restLatency (Real.exp (s.x 0 (.z p)))', '2/5'),
        pair('every supplied next date corresponds to exactly one preceding learned response', pref+
             ': (r.execution.emissionTimes 0).length=times.length@v@ := by exact r.emission_count\n', '', '+1'),
        pair('the prefix consumes the supplied nonuniform source dates without retiming', pref+
             ': r.execution.deliveries=@v@ := by exact r.deliveries\n',
             'times.map (fun T=>⟨0,p,T⟩)', 'sourceTrain 0 p (s.time+8) 8 times.length'),
        pair('the full prefix retains each own gain without reinitializing it', pref+
             '(q : Port) : r.final.x 0 (.z q)=s.x 0 (.z q)@v@ := by exact r.gains q\n', '', '+3/5'),
        pair('the final RAW origin is the actual last input clock', pref+
             ': r.final.raw 0 p=some @v@ := by exact r.raw_active\n', 'r.final.time', 's.time'),
    ]


def main():
    controls = cases()
    with tempfile.TemporaryDirectory(prefix='hybrid-learned-source-prefix-', dir=ROOT) as tmp:
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

        check('\n'.join(good for _, good, _ in controls), True, 'valid learned-source-prefix controls')
        print(f'All {len(controls)} positive learned-source-prefix contracts accepted.', flush=True)
        for name, _, bad in controls:
            check(bad, False, name)
            print(f'{name}: valid conclusion accepted; altered claim rejected.', flush=True)
        print(f'{len(controls)} paired learned-source-prefix controls passed.', flush=True)


if __name__ == '__main__':
    main()
