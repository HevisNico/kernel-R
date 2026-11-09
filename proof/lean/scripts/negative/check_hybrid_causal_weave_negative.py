#!/usr/bin/env python3
"""Paired contracts for actual causal feed-forward execution weaving."""
from pathlib import Path
import subprocess
import tempfile

from scripts.lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[2]
PREFIX = '''import KernelR.HybridCausalHeadSignals
open KernelR.Hybrid
noncomputable section
'''


def pair(label, source, good, bad):
    assert '@v@' in source and good != bad
    return label, source.replace('@v@', good), source.replace('@v@', bad)


def cases():
    tail = '''example {n θ route s u} (e : @Execution n θ route s u)
    (contacts : HeadRoutes n) '''
    balance = '''example {n θ route s u a Q contacts}
    {e : @Execution n θ route s u} (h : HeadQueueBalance e a Q contacts) '''
    flow = '''example {n θ s u} (f : @Flow n θ s u) (Q : List (Delivery n))
    (hp : ∀ d∈Q,u.time≤d.due) '''
    witness = '''example {n θ θH route s u a b Q contacts}
    {tail : @Execution n θ route s u} {head : @Execution 1 θH (fun _ _=>[]) a b}
    (w : CausalHeadWeave tail head Q contacts) '''
    factory = '''example {n θ θH route s u a b}
    (tail : @Execution n θ route s u) (head : @Execution 1 θH (fun _ _=>[]) a b)
    (hstart : s.time=a.time) (hfinish : u.time=b.time)
    (contacts : HeadRoutes n) (hc : StrictHeadRoutes contacts)
    (Q : List (Delivery (n+1))) (hb : HeadQueueBalance tail a Q contacts) :
    ∃ (Q' : List (Delivery (n+1)))
      (global : Execution (prependParameters θH θ) (prependRouted route contacts)
        (s.prependQueued a Q) (u.prependQueued b Q')),
      @v@ := by
  obtain ⟨Q',global,hQ,htrace⟩ := tail.prepend_causal head hstart hfinish contacts hc Q hb
  exact ⟨Q',global,htrace.emissions⟩
'''
    complete = '''example {n θ θH route s u a b T}
    (tail : @Execution n θ route s u) (head : @Execution 1 θH (fun _ _=>[]) a b)
    (hstart : s.time=a.time) (ht : CompleteThrough tail T) (hh : CompleteThrough head T)
    (contacts : HeadRoutes n) (hc : StrictHeadRoutes contacts)
    (Q : List (Delivery (n+1))) (hb : HeadQueueBalance tail a Q contacts) :
    ∃ (Q' : List (Delivery (n+1)))
      (global : Execution (prependParameters θH θ) (prependRouted route contacts)
        (s.prependQueued a Q) (u.prependQueued b Q')),
      CompleteThrough global @v@ := by
  obtain ⟨Q',global,hcomplete,hQ,htrace⟩ :=
    tail.prepend_causal_complete head hstart ht hh contacts hc Q hb
  exact ⟨Q',global,hcomplete⟩
'''
    return [
        pair('analysis receiver queue is derived from actual tail emissions', tail +
             ': e.headInputQueue contacts=@v@ := by rfl\n',
             'e.ledger.emissions.flatMap (fun ev=>contacts ev.1 ev.2)', '[]'),
        pair('unissued head wires retain the actual issuing clocks and routes', tail +
             ': e.futureHeadWires contacts=@v@ := by exact e.futureHeadWires_map contacts\n',
             '(e.headInputQueue contacts).map (Delivery.head (n:=n))', 's.pending.map Delivery.succ'),
        pair('unissued wires are strictly future of the current clock', tail +
             '''(hc : StrictHeadRoutes contacts) (d : Delivery (n+1))
    (hd : d∈e.futureHeadWires contacts) : @v@<d.due := by
  exact e.futureHeadWires_future contacts hc d hd
''', 's.time', 'u.time'),
        pair('operational queue plus ghost pool accounts for each local occurrence', balance +
             ''': (Q : Multiset (Delivery (n+1)))+(e.futureHeadWires contacts : Multiset (Delivery (n+1)))=
    (s.pending.map Delivery.succ : Multiset (Delivery (n+1)))+
    (a.pending.map (Delivery.head (n:=n)) : Multiset (Delivery (n+1)))@v@ := by exact h
''', '', '+(e.futureHeadWires contacts : Multiset (Delivery (n+1)))'),
        pair('a due local token is already present in the true operational queue', balance +
             '''(hc : StrictHeadRoutes contacts) (d : Delivery (n+1))
    (hd : d∈s.pending.map Delivery.succ ∨ d∈a.pending.map (Delivery.head (n:=n)))
    (ht : d.due=s.time) : d∈@v@ := by exact h.available_now hc hd ht
''', 'Q', '([] : List (Delivery (n+1)))'),
        pair('initial global queue contains external tokens while future wires stay ghost', tail +
             '''(a : Snapshot 1) (hq : a.pending=e.headInputQueue contacts) :
    HeadQueueBalance e a (@v@) contacts := by exact HeadQueueBalance.initial e a contacts hq
''', 's.pending.map Delivery.succ', 's.pending.map Delivery.succ++e.futureHeadWires contacts'),
        pair('requeue preserves the full actual flow ledger', flow +
             ': (f.requeue Q hp).ledger=@v@ := by rfl\n', 'f.ledger', 'Ledger.zero'),
        pair('requeue retains the actual energy endpoint', flow +
             '(i : Fin n) : (u.requeue Q).x i .energy=@v@ := by rfl\n', 'u.x i .energy', '100'),
        pair('new head has a closed outgoing contact in this feed-forward extension',
             '''example {n} (route : Router n) (contacts : HeadRoutes n) (t : ℝ) :
    prependRouted route contacts 0 t=@v@ := by rfl
''', '[]', '[⟨0,2,t+1⟩]'),
        pair('whole product constructs actual global FIREs without dropping head outputs', factory,
             '''(global.ledger.emissions : Multiset (Fin (n+1)×ℝ))=
        (tail.ledger.emissions.map (fun ev=>(ev.1.succ,ev.2)) : Multiset (Fin (n+1)×ℝ))+
        (head.ledger.emissions.map (fun ev=>((0:Fin (n+1)),ev.2)) : Multiset (Fin (n+1)×ℝ))''',
             '''(global.ledger.emissions : Multiset (Fin (n+1)×ℝ))=
        (tail.ledger.emissions.map (fun ev=>(ev.1.succ,ev.2)) : Multiset (Fin (n+1)×ℝ))'''),
        pair('whole product keeps the exact local terminal token occurrence balance', witness +
             ''': (w.pending : Multiset (Delivery (n+1)))=@v@ := by exact w.terminal
''', '(u.pending.map Delivery.succ : Multiset (Delivery (n+1)))+(b.pending.map (Delivery.head (n:=n)) : Multiset (Delivery (n+1)))', '0'),
        pair('whole product retains every actual source and wire delivery', witness +
             ''': (w.execution.deliveries : Multiset (Delivery (n+1)))=
    (tail.deliveries.map Delivery.succ : Multiset (Delivery (n+1)))+
    (@v@ : Multiset (Delivery (n+1))) := by exact w.trace.deliveries
''', 'head.deliveries.map (Delivery.head (n:=n))', '[]'),
        pair('global completion holds at the actual shared finite horizon', complete, 'T', 'T+1'),
        pair('local empty terminal queues imply a genuinely empty global terminal queue', witness +
             '''(ht : u.pending=[]) (hh : b.pending=[]) : w.pending=@v@ := by exact w.pending_empty ht hh
''', '[]', 'Q'),
        pair('head emitted stream is retained in its genuine chronological order', witness +
             ': w.execution.emissionTimes 0=@v@ := by exact w.head_emission_times\n',
             'head.emissionTimes 0', '[]'),
        pair('every existing tail cell retains its actual chronological emitted stream', witness +
             '(i : Fin n) : w.execution.emissionTimes i.succ=@v@ := by exact w.tail_emission_times i\n',
             'tail.emissionTimes i', '[]'),
        pair('global FIRE count has no additional synthetic output', witness +
             ''': w.execution.ledger.emissions.length=
    tail.ledger.emissions.length+head.ledger.emissions.length@v@ := by exact w.trace.total_emission_count
''', '', '+1'),
        pair('global delivery count includes both actual local programs', witness +
             ''': w.execution.deliveries.length=tail.deliveries.length+@v@ := by exact w.trace.total_delivery_count
''', 'head.deliveries.length', '0'),
    ]


def main():
    controls = cases()
    with tempfile.TemporaryDirectory(prefix='hybrid-causal-weave-', dir=ROOT) as tmp:
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

        check('\n'.join(good for _, good, _ in controls), True, 'valid causal-weave contracts')
        print(f'All{len(controls)} positive causal-weave contracts accepted.', flush=True)
        for name, _, bad in controls:
            check(bad, False, name)
            print(f'{name}: physical conclusion accepted; altered claim rejected.', flush=True)
        print(f'{len(controls)} paired causal-weave controls passed.', flush=True)


if __name__ == '__main__':
    main()
