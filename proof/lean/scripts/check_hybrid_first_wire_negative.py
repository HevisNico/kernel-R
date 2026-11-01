#!/usr/bin/env python3
"""Guard the actual issued wire, first B delivery and joint execution products."""
from pathlib import Path
import subprocess
import tempfile

from lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[1]
PREFIX = 'import KernelR.HybridFirstWiredArrival\nimport KernelR.HybridNeutralExecutionProduct\nopen KernelR.Hybrid\n'


def cases():
    factory = """example {{θ fresh ε born}} (hs : @BirthState 1 born)
    (hb : @PhysicalBox 2 (extendParameters θ fresh) ε)
    (ha : ∀ p, born.aux 0 p = .ready)
    (hq : born.pending = sourceTrain 0 0 0 8 {count} ++ sourceTrain 0 0 160 8 16)
    (newborn : Newborn) (forward backward : ℝ → ℝ)
    (hd : ∀ t, (3/10:ℝ)≤forward t ∧ forward t≤2/5) :
    ∃ c : ConstructedBirthPreparation θ born,
      ∃ b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources,
        ∃ r : FirstWiredArrival b, CompleteThrough r.staged.after r.final.time ∧ r.final.pending.length=47 := by
  exact birth_protocol_first_wired_arrival_exists hs hb ha hq newborn forward backward hd
"""
    ctx = """example {{θ born fresh newborn forward backward}}
    {{c : ConstructedBirthPreparation θ born}}
    {{b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}}
    (r : FirstWiredArrival b) """
    complete = ctx + """: CompleteThrough r.{value} r.final.time := by exact r.staged_complete
"""
    deliveries = ctx + """: r.execution.deliveries = [⟨1,{port},r.final.time⟩] := by exact r.deliveries
"""
    outputs = ctx + """: r.execution.ledger.emissions = [⟨{cell},r.fire.final.time⟩] := by exact r.emissions
"""
    token = ctx + """: r.fire.final.pending = constructedBBirthQueue ++ [⟨1,{port},r.fire.final.time+forward r.fire.final.time⟩] := by
  exact r.fire.protocol_pending
"""
    queue = ctx + """: r.final.pending.length = {value} := by exact r.pending_length
"""
    issued = ctx + """: r.fire.final.pending.length = {value} := by
  rw [r.fire.protocol_pending]
  norm_num [constructedBBirthQueue,constructedBBirthSources,sourceTrain]
"""
    date = ctx + """: r.final.time = r.fire.final.time+{value} := by exact r.date
"""
    raw = ctx + """: r.final.raw 1 1 = some {value} := by exact r.raw_receiver
"""
    gain = ctx + """(p : Port) : r.final.x 1 (.z p) = {value} := by exact r.receiver_gain p
"""
    recovery = ctx + """: r.final.x 1 .b = {value} := by exact r.receiver_recovery
"""
    q = ctx + """: r.final.x 1 .q ≤ {value} := by exact r.receiver_charge.2
"""
    bounds = ctx + """(hd : ∀ t, (3/10:ℝ)≤forward t ∧ forward t≤2/5) :
    (160+7/10:ℝ)<r.final.time ∧ r.final.time<160+{value} := by exact r.date_bounds hd
"""
    sender_raw = ctx + """: r.fire.final.raw 0 0 = some {value} := by exact r.fire.raw_active
"""
    fire = ctx + """: r.fire.execution.ledger.emissions = [⟨0,{value}⟩] := by exact r.fire.emissions
"""
    before = ctx + """: r.fire.before.pending = {value} := by
  rw [r.fire.product_before]
  rfl
"""
    receiver = ctx + """: r.final.main 1 = .{value} := by exact r.receipt.receiver_ready.ready
"""
    neutral = """example {{θA θB : Fin 1 → Parameters}} {{sA uA sB uB : Snapshot 1}}
    (eA : Execution θA (fun _ _=>[]) sA uA) (eB : Execution θB (fun _ _=>[]) sB uB)
    (hs : sA.time=sB.time) (hu : uA.time=uB.time)
    (heA : eA.ledger.emissions=[]) (hdA : eA.deliveries=[])
    (heB : eB.ledger.emissions=[]) (hdB : eB.deliveries=[])
    (Q : List (Delivery 2)) (hq : ∀d∈Q,uA.time≤d.due) (route : Router 2) :
    ∃ e : Execution (extendParameters θA (θB 0)) route (sA.product sB Q) (uA.product {value} Q),
      e.ledger.emissions=[] ∧ e.deliveries=[] := by
  exact eA.product_neutral eB hs hu heA hdA heB hdB Q hq route
"""
    cut = """example {{n θ route s u H}} {{e : @Execution n θ route s u}}
    (r : e.BeforeFlowCut H) : {value} := by
  linarith [r.flow.positive,r.date]
"""
    other_raw = ctx + """(p : Port) (hp : p≠1) : r.final.raw 1 p = {value} := by
  exact r.receipt.raw_other p hp
"""
    return [
        ('the original birth family constructs its first real wire delivery', factory.format(count='16'), factory.format(count='15')),
        ('the staged endpoint is saturated after the actual receipt', complete.format(value='staged.after'), complete.format(value='fire.execution')),
        ('the actual received wire targets B port1', deliveries.format(port='1'), deliveries.format(port='2')),
        ('only A fires in the constructed post-birth prefix', outputs.format(cell='0'), outputs.format(cell='1')),
        ('the real FIRE issues the actual port1 contact token', token.format(port='1'), token.format(port='0')),
        ('consuming the wire preserves all forty-seven external tokens', queue.format(value='47'), queue.format(value='48')),
        ('FIRE first adds one token to the real global queue', issued.format(value='48'), issued.format(value='47')),
        ('receipt uses the delay at the actual firing date', date.format(value='forward r.fire.final.time'), date.format(value='7/20')),
        ('the received raw starts at receipt rather than emission', raw.format(value='r.final.time'), raw.format(value='r.fire.final.time')),
        ('B keeps its own newborn gains through the quiet prefix', gain.format(value='newborn.x (.z p)'), gain.format(value='born.x 0 (.z p)+9/5')),
        ('B keeps its own perturbed recovery', recovery.format(value='newborn.x .b'), recovery.format(value='2/25')),
        ('the actual newborn charge band survives waiting', q.format(value='1/10+1/100000'), q.format(value='1/10')),
        ('the wired date includes both real response and wire delay', bounds.format(value='13/10'), bounds.format(value='9/10')),
        ('the sender raw retains source160 at its FIRE', sender_raw.format(value='160'), sender_raw.format(value='r.fire.final.time')),
        ('the actual FIRE emission has its own guard date', fire.format(value='r.fire.final.time'), fire.format(value='160')),
        ('the pre-FIRE global queue contains no wired token', before.format(value='constructedBBirthQueue'), before.format(value='constructedBBirthQueue++[⟨1,1,r.final.time⟩]')),
        ('the receiver remains READY until the actual arrival', receiver.format(value='ready'), receiver.format(value='fast')),
        ('active neutral products retain both actual endpoint states', neutral.format(value='uB'), neutral.format(value='sB')),
        ('a saturated cut retains its next positive physical flow', cut.format(value='H<r.nextState.time'), cut.format(value='r.nextState.time<H')),
        ('receipt creates raw only on its actual receiver port', other_raw.format(value='none'), other_raw.format(value='some r.final.time')),
    ]


def main():
    controls = cases()
    with tempfile.TemporaryDirectory(prefix='hybrid-first-wire-negative-', dir=ROOT) as tmp:
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

        check('\n'.join(good for _, good, _ in controls), True, 'valid first-wire controls')
        for name, _, bad in controls:
            check(bad, False, name)
            print(f'{name}: physical conclusion accepted; altered claim rejected.', flush=True)


if __name__ == '__main__':
    main()
