#!/usr/bin/env python3
"""Guard real B birth, retained queues and independent two-cell transport."""
from pathlib import Path
import subprocess
import tempfile

from lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[1]
PREFIX = 'import KernelR.HybridConstructedBBirth\nimport KernelR.HybridTwoCellJumpProduct\nopen KernelR.Hybrid\n'


def cases():
    factory = """example {{θ fresh ε born}} (hs : @BirthState 1 born)
    (hb : @PhysicalBox 2 (extendParameters θ fresh) ε)
    (ha : ∀ p, born.aux 0 p = .ready)
    (hq : born.pending = sourceTrain 0 0 0 8 {count} ++ sourceTrain 0 0 160 8 16)
    (newborn : Newborn) (forward backward : ℝ → ℝ) :
    ∃ c : ConstructedBirthPreparation θ born,
      ∃ b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources,
        CompleteThrough b.staged.after 160 ∧ b.final.pending.length = 47 := by
  exact birth_protocol_b_birth_complete_exists hs hb ha hq newborn forward backward
"""
    ctx = """example {{θ born}} {{c : ConstructedBirthPreparation θ born}}
    {{fresh newborn route}} (b : ConstructedBBirth c fresh newborn route constructedBBirthSources) """
    before = ctx + """: b.beforeBirth.time = {value} := by exact b.before_date
"""
    after = ctx + """: b.afterBirth.time = {value} := by exact b.after_date
"""
    complete = ctx + """: CompleteThrough b.staged.after {value} := by exact b.protocol_complete
"""
    queue = ctx + """: b.final.pending = sourceTrain 0 0 {start} 8 {count} ++ constructedBBirthSources := by exact b.pending
"""
    length = ctx + """: b.final.pending.length = {value} := by exact b.protocol_pending_length
"""
    sources = ctx + """: b.birth.sources = sourceTrain 1 {port} 320 8 16 ++ sourceTrain 1 2 480 8 {count} := by
  exact b.source_list
"""
    raw = ctx + """: b.final.raw 0 0 = some {value} := by exact b.raw_active
"""
    braw = ctx + """(p : Port) : b.final.raw 1 p = {value} := by
  exact b.raw_other 1 p (Or.inl (by decide))
"""
    aq = ctx + """: b.final.x 0 .q = {value} := by exact b.a_charge
"""
    gain = ctx + """(p : Port) : b.final.x 0 (.z p) = c.final.x 0 (.z p) {extra} := by exact b.a_gain_preserved p
"""
    recovery = ctx + """: b.final.x 0 .b = c.final.x 0 .b {extra} := by exact b.a_recovery
"""
    bq = ctx + """: b.final.x 1 .q = {value} := by exact congrFun b.b_coordinates .q
"""
    bz = ctx + """(p : Port) : b.final.x 1 (.z p) = {value} := by exact congrFun b.b_coordinates (.z p)
"""
    delivered = ctx + """: b.arrival.deliveries = [⟨0,0,{value}⟩] := by exact b.arrival_deliveries
"""
    bcount = """example : constructedBBirthSources.length = {value} := by
  norm_num [constructedBBirthSources,sourceTrain]
"""
    value = """example (xA xB : Values 1) : xA.product xB 1 = {value} := by rfl
"""
    product_queue = """example (sA sB : Snapshot 1) (Q : List (Delivery 2)) :
    (sA.product sB Q).pending = {value} := by rfl
"""
    field = """example (θA θB : Fin 1 → Parameters) (sA sB : Snapshot 1)
    (Q : List (Delivery 2)) (xA xB : Values 1) (t : ℝ) :
    field (extendParameters θA (θB 0)) (sA.product sB Q) (xA.product xB) t 0 .energy =
      field {params} {state} {values} t 0 .energy := by
  exact product_field_zero θA θB sA sB Q xA xB t .energy
"""
    guard = """example (sA sB : Snapshot 1) (Q : List (Delivery 2)) (p q : Port) :
    ((setRaw sA 0 p none).product sB Q).raw 1 q = {value} := by rfl
"""
    return [
        ('the original birth factory constructs the real B boundary', factory.format(count='16'), factory.format(count='15')),
        ('the actual pre-birth waiting flow reaches 160', before.format(value='160'), before.format(value='128')),
        ('the genuine birth preserves its boundary clock', after.format(value='160'), after.format(value='168')),
        ('saturation is proved after consuming the boundary input', complete.format(value='160'), complete.format(value='168')),
        ('A160 is consumed while later A sources remain', queue.format(start='168',count='15'), queue.format(start='160',count='16')),
        ('all forty-seven external future tokens remain', length.format(value='47'), length.format(value='31')),
        ('B sources use their own port2 and retain both trains', sources.format(port='2',count='16'), sources.format(port='0',count='16')),
        ('A raw has its actual source160 origin', raw.format(value='160'), raw.format(value='128')),
        ('the fresh newborn has no copied raw input', braw.format(value='none'), braw.format(value='some 160')),
        ('A retains its exact prepared charge across birth', aq.format(value='1/10'), aq.format(value='1/4')),
        ('A retains its own gains across birth', gain.format(extra=''), gain.format(extra='+3/5')),
        ('A receives no fictitious recovery dose at birth', recovery.format(extra=''), recovery.format(extra='+1/10')),
        ('B charge comes from its own perturbed newborn data', bq.format(value='newborn.x .q'), bq.format(value='1/10')),
        ('B gains come from its own newborn rather than A', bz.format(value='newborn.x (.z p)'), bz.format(value='c.final.x 0 (.z p)')),
        ('the post-birth move is the real A160 delivery', delivered.format(value='160'), delivered.format(value='168')),
        ('both sixteen-source B trains are retained', bcount.format(value='32'), bcount.format(value='16')),
        ('product cell one retains its own coordinates', value.format(value='xB 0'), value.format(value='xA 0')),
        ('the flow product uses only its explicit global queue', product_queue.format(value='Q'), product_queue.format(value='[]')),
        ('the full energy field remains local to the correct cell', field.format(params='θA',state='sA',values='xA'), field.format(params='θB',state='sB',values='xB')),
        ('an A raw-expiry update leaves the B raw unchanged', guard.format(value='sB.raw 0 q'), guard.format(value='none')),
    ]


def main():
    controls = cases()
    with tempfile.TemporaryDirectory(prefix='hybrid-b-birth-product-negative-', dir=ROOT) as tmp:
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

        check('\n'.join(good for _, good, _ in controls), True, 'valid B-birth and flow-product controls')
        for name, _, bad in controls:
            check(bad, False, name)
            print(f'{name}: physical conclusion accepted; altered claim rejected.', flush=True)


if __name__ == '__main__':
    main()
