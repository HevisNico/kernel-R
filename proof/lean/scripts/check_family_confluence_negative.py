#!/usr/bin/env python3
"""Paired semantic controls for the parametric native jump layer.

Every public theorem in the four confluence modules has its own accepted
application and rejected mutation. Additional concrete fixtures check guard
dependence, queue multiplicity and the distinction between local diamonds and
immediate equality. Rejection alone is not proof that a proposition is false.
"""
import argparse
import json
from pathlib import Path
import re
from family_control_batches import run_batches

ROOT = Path(__file__).resolve().parents[1]
MODULES = ["RawJumpConfluence", "JumpConfluence", "JumpDepartures", "JumpLocalDiamond"]
PREFIX = """import KernelR.Family.JumpLocalDiamond
namespace KernelR.Family
open KernelR.Hybrid
noncomputable section

def controlRoute : Router 1 := fun _ _ => []
def controlState (main : MainMode) (aux : AuxMode) (q m : ℝ) : Snapshot 1 where
  time := 0
  x := fun _ k => match k with
    | .q => q
    | .m _ => m
    | _ => 0
  main := fun _ => main
  aux := fun _ _ => aux
  raw := fun _ _ => none
  pending := []
def controlToken (p : Port) (t : ℝ) : Delivery 1 := ⟨0, p, t⟩
def controlContact : Snapshot 1 := controlState .ready .ready 1 1
def controlFire : Snapshot 1 := setMain controlContact 0 .fast
def controlMark : Snapshot 1 := setAux controlContact 0 0 .mark

theorem control_not_immediate : ¬ controlFire.ObservationalEq controlMark := by
  intro h
  have hm := congrFun h.main 0
  simp [controlFire, controlMark, controlContact, controlState, setMain, setAux] at hm

theorem control_fire : Nonempty (Jump nominal controlRoute controlContact controlFire) :=
  ⟨Jump.fire _ 0 rfl rfl⟩
theorem control_mark : Nonempty (Jump nominal controlRoute controlContact controlMark) :=
  ⟨Jump.mark _ 0 0 rfl rfl⟩
"""
SUFFIX = "\nend\nend KernelR.Family\n"


def pair(label, template, good, bad, counterexample=""):
    assert "@v@" in template and good != bad
    return label, template.replace("@v@", good) + counterexample, template.replace("@v@", bad)


def no_jump_counterexample(config, main, aux, q, m, extra=""):
    return f"""
def controlCfg : Constants := {config}
def controlBlocked : Snapshot 1 := {extra or f'controlState .{main} .{aux} ({q}) ({m})'}
example : ∀ u, IsEmpty (Jump controlCfg controlRoute controlBlocked u) := by
  intro u
  constructor
  intro j
  cases j <;> norm_num [controlCfg, controlBlocked, controlState, nominal,
    controlRoute, controlToken, setMain, setAux, setRaw] at *
"""


def cases():
    out = []
    events = [
        ("fire_guard", "fire", "ready", "q", "threshold", "1", "2"),
        ("fast_exit_guard", "fastEnd", "fast", "q", "fastExit", "1/4", "1/3"),
        ("reopen_guard", "reopen", "slow", "q", "rest", "1/10", "1/8"),
        ("mark_guard", "mark", "ready", "m", "auxThreshold", "1", "2"),
        ("silent_guard", "silent", "mark", "m", "markExit", "4/5", "3/4"),
        ("error_guard", "error", "silent", "m", "errorLevel", "1/10", "1/8"),
        ("aux_ready_guard", "auxReady", "error", "m", "auxRest", "1/40", "1/50"),
    ]
    for label, constructor, mode, coord, field, old, changed in events:
        if coord == "q":
            template = f"""example {{n c route s}} (i : Fin n)
    (hm : s.main i = .{mode}) (hg : s.x i .q = @v@) :
    ∃ u, Nonempty (@Jump n c route s u) := by
  exact ⟨_, ⟨Jump.{constructor} _ i hm hg⟩⟩
"""
            witness = no_jump_counterexample(
                f"{{ nominal with {field} := {changed} }}", mode, "ready", old, "0")
        else:
            template = f"""example {{n c route s}} (i : Fin n) (p : Port)
    (hm : s.aux i p = .{mode}) (hg : s.x i (.m p) = @v@) :
    ∃ u, Nonempty (@Jump n c route s u) := by
  exact ⟨_, ⟨Jump.{constructor} _ i p hm hg⟩⟩
"""
            witness = no_jump_counterexample(
                f"{{ nominal with {field} := {changed} }}", "ready", mode, "0", old)
        out.append(pair(label, template, f"c.{field}", old, witness))
    out.append(pair("raw_width", """example {n c route s} (i : Fin n) (p : Port) (origin : ℝ)
    (active : s.raw i p = some origin) (due : s.time = origin + @v@) :
    ∃ u, Nonempty (@Jump n c route s u) := by
  exact ⟨_, ⟨Jump.rawEnd _ i p origin active due⟩⟩
""", "c.pulseWidth", "1", """
def controlCfg : Constants := { nominal with pulseWidth := 2 }
def controlBlocked : Snapshot 1 :=
  { controlState .ready .ready 0 0 with
    time := 1, raw := fun _ p => if p = 0 then some 0 else none }
example : ∀ u, IsEmpty (Jump controlCfg controlRoute controlBlocked u) := by
  intro u
  constructor
  intro j
  cases j
  case rawEnd i p origin active due =>
    change (if p = 0 then some (0:ℝ) else none) = some origin at active
    split_ifs at active with hp
    · have ho : (0:ℝ) = origin := Option.some.inj active
      subst origin
      norm_num [controlBlocked, controlCfg, nominal] at due
  all_goals norm_num [controlBlocked, controlState, controlCfg, nominal] at *
"""))
    out.append(pair("delivery_due", """example {n c route s} (d : Delivery n)
    (before after : List (Delivery n)) (queue : s.pending = before ++ d :: after)
    (due : d.due = @v@) (free : s.raw d.cell d.port = none) :
    ∃ u, Nonempty (@Jump n c route s u) := by
  exact ⟨_, ⟨Jump.arrive _ d before after queue due free⟩⟩
""", "s.time", "s.time + 1", """
def controlBlocked : Snapshot 1 :=
  { controlState .ready .ready 0 0 with pending := [controlToken 0 1] }
example : ∀ u, IsEmpty (Jump nominal controlRoute controlBlocked u) := by
  intro u
  constructor
  intro j
  cases j
  case arrive d before after queue due free =>
    have member : d ∈ [controlToken 0 1] := by
      change d ∈ controlBlocked.pending
      rw [queue]
      simp
    simp only [List.mem_singleton] at member
    subst d
    norm_num [controlToken, controlBlocked, controlState] at due
  all_goals norm_num [controlBlocked, controlState, controlToken, nominal] at *
"""))
    out.append(pair("immediate_merge", """example {n c route s a b}
    (j : @Jump n c route s a) (k : Jump c route s b) : @v@ := by
  exact j.local_diamond k
""", "JumpDiamond c route a b", "a.ObservationalEq b", """
example : ¬ (∀ (a b : Snapshot 1),
    Nonempty (Jump nominal controlRoute controlContact a) →
    Nonempty (Jump nominal controlRoute controlContact b) → a.ObservationalEq b) := by
  intro h
  exact control_not_immediate (h _ _ control_fire control_mark)
"""))
    out.append(pair("raw_raw_merge", """example {n c route} (s : Snapshot n)
    (i j : Fin n) (p q : Port) (o r : ℝ)
    (hi : s.raw i p = some o) (hj : s.raw j q = some r)
    (hti : s.time = o + c.pulseWidth) (htj : s.time = r + c.pulseWidth) :
    @v@ := by
  exact rawEnd_rawEnd_diamond s i j p q o r hi hj hti htj
""", "JumpDiamond c route (setRaw s i p none) (setRaw s j q none)",
        "(setRaw s i p none).ObservationalEq (setRaw s j q none)", """
def controlTwoRaw : Snapshot 1 :=
  { controlContact with raw := fun _ _ => some (-1) }
example : ¬ (setRaw controlTwoRaw 0 0 none).ObservationalEq
    (setRaw controlTwoRaw 0 1 none) := by
  intro h
  have hr := congrFun (congrFun h.raw 0) 0
  norm_num [setRaw, controlTwoRaw] at hr
example : controlTwoRaw.time = (-1:ℝ) + nominal.pulseWidth := by
  norm_num [controlTwoRaw, controlContact, controlState, nominal]
"""))
    out.append(pair("arrival_merge", """example {n c route} (s : Snapshot n) (d e : Delivery n)
    (b₁ a₁ b₂ a₂ : List (Delivery n))
    (hq₁ : s.pending=b₁++d::a₁) (hq₂ : s.pending=b₂++e::a₂)
    (hd : d.due=s.time) (he : e.due=s.time)
    (hf₁ : s.raw d.cell d.port=none) (hf₂ : s.raw e.cell e.port=none) :
    @v@ := by
  exact arrive_arrive_diamond s d e b₁ a₁ b₂ a₂ hq₁ hq₂ hd he hf₁ hf₂
""", "JumpDiamond c route (Snapshot.afterArrival s d b₁ a₁) (Snapshot.afterArrival s e b₂ a₂)",
        "(Snapshot.afterArrival s d b₁ a₁).ObservationalEq (Snapshot.afterArrival s e b₂ a₂)", """
def controlTwoTokens : Snapshot 1 :=
  { controlContact with pending := [controlToken 0 0, controlToken 1 0] }
example : ¬ (Snapshot.afterArrival controlTwoTokens (controlToken 0 0) [] [controlToken 1 0]).ObservationalEq
    (Snapshot.afterArrival controlTwoTokens (controlToken 1 0) [controlToken 0 0] []) := by
  intro h
  have hr := congrFun (congrFun h.raw 0) 0
  norm_num [Snapshot.afterArrival, setRaw, controlToken, controlTwoTokens,
    controlContact, controlState] at hr
"""))
    out.append(pair("arrival_expiry_merge", """example {n c route} (s : Snapshot n) (d : Delivery n)
    (before after : List (Delivery n)) (hq : s.pending=before++d::after)
    (hd : d.due=s.time) (hf : s.raw d.cell d.port=none)
    (i : Fin n) (p : Port) (o : ℝ) (ha : s.raw i p=some o)
    (ht : s.time=o+c.pulseWidth) : @v@ := by
  exact arrive_rawEnd_diamond s d before after hq hd hf i p o ha ht
""", "JumpDiamond c route (Snapshot.afterArrival s d before after) (setRaw s i p none)",
        "(Snapshot.afterArrival s d before after).ObservationalEq (setRaw s i p none)", """
def controlArrivalRaw : Snapshot 1 :=
  { controlContact with
    pending := [controlToken 0 0], raw := fun _ p => if p = 1 then some (-1) else none }
example : ¬ (Snapshot.afterArrival controlArrivalRaw (controlToken 0 0) [] []).ObservationalEq
    (setRaw controlArrivalRaw 0 1 none) := by
  intro h
  have hr := congrFun (congrFun h.raw 0) 0
  norm_num [Snapshot.afterArrival, setRaw, controlToken, controlArrivalRaw,
    controlContact, controlState] at hr
"""))
    out.append(pair("raw_address", """example {n} (s : Snapshot n) (i j : Fin n) (p q : Port)
    (r : Option ℝ) (h : i ≠ j ∨ p ≠ q) :
    (setRaw s i p r).raw j q = @v@ := by
  exact setRaw_other s i j p q r h
""", "s.raw j q", "none", """
def controlRaw : Snapshot 1 := { controlContact with raw := fun _ _ => some 0 }
example : (setRaw controlRaw 0 0 none).raw 0 1 ≠ none := by
  simp [controlRaw, setRaw]
"""))
    out.append(pair("queue_loss", """example {n c route s u} (j : @Jump n c route s u)
    (Q : List (Delivery n)) :
    ∃ v, Nonempty (Jump c route (appendPending s Q) v) ∧
      v.ObservationalEq (appendPending u Q) ∧
      v.pending.length = @v@ := by
  obtain ⟨v, hj, hv⟩ := j.appendPending_observational Q
  refine ⟨v, hj, hv, ?_⟩
  simpa [appendPending] using hv.pending.length_eq
""", "u.pending.length + Q.length", "u.pending.length + Q.length + 1", """
example {n} (u v : Snapshot n) (Q : List (Delivery n))
    (h : v.ObservationalEq (appendPending u Q)) :
    v.pending.length ≠ u.pending.length + Q.length + 1 := by
  have count := h.pending.length_eq
  simp only [appendPending, List.length_append] at count
  omega
"""))
    out.append(pair("main_framing", """example {n c route s u} (j : @Jump n c route s u)
    (i : Fin n) (mode : MainMode) (h : u.main i=s.main i) : @v@ := by
  exact j.setMain_of_unchanged i mode h
""", "Nonempty (Jump c route (setMain s i mode) (setMain u i mode))",
        "IsEmpty (Jump c route (setMain s i mode) (setMain u i mode))", """
example : ¬ IsEmpty (Jump nominal controlRoute
    (setMain controlContact 0 .slow) (setMain controlMark 0 .slow)) := by
  intro h
  apply h.false
  exact Jump.mark _ 0 0 rfl rfl
"""))
    out.append(pair("aux_framing", """example {n c route s u} (j : @Jump n c route s u)
    (i : Fin n) (p : Port) (mode : AuxMode) (h : u.aux i p=s.aux i p) : @v@ := by
  exact j.setAux_of_unchanged i p mode h
""", "Nonempty (Jump c route (setAux s i p mode) (setAux u i p mode))",
        "IsEmpty (Jump c route (setAux s i p mode) (setAux u i p mode))", """
example : ¬ IsEmpty (Jump nominal controlRoute
    (setAux controlContact 0 0 .silent) (setAux controlFire 0 0 .silent)) := by
  intro h
  apply h.false
  exact Jump.fire _ 0 rfl rfl
"""))
    return out


COVERAGE = {
    "setRaw_other": "raw_address", "setRaw_commute": "raw_address",
    "queue_removal_diamond": "queue_loss", "due_delivery_eq_of_address": "delivery_due",
    "rawEnd_rawEnd_diamond": "raw_raw_merge", "arrive_rawEnd_diamond": "arrival_expiry_merge",
    "arrive_arrive_diamond": "arrival_merge", "Jump.setMain_of_unchanged": "main_framing",
    "Jump.setAux_of_unchanged": "aux_framing", "Jump.appendPending_observational": "queue_loss",
    "Jump.fire_diamond_of_unchanged": "fire_guard", "Jump.fastEnd_diamond_of_unchanged": "fast_exit_guard",
    "Jump.reopen_diamond_of_unchanged": "reopen_guard", "Jump.mark_diamond_of_unchanged": "mark_guard",
    "Jump.silent_diamond_of_unchanged": "silent_guard", "Jump.error_diamond_of_unchanged": "error_guard",
    "Jump.auxReady_diamond_of_unchanged": "aux_ready_guard", "Jump.eq_fire_of_main_changed": "fire_guard",
    "Jump.eq_fastEnd_of_main_changed": "fast_exit_guard", "Jump.eq_reopen_of_main_changed": "reopen_guard",
    "Jump.eq_mark_of_aux_changed": "mark_guard", "Jump.eq_silent_of_aux_changed": "silent_guard",
    "Jump.eq_error_of_aux_changed": "error_guard", "Jump.eq_auxReady_of_aux_changed": "aux_ready_guard",
    "JumpDiamond.symm": "immediate_merge", "Jump.local_diamond": "immediate_merge",
}


def mutate_conclusion(name, conclusion):
    """Alter the advertised observation, mode, or queue guarantee itself."""
    if name == 'setRaw_other':
        return conclusion.replace('=s.raw j q', '≠s.raw j q')
    if name == 'setRaw_commute':
        return conclusion.replace('j q t=setRaw', 'j q t≠setRaw')
    if name == 'queue_removal_diamond':
        return conclusion.replace('(ba++aa).Perm (bb++ab)', '¬ (ba++aa).Perm (bb++ab)')
    if name == 'due_delivery_eq_of_address':
        return conclusion.replace('d=e', 'd≠e')
    if name == 'Jump.appendPending_observational':
        return conclusion.replace('v.ObservationalEq (appendPending u Q)', 'v.ObservationalEq u')
    if name in ['Jump.setMain_of_unchanged', 'Jump.setAux_of_unchanged']:
        return conclusion.replace('Nonempty', 'IsEmpty')
    if name.startswith('Jump.eq_'):
        changed = {
            'Jump.eq_fire_of_main_changed': ('.fast', '.ready'),
            'Jump.eq_fastEnd_of_main_changed': ('.slow', '.fast'),
            'Jump.eq_reopen_of_main_changed': ('.ready', '.slow'),
            'Jump.eq_mark_of_aux_changed': ('.mark', '.ready'),
            'Jump.eq_silent_of_aux_changed': ('.silent', '.mark'),
            'Jump.eq_error_of_aux_changed': ('.error', '.silent'),
            'Jump.eq_auxReady_of_aux_changed': ('.ready', '.error'),
        }
        before, after = changed[name]
        return conclusion.replace(before, after)
    # Replacing a local diamond by immediate observational equality discards
    # the real continuation jumps; FIRE/MARK and distinct arrivals refute it.
    return conclusion.replace('JumpDiamond c route', 'Snapshot.ObservationalEq')


def api_instantiations():
    """Pair each exact public signature with its own changed conclusion."""
    results = {}
    for module in MODULES:
        source = (ROOT / f"KernelR/Family/{module}.lean").read_text()
        for match in re.finditer(r"^(?:@\[[^\n]*\]\s*)?(?:protected\s+)?theorem ([A-Za-z0-9_.]+)", source, re.M):
            name = match.group(1)
            start = match.end()
            proof_start = re.search(r':=\s*by\b', source[start:])
            assert proof_start is not None, name
            end = start + proof_start.start()
            signature = source[start:end]
            arguments = []
            pos = 0
            while pos < len(signature):
                if signature[pos].isspace():
                    pos += 1
                    continue
                if signature[pos] not in "{([":
                    break
                begin = pos
                depth = 0
                for index in range(pos, len(signature)):
                    char = signature[index]
                    if char in "{([":
                        depth += 1
                    elif char in "})]":
                        depth -= 1
                        if depth == 0:
                            pos = index + 1
                            break
                else:
                    raise AssertionError(f"Unclosed binder in {name}")
                body = signature[begin + 1:pos - 1]
                names = body.split(":", 1)[0].split()
                assert all(re.fullmatch(r"[A-Za-zα-ωΑ-Ω₀-₉][A-Za-z0-9_α-ωΑ-Ω₀-₉']*", n) for n in names), names
                arguments.extend(names)
            args = " ".join(f"({n}:={n})" for n in arguments)
            binders, conclusion = signature[:pos], signature[pos:]
            mutated = mutate_conclusion(name, conclusion)
            assert mutated != conclusion, (name, conclusion)
            proof = f":= by\n  exact {name} {args}\n"
            results[name] = (f'example {signature}{proof}',
                             f'example {binders}{mutated}{proof}')
    assert set(results) == set(COVERAGE), (set(results) - set(COVERAGE), set(COVERAGE) - set(results))
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--case', action='append', help='run exact case label (repeatable)')
    parser.add_argument('--inventory', action='store_true')
    parser.add_argument('--report', type=Path)
    parser.add_argument('--timeout', type=int, default=240,
                        help='seconds allowed for each complete Lean batch')
    args = parser.parse_args()
    controls = cases()
    names = {name for name, _, _ in controls}
    assert set(COVERAGE.values()) <= names
    api = api_instantiations()
    paired = [(name, good, bad) for name, (good, bad) in api.items()] + controls
    if args.inventory:
        print(json.dumps({'public_theorems': sorted(api),
                          'concrete_fixtures': sorted(names)}, indent=2))
        return
    if args.case:
        selected = set(args.case)
        all_names = {name for name, _, _ in paired}
        if selected - all_names:
            parser.error('unknown cases: ' + ', '.join(sorted(selected - all_names)))
        paired = [case for case in paired if case[0] in selected]
    # Concrete fixtures deliberately reuse controlCfg/controlBlocked names;
    # namespaces isolate their declarations in each batch.
    isolated = []
    for index, (name, good, bad) in enumerate(paired):
        def wrap(source):
            # A diamond conclusion used to infer c/route. Its mutation to
            # immediate equality must retain those same, explicitly typed
            # parameters, so rejection tests the claim rather than inference.
            source = source.replace('{n c route}',
                                    '{n} {c : Constants} {route : Router n}')
            return f'namespace Control{index}\n' + source + f'\nend Control{index}\n'
        isolated.append((name, wrap(good), wrap(bad)))
    report = run_batches(isolated, PREFIX, SUFFIX, root=ROOT,
                         root_module='KernelR.Family.JumpLocalDiamond', timeout=args.timeout)
    if args.report:
        args.report.write_text(json.dumps(report, indent=2) + '\n')
    print(f'{len(paired)} paired confluence controls passed; full inventory has '
          f'{len(api)} public theorems and {len(controls)} concrete fixtures.', flush=True)


if __name__ == "__main__":
    main()
