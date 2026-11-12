#!/usr/bin/env python3
"""Build/audit this standalone package; reject paired semantic mutations.

Only type/proof failures count as semantic rejection. Parser/import failures,
timeouts, missing tools, admissions and native-evaluation shortcuts do not.
All writes for controls are confined to temporary directories below .lake.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
PROJECT = ROOT / "SelfCertifyingLearning"

# Each pair first compiles the original complete module, then changes one
# premise, conclusion or transition. Physical assumptions remain explicit.
MUTATIONS = [
    ("correction_without_decrease", "Budget", "(decrease : next + eta ≤ v)", "(decrease : next ≤ v)"),
    ("unpaid_idle_increase", "Budget", "(nonincrease : next ≤ v)", "(nonincrease : next ≤ v + 1)"),
    ("omit_disturbance_budget", "Budget", "final + eta * corrections trace ≤ initial + injected trace", "final + eta * corrections trace ≤ initial"),
    ("omit_coupling_margin", "Composition", "(margin : eta + weighted weights added indices ≤ weighted weights removed indices)", "(margin : weighted weights added indices ≤ weighted weights removed indices)"),
    ("unpaid_spillover", "Composition", "weighted weights before indices + weighted weights added indices := by", "weighted weights before indices := by"),
    ("overstate_matrix_margin", "Composition", "eta := 2", "eta := 3"),
    ("untrusted_state_enclosure", "Deadline", "(enclosure : ∀ k, k ≤ deadline → (initial : Int) - (loss k : Int) ≤ state k)", "(enclosure : True)"),
    ("omit_between_probe_loss_bound", "Deadline", "(lossBound : ∀ k, k ≤ deadline → loss k ≤ loss deadline)", "(lossBound : True)"),
    ("spend_repair_reserve", "Deadline", "(budget : loss deadline + reserve ≤ initial)", "(budget : loss deadline ≤ initial)"),
    ("extend_certificate_deadline", "Deadline", "(within : earlier ≤ deadline)", "(within : True)"),
    ("use_expired_certificate", "Deadline", "now ≤ cert.expires ∧ cert.valid state", "now ≤ cert.expires + 1 ∧ cert.valid state"),
    ("overstate_two_level_progress", "TwoLevel", "rank t + 2 = rank s := by", "rank t + 3 = rank s := by"),
    ("ignore_interval_uncertainty", "Renewal", "anchor.hi + granularity ≤ next.lo ∨ next.hi + granularity ≤ anchor.lo", "anchor.lo + granularity ≤ next.hi ∨ next.lo + granularity ≤ anchor.hi"),
    ("undercharge_sampled_variation", "Renewal", "distance previous sample.truth + variation sample.truth rest", "variation sample.truth rest"),
    ("inflate_reopening_granularity", "Renewal", "g * reopenings g initial.report (samples.map Sample.report) ≤", "(g + 1) * reopenings g initial.report (samples.map Sample.report) ≤"),
    ("ignore_rate_measurement_error", "Renewal", "⟨value - radius, value + radius, by omega⟩", "⟨value, value, by omega⟩"),
    ("omit_detection_uncertainty_widths", "Renewal", "(movement : g + (a.hi - a.lo) + (b.hi - b.lo) ≤ distance x y)", "(movement : g ≤ distance x y)"),
    ("spend_scheduler_reserve", "Scheduler", "if bound * (cap + 1) + reserve ≤ initial then cap + 1", "if bound * (cap + 1) ≤ initial then cap + 1"),
    ("schedule_beyond_cap", "Scheduler", "then cap + 1\n      else horizon", "then cap + 2\n      else horizon"),
    ("omit_future_slew", "Scheduler", "report.hi + slew * cap\n", "report.hi\n"),
    ("underrepair_one_tick", "Scheduler", "reserve + bound - initial\n", "reserve - initial\n"),
    ("clip_negative_reserve", "Controller", "if 0 ≤ lower then", "if True then"),
    ("reuse_stale_safety_anchor", "Controller", "Scheduler.rateCeiling reading.rate slew cap) cap⟩", "Scheduler.rateCeiling anchor slew cap) cap⟩"),
    ("ignore_repair_latency_loss", "Repair", "c.bound * c.latency\n", "c.bound\n"),
    ("spend_repair_buffer", "Repair", "c.service + c.loss\n", "c.service\n"),
    ("ignore_loss_in_net_gain", "Repair", "c.dose - c.loss\n", "c.dose\n"),
    ("allow_zero_net_progress", "Repair", "c.loss < c.dose ∧ c.target ≤ c.capacity", "c.loss ≤ c.dose ∧ c.target ≤ c.capacity"),
    ("undersized_restart_capacity", "Repair", "c.target ≤ c.capacity\n", "c.guard ≤ c.capacity\n"),
    ("ignore_storage_saturation", "Repair", "min c.capacity (lower + c.gain)\n", "lower + c.gain\n"),
    ("omit_delayed_dose_delivery", "Repair", "(delivered : min (c.capacity : Int) (initial - (c.loss : Int) + (c.dose : Int)) ≤ final)", "(delivered : min (c.capacity : Int) (initial - (c.loss : Int)) ≤ final)"),
    ("erase_recovery_elapsed_time", "Repair", "(pulses c n lower : Int) ≤ state (n * c.latency) := by", "(pulses c n lower : Int) ≤ state n := by"),
    ("schedule_to_bare_service", "ClosedLoop", "match Scheduler.plan lower c.guard c.bound c.maxWait with", "match Scheduler.plan lower c.service c.bound c.maxWait with"),
    ("forget_wait_loss", "ClosedLoop", "| .wait ticks => lower - c.bound * ticks", "| .wait ticks => lower"),
    ("zero_time_write", "ClosedLoop", "| .write => c.latency\n", "| .write => 0\n"),
    ("handoff_without_buffer", "ClosedLoop", "(Controller.visit g c.guard slew c.maxWait anchor reading).delay = some delay", "(Controller.visit g c.service slew c.maxWait anchor reading).delay = some delay"),
    ("deliver_dose_early", "RepairPlant", "if t < c.latency then", "if t + 1 < c.latency then"),
    ("expiry_at_dispatch_only", "Epochs", "offer.issued ≤ cursor.now ∧ cursor.now + span cursor offer ≤ offer.expires ∧", "offer.issued ≤ cursor.now ∧ cursor.now ≤ offer.expires ∧"),
    ("accept_future_issuance", "Epochs", "offer.issued ≤ cursor.now ∧ cursor.now + span cursor offer ≤ offer.expires ∧", "True ∧ cursor.now + span cursor offer ≤ offer.expires ∧"),
    ("weaken_service_on_switch", "Epochs", "decide (offer.config.Valid ∧ offer.config.service = policy.service ∧", "decide (offer.config.Valid ∧ offer.config.service ≤ policy.service ∧"),
    ("spend_next_phase_buffer", "Epochs", "policy.handoff ≤ endpoint cursor offer ∧ charge cursor offer ≤ cursor.credit)", "True ∧ charge cursor offer ≤ cursor.credit)"),
    ("admit_unfunded_reconfiguration", "Epochs", "policy.handoff ≤ endpoint cursor offer ∧ charge cursor offer ≤ cursor.credit)", "policy.handoff ≤ endpoint cursor offer ∧ True)"),
    ("erase_switch_charge", "Epochs", "deficit offer.config (entry cursor offer) - cursor.debt\n", "0\n"),
    ("refund_spent_switch_credit", "Epochs", "cursor.credit - charge cursor offer⟩", "cursor.credit⟩"),
    ("reset_terminal_debt", "Epochs", "deficit offer.config (endpoint cursor offer), cursor.credit - charge cursor offer⟩", "0, cursor.credit - charge cursor offer⟩"),
    ("insert_unaccounted_time_gap", "Epochs", "⟨cursor.now + span cursor offer, endpoint cursor offer,", "⟨cursor.now + span cursor offer + 1, endpoint cursor offer,"),
    ("zero_decision_phase", "Epochs", "offer.config.Ready (entry cursor offer) ∧ 0 < offer.decisions ∧", "offer.config.Ready (entry cursor offer) ∧ 0 ≤ offer.decisions ∧"),
    ("hide_refusal_as_completion", "Epochs", "| none => .blocked cursor", "| none => .complete cursor"),
    ("omit_switching_from_global_balance", "Epochs", "plan.finish.debt + plan.writes ≤ cursor.debt + plan.switchCost + plan.leakBudget := by", "plan.finish.debt + plan.writes ≤ cursor.debt + plan.leakBudget := by"),
    ("reuse_relative_origin_between_epochs", "EpochSafety", "(fun t => state (cursor.now + t)) ∧ Realizes state tail", "(fun t => state t) ∧ Realizes state tail"),
    ("skip_reference_dose_verification", "EpochExamples", "decide (action = .write →\n      min (c.capacity : Int) (state 0 - (c.loss : Int) + (c.dose : Int)) ≤ state c.latency)", "true"),

    ("ignore_write_horizon", "OfferFactory", "count * max hardware.maxWait hardware.latency\n", "count * hardware.maxWait\n"),
    ("omit_factory_measurement_error", "OfferFactory", "let report := Renewal.measurement reading.value reading.error", "let report := Renewal.measurement reading.value 0"),
    ("omit_factory_future_slew", "OfferFactory", "Scheduler.rateCeiling report hardware.slew window,", "Scheduler.rateCeiling report 0 window,"),
    ("resign_stale_measurement", "OfferFactory", "if request.reading.measuredAt = cursor.now then", "if True then"),
    ("forget_actual_write_loss", "OfferFactory", "| n + 1 => loss rate n + rate (n + 1)", "| n + 1 => loss rate n"),
    ("weaken_measured_growth", "OfferFactory", "growth : ∀ k, k ≤ horizon hardware count → rate k ≤ rate 0 + hardware.slew * k", "growth : ∀ k, k ≤ horizon hardware count → rate k ≤ rate 0 + hardware.slew * k + 1"),
    ("weaken_physical_flow", "OfferFactory", "flow : ∀ k, k < horizon hardware count → state k - (rate (k + 1) : Int) ≤ state (k + 1)", "flow : ∀ k, k < horizon hardware count → state k - (rate (k + 1) : Int) - 1 ≤ state (k + 1)"),
    ("assume_dose_without_delivery", "OfferFactory", "delivery : Delivers (make policy hardware reading count).config count\n    (entry cursor (make policy hardware reading count)) rate state", "delivery : True"),
    ("observe_after_dispatch", "OfferFactory", "(observed : (cursor.lower : Int) ≤ state cursor.now)", "(observed : (cursor.lower : Int) ≤ state (cursor.now + 1))"),
    ("invent_larger_dose", "OfferFactory", "hardware.latency, hardware.dose, hardware.capacity, hardware.maxWait⟩", "hardware.latency, hardware.dose + 1, hardware.capacity, hardware.maxWait⟩"),



]

SEMANTIC = re.compile(r"Type mismatch|type mismatch|unsolved goals|omega could not prove|Tactic `decide` proved|tactic 'decide' proved", re.I)
BROKEN = re.compile(r"unexpected token|Unknown identifier|Unknown constant|unknown module|unknown package|object file .* does not exist|unknown tactic|failed to synthesize", re.I)


def run(args, cwd=ROOT):
    result = subprocess.run(args, cwd=cwd, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, timeout=120)
    return result.returncode, result.stdout


def require_success(args, cwd=ROOT):
    code, output = run(args, cwd)
    if code or re.search(r"declaration uses ['`]?sorry", output):
        raise RuntimeError(f"Positive check failed: {args}\n{output}")
    return output


def hygiene():
    files = sorted(PROJECT.glob("*.lean"))
    root_imports = set((ROOT / "SelfCertifyingLearning.lean").read_text().splitlines())
    expected = {"import SelfCertifyingLearning." + p.stem for p in files}
    if root_imports != expected or len(files) != 16:
        raise RuntimeError("Root module must import exactly every maintained proof module")
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    if manifest["packages"] or "[[require]]" in (ROOT / "lakefile.toml").read_text():
        raise RuntimeError("The abstract package must have no external dependencies")
    for path in [ROOT / "SelfCertifyingLearning.lean", ROOT / "Audit.lean", *files]:
        source = path.read_text()
        if re.search(r"\b(sorry|admit|native_decide)\b|^\s*(?:private\s+)?(?:axiom|unsafe)\s", source, re.M):
            raise RuntimeError(f"Forbidden proof shortcut in {path.name}")
        for imported in re.findall(r"^import\s+(\S+)", source, re.M):
            if not (imported == "Std" or imported == "SelfCertifyingLearning" or
                    imported.startswith("SelfCertifyingLearning.") or
                    (path.name == "Audit.lean" and imported.startswith("Lean."))):
                raise RuntimeError(f"Unexpected dependency {imported}")


def semantic_controls():
    passed = []
    with tempfile.TemporaryDirectory(prefix="semantic-", dir=ROOT / ".lake") as tmp:
        target = Path(tmp) / "Control.lean"
        for label, module, old, new in MUTATIONS:
            source = (PROJECT / f"{module}.lean").read_text()
            if source.count(old) != 1:
                raise RuntimeError(f"Mutation {label} no longer has one exact anchor")
            target.write_text(source)
            require_success(["lake", "env", "lean", str(target)])
            target.write_text(source.replace(old, new))
            code, output = run(["lake", "env", "lean", str(target)])
            if not code or BROKEN.search(output) or not SEMANTIC.search(output):
                raise RuntimeError(f"Mutation {label} did not fail semantically:\n{output}")
            passed.append(label)
    return passed


def audit_controls():
    payloads = {
        "unused_external_namespace_axiom": "\nnamespace External\naxiom hidden : False\nend External\n",
        "unused_private_axiom": "\nprivate axiom hidden : False\n",
        "admitted_external_theorem": "\nnamespace External\ntheorem hidden : False := by sorry\nend External\n",
    }
    passed = []
    with tempfile.TemporaryDirectory(prefix="audit-", dir=ROOT / ".lake") as tmp:
        copy = Path(tmp)
        for name in ["lakefile.toml", "lake-manifest.json", "lean-toolchain", "SelfCertifyingLearning.lean", "Audit.lean"]:
            shutil.copy2(ROOT / name, copy / name)
        shutil.copytree(PROJECT, copy / "SelfCertifyingLearning")
        require_success(["lake", "build"], copy)
        target = copy / "SelfCertifyingLearning/Deadline.lean"
        original = target.read_text()
        for label, payload in payloads.items():
            target.write_text(original + payload)
            code, output = run(["lake", "build"], copy)
            if not code or BROKEN.search(output) or not re.search(r"Unexpected (?:project )?axiom", output):
                raise RuntimeError(f"Audit did not reject {label}:\n{output}")
            passed.append(label)
    return passed


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    hygiene()
    require_success(["lake", "build"])
    audit = require_success(["lake", "env", "lean", "Audit.lean"])
    semantic = semantic_controls()
    audits = audit_controls()
    maintained = [ROOT / "lakefile.toml", ROOT / "lake-manifest.json", ROOT / "lean-toolchain",
                  ROOT / "SelfCertifyingLearning.lean", ROOT / "Audit.lean", ROOT / "verify.py",
                  *sorted(PROJECT.glob("*.lean"))]
    report = {"toolchain": (ROOT / "lean-toolchain").read_text().strip(),
              "audit": audit.strip(), "semantic_controls": semantic, "audit_controls": audits,
              "sha256": {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in maintained}}
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(report, indent=2) + "\n")
    print(audit.strip())
    print(f"PASS: {len(semantic)} paired semantic mutations; {len(audits)} audit mutations")


if __name__ == "__main__":
    main()
