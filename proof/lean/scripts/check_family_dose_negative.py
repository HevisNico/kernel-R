#!/usr/bin/env python3
"""Paired conclusion mutations for every public family dose theorem.

Each positive control rechecks the original theorem as an anonymous example.
Only after it succeeds do we alter the conclusion and require a Lean proof
error. Imports, hypotheses, and proof bodies are unchanged. The inventory is
exhaustive over these two owned files and refuses unregistered new theorems.
This is a semantic regression suite, not a second proof checker.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re

from family_control_batches import run_batches

ROOT = Path(__file__).resolve().parents[1]
SOURCES = ("KernelR/Family/Refinement.lean", "KernelR/Family/DoseCounting.lean")
PREFIX = """import KernelR.Family.DoseCounting
namespace KernelR.Family
open KernelR.Hybrid Set MeasureTheory
variable {cfg : Constants}
"""
SUFFIX = "\nend KernelR.Family\n"
# name -> (statement text, replacement, purpose)
MUTATIONS: dict[str, tuple[str, str, str]] = {}


def register(name, before, after, purpose):
    if name in MUTATIONS:
        raise RuntimeError(f"Duplicate theorem coverage: {name}")
    MUTATIONS[name] = before, after, purpose


register("Jump.no_actuation", "j.ledger.error i p = 0", "j.ledger.error i p = 1", "jumps do not supply a learning dose")
for kind, value in (("Flow", "f"), ("Move", "m"), ("Execution", "e")):
    register(f"{kind}.gain_balance", f"s.x i (.z p) + {value}.ledger.error i p", f"{value}.ledger.error i p", "retain the initial gain memory")
    register(f"{kind}.recovery_balance", f"s.x i .b + {value}.ledger.recovery i", f"{value}.ledger.recovery i", "retain the initial recovery memory")
for kind in ("Flow", "Execution"):
    register(f"{kind}.error_charge_balance", "cfg.gainFactor *", "(cfg.gainFactor + 1) *", "the ERROR coefficient is structural and symbolic")
    register(f"{kind}.error_affine_invariant", "cfg.gainFactor *", "(cfg.gainFactor + 1) *", "the exact affine relation uses the shared physical coefficient")
    register(f"{kind}.mark_charge_balance", "cfg.recoveryFactor *", "(cfg.recoveryFactor + 1) *", "the MARK coefficient is structural and symbolic")
    register(f"{kind}.full_error_of_open_endpoints", "= cfg.errorDose :=", "= cfg.errorDose + 1 :=", "full ERROR dose follows its actual levels")
    register(f"{kind}.full_mark_of_open_endpoints", "= cfg.markDose :=", "= cfg.markDose + 1 :=", "full MARK dose follows its actual levels")
for kind, value in (("Flow", "f"), ("Jump", "j"), ("Execution", "e")):
    before = f"∑ p : Port, {value}.ledger.mark i p"
    register(f"{kind}.recovery_sum_marks", before, f"({before}) + 1", "recovery is exactly the sum of all port contributions")
register("Jump.no_mark_actuation", "j.ledger.mark i p = 0", "j.ledger.mark i p = 1", "jumps do not supply a MARK dose")
for name, level in (
    ("mark_entry_guard", "auxThreshold"), ("mark_departure_guard", "markExit"),
    ("silent_entry_guard", "markExit"), ("silent_departure_guard", "errorLevel"),
    ("error_entry_guard", "errorLevel"), ("error_departure_guard", "auxRest"),
):
    register(f"Jump.{name}", f"= cfg.{level} :=", f"= cfg.{level} + 1 :=", "derive the correct symbolic level from the actual jump")
for phase in ("error", "mark"):
    register(f"guarded_{phase}_dose", f"= cfg.{phase}Dose :=", f"= cfg.{phase}Dose + 1 :=", "complete exposed actual sections have their exact dose")
    register(f"Move.{phase}_zero_of_inactive", f"move.ledger.{phase} i p = 0", f"move.ledger.{phase} i p = 1", "structurally inactive moves contribute zero")
    before = f"segment.ledger.{phase} i p + rest.ledger.{phase} i p"
    register(f"Execution.dose_{phase}_append", before, before + " + 1", "concatenation is additive without an extra dose")
for cover, dose in (("ErrorSectionCover", "errorDose"), ("MarkSectionCover", "markDose")):
    register(f"{cover}.ledger_eq", f"cfg.{dose} * cover.count", f"(cfg.{dose} + 1) * cover.count", "whole-trace counts use the symbolic phase dose")
    for suffix in ("count_unique", "count_unique_of_admissible"):
        register(f"{cover}.{suffix}", "left.count = right.count", "left.count = right.count + 1", "valid actual-trace covers agree on the count")
register("Execution.memory_of_section_covers", "cfg.errorDose * (errors i p).count", "(cfg.errorDose + 1) * (errors i p).count", "the memory formula retains the exact section dose")
for name in ("same_increments_of_same_counts", "same_increments_of_same_doses_and_counts"):
    before = "u₂.x i (.z p) - s₂.x i (.z p)"
    register(name, before, before + " + 1", "equal valid counts and doses give equal increments")
register("same_memories_of_same_birth_and_counts", "u₁.x i (.z p) = u₂.x i (.z p)", "u₁.x i (.z p) = u₂.x i (.z p) + 1", "equal initial memories and counts give equal final memories")


DECLARATION = re.compile(r"(?m)^(?:theorem|lemma|def|noncomputable def|structure|inductive|#print|end\b|/--)")
THEOREM = re.compile(r"(?m)^theorem ([^\s{(]+)")


def cases():
    result = []
    names = set()
    for source in SOURCES:
        text = (ROOT / source).read_text()
        for match in THEOREM.finditer(text):
            name = match.group(1)
            names.add(name)
            boundary = DECLARATION.search(text, match.end())
            declaration = text[match.start():boundary.start() if boundary else len(text)].strip()
            header, sep, proof = declaration.partition(":=")
            if not sep:
                raise RuntimeError(f"No proof boundary in {source}: {name}")
            before, after, purpose = MUTATIONS[name]
            if before not in header + ":=":
                raise RuntimeError(f"Stale conclusion mutation for {name}: {before!r}")
            original = (header + ":=" + proof).replace("theorem " + name, "example", 1)
            changed = (header + ":=").replace(before, after) + proof
            changed = changed.replace("theorem " + name, "example", 1)
            # Qualified theorem declarations elaborate their proof in that
            # namespace. Preserve it when replacing the name by `example`.
            if "." in name:
                namespace = name.rsplit(".", 1)[0]
                original = f"namespace {namespace}\n{original}\nend {namespace}\n"
                changed = f"namespace {namespace}\n{changed}\nend {namespace}\n"
            result.append((name, source, purpose, original, changed))
    if names != MUTATIONS.keys():
        raise RuntimeError(f"Coverage mismatch: missing={sorted(names-MUTATIONS.keys())}, stale={sorted(MUTATIONS.keys()-names)}")
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--inventory", action="store_true", help="print theorem/mutation coverage without running Lean")
    parser.add_argument("--case", help="run one exact theorem name")
    parser.add_argument("--timeout", type=int, default=300)
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    selected = cases()
    if args.case:
        selected = [case for case in selected if case[0] == args.case]
        if not selected:
            parser.error("unknown theorem name")
    if args.inventory:
        print(json.dumps([{"theorem": x[0], "source": x[1], "mutation": x[2]} for x in selected], indent=2))
        return
    run_batches([(name, good, bad) for name, _, _, good, bad in selected],
                PREFIX, SUFFIX, root_module="KernelR.Family.DoseCounting",
                root=ROOT, timeout=args.timeout)
    checked = [{"theorem": name, "source": source, "mutation": purpose,
                "positive": "passed", "negative": "rejected"}
               for name, source, purpose, _, _ in selected]
    report = {"paired_controls": len(checked), "results": checked}
    if args.report:
        args.report.write_text(json.dumps(report, indent=2) + "\n")
    print(f"Family dose controls: {len(checked)} positive proofs passed; {len(checked)} altered conclusions rejected.")


if __name__ == "__main__":
    main()
