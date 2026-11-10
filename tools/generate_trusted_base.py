#!/usr/bin/env python3
"""Render the trusted-base reading list from Lean's declaration manifest.

Declaration locations are supplied by Lean, never by a handwritten line table.
The selected commit and file hashes authenticate the source behind every link.
The written-model mapping is keyed by declaration names and checked against
the headings in the cell laws and chain protocol. This renderer is not the dependency checker;
KernelR.TrustedBaseChecker computes the closure in Lean before export.
"""
from __future__ import annotations

import argparse
from functools import cache
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_MANIFEST = ROOT / "proof/lean/evidence/trusted_base.json"
DEFAULT_OUTPUT = ROOT / "docs/TRUSTED_BASE.md"
REPOSITORY = "https://github.com/HevisNico/kernel-R"
CELL_LAWS = "model/CELL.md"
CHAIN_PROTOCOL = "model/CHAIN_PROTOCOL.md"
PROTOCOL_SECTIONS = {"birth-and-fabrication", "chain-and-sources", "complete-executions-and-outcomes"}
VERIFICATION_SOURCES = {
    CELL_LAWS,
    CHAIN_PROTOCOL,
    "proof/lean/Audit.lean",
    "proof/lean/lean-toolchain",
    "proof/lean/lake-manifest.json",
    "proof/lean/KernelR/TrustedBaseChecker.lean",
    "proof/lean/KernelR/TrustedBase.lean",
    "tools/generate_trusted_base.py",
    ".github/actions/build-lean/action.yml",
    ".github/workflows/lean.yml",
    "proof/lean/scripts/evidence/export_trusted_base.py",
    "proof/lean/scripts/negative/check_trusted_base_negative.py",
    "proof/lean/scripts/negative/check_trusted_headline_negative.py",
    "proof/lean/scripts/check_trusted_source_boundary.py",
    "proof/lean/scripts/evidence/trusted_validation_report.py",
}


def model_source(anchor: str) -> str:
    return CHAIN_PROTOCOL if anchor in PROTOCOL_SECTIONS else CELL_LAWS


@cache
def git_bytes(commit: str, path: str) -> bytes:
    result = subprocess.run(["git", "show", f"{commit}:{path}"], cwd=ROOT,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if result.returncode:
        raise ValueError(f"Cannot authenticate {path} at {commit}: "
                         + result.stderr.decode(errors="replace").strip())
    return result.stdout


def source_link(commit: str, declaration: dict, *, statement_only: bool = False) -> str:
    path = declaration["file"]
    line = declaration["line"]
    if not isinstance(line, int) or line < 1:
        raise ValueError(f"Invalid generated source line for {declaration['name']}")
    end = declaration.get("end_line")
    if statement_only:
        lines = git_bytes(commit, path).decode().splitlines()
        last = end if isinstance(end, int) else line
        proof_line = next((index for index in range(line, last + 1)
                           if re.search(r":=\s*by\b", lines[index - 1])), None)
        if proof_line is None:
            raise ValueError(f"No statement/proof boundary in generated range for {declaration['name']}")
        end = proof_line
    fragment = f"#L{line}" + (f"-L{end}" if isinstance(end, int) and end > line else "")
    return f"{REPOSITORY}/blob/{commit}/{path}{fragment}"


def headings(text: str) -> set[str]:
    result = set()
    for heading in re.findall(r"^#{1,6}\s+(.+)$", text, re.M):
        slug = re.sub(r"[^\w\s-]", "", heading.strip().lower())
        result.add(re.sub(r"\s+", "-", slug))
    return result


def record_sources(manifest: dict) -> dict:
    paths = VERIFICATION_SOURCES | {entry["file"] for entry in manifest["trusted"]}
    paths.add(manifest["headline"]["file"])
    return {**manifest, "sources": {
        path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest()
        for path in sorted(paths)
    }}


def model_rule(name: str) -> tuple[str, str, str]:
    """Return reading group, written-model anchor, and exact semantic role."""
    tail = name.removeprefix("KernelR.Hybrid.")
    leaf = tail.rsplit(".", 1)[-1]
    if tail.startswith("TrustedHeadline."):
        return "Statement", "chain-and-sources", "Finite directed-chain protocol and its explicitly quantified observations."
    if tail in {"Port", "Values", "Coord", "MainMode", "AuxMode", "Snapshot", "Parameters", "Delivery", "Router"}:
        return "Model", "state-of-a-cell", "Cell coordinates, three ports, modes, fixed parameters, raw origins and pending deliveries."
    if leaf.startswith("instDecidableEq") or leaf.startswith("decEq"):
        return "Model", "state-of-a-cell", "Equality support for the finite mode/coordinate types; no additional cell law."
    if tail in {"a", "response", "nominalGain", "InRelativeBox", "PhysicalBox"}:
        return "Model", "constants", "Fixed constants, canonical READY response and independent per-port fabrication boxes."
    if tail in {"Thresholds", "Thresholds.nominal"}:
        return "Model", "constants", "Charge guards stored in the parameters and their original nominal levels."
    if tail == "FlowDynamics":
        return "Model", "event-semantics", "Integral field, fixed discrete state, raw support and delivery urgency shared by both guard profiles."
    if tail == "BirthState":
        return "Protocol inputs", "birth-and-fabrication", "Common birth at zero, no RAW currents, main READY, declared 1e−5 charge/memory bands, reserve [50,100], and auxiliary rest/ERROR alternatives; the headline separately requires all auxiliaries READY."
    if tail == "PhysicalInvariant":
        return "Observations", "energy", "Current upper-region bounds, own gain/recovery caps and reserve [50,100]."
    if tail == "ReadyCoordinates":
        return "Observations", "initial-and-prepared-sections", "Main READY with q in [1/10−1e−5,7/50], and READY auxiliaries in their rest band; the outcome also separately states q=1/10."
    if tail in {"CellInvariant", "RawValid"}:
        return "Observations", "initial-and-prepared-sections", "Declared current-state or active-RAW validity conditions."
    if tail == "UpperRegion":
        return "Observations", "event-semantics", "Nonnegative recovery, q ≤ 1 and mode-dependent auxiliary upper levels."
    if tail == "auxUpper":
        return "Observations", "auxiliaries-and-plasticity", "Auxiliary upper level 1/10 in ERROR and 1 in the other modes."
    if tail == "RestBand":
        return "Observations", "initial-and-prepared-sections", "Auxiliary rest band 1/40 ± 1/100000."
    if tail in {"pulse", "current"}:
        return "Model", "canonical-pulses", "Canonical current a·exp(−a·(t−F)) on [F,F+1), with the actual raw origin F."
    if tail == "drive":
        return "Model", "main-unit", "Admitted READY current Σ exp(zₚ)·pₚ(t)."
    if tail in {"errorAct", "markAct", "auxDrain"}:
        return "Model", "auxiliaries-and-plasticity", "Auxiliary decay and the mode, energy and cap gates of gain/recovery actuation."
    if tail == "work":
        return "Model", "energy", "W sums main work, auxiliary admission/drains and actual learning actuation."
    if tail == "field":
        return "Model", "main-unit", "Complete q/m/z/b/E vector field: READY leak plus admitted current, protected decays, gated actuation and E′ = 10(100−E)−W."
    if tail in {"BeforeGuards", "Flow", "setMain", "setAux", "setRaw", "Jump", "Move", "Execution", "CompleteThrough", "CausalRouter"}:
        return "Model", "event-semantics", "Native integral flows, exact mode/RAW/queue updates, first contacts and terminal urgency."
    if tail.startswith(("Ledger", "Flow.ledger", "Move.ledger", "Jump.ledger", "Execution.ledger", "Execution.emissionTimes", "WeakFlow.ledger", "WeakMove.ledger", "WeakExecution.ledger", "WeakExecution.emissionTimes")):
        return "Observations", "event-semantics", "Actual learning integrals and ordered FIRE observations of the recorded trace."
    if tail == "CellOrbitGerm":
        return "Crossing semantics", "event-semantics", "Positive-duration incoming-mode ODE continuation of every coordinate of the contact cell, initialized at its actual state."
    if tail == "CellRightCrossing":
        return "Crossing semantics", "event-semantics", "Some full-cell incoming-mode ODE germ is strictly above one immediately to the right; generic germ uniqueness is not asserted."
    if tail == "CrossingCompleteThrough":
        return "Crossing semantics", "event-semantics", "Reach T, resolve every jump enabled by its actual left/right crossing guards, and leave no pending token due by T."
    if tail.startswith(("Weak", "Flow.toWeak", "Execution.toWeak")) or tail in {"CellField", "CellValues", "ReadyCoordinate", "CrossingExecution", "InitiallyBelowReady"} or tail.startswith("Jump.Crossing"):
        return "Crossing semantics", "event-semantics", "Actual left approach and full-cell incoming-mode right ODE continuation; READY tangency is allowed in weak flows."
    if tail == "Snapshot.ObservationalEq":
        return "Observations", "event-semantics", "Equal clock, physical coordinates, modes and RAW origins; pending lists agree up to permutation."
    if tail == "UniversalCadenceOutcome":
        return "Observations", "complete-executions-and-outcomes", "Terminal READY/rest state, no RAW or pending traffic, own memory increments and exact actual FIRE counts."
    if tail == "finiteChainPreparationCount":
        return "Observations", "complete-executions-and-outcomes", "Actual preparation prefix length: fourteen leaf FIREs and twelve at each other cell."
    if tail == "cadenceActivePort":
        return "Observations", "complete-executions-and-outcomes", "Active cadence port: zero at the leaf, two at each other cell."
    if tail == "sourceTrain":
        return "Protocol inputs", "chain-and-sources", "Finite input-token train at dates start + gap·k, with supplied receiving cell and port."
    if tail == "finiteChainPreparationPort":
        return "Protocol inputs", "chain-and-sources", "Preparation enters port one at the leaf and port two at every other cell."
    if tail == "familyPreparationBornSource":
        return "Protocol inputs", "chain-and-sources", "Independent supplied births and their preparation queues, plus K period-four leaf inputs from time 160."
    if tail == "explicitFiniteChainRouter":
        return "Protocol inputs", "chain-and-sources", "Root sends nothing; cell i > 0 sends one parent-port-2 token on [160,T+1), due at t + delay(n−i,t)."
    if tail == "cadenceChainTerminal":
        return "Protocol inputs", "chain-and-sources", "Terminal horizon 160 + 4(K−1) + (11/10)·n + 8 for n+1 cells."
    if tail == "finiteCadenceTerminal":
        return "Protocol inputs", "chain-and-sources", "Horizon start + 4·(K−1) + (11/10)·(N−1) + 8, using natural-number subtraction before conversion to real time."
    if name == "KernelR.Chain.pathJitter":
        return "Protocol inputs", "chain-and-sources", "Sum of the supplied per-link nonnegative jitter budgets along the chain."
    if tail in {"independentFamilySource", "independentHeadQueue", "Snapshot.prependQueued", "Snapshot.prependQuiet", "Snapshot.requeue", "appendPending", "Delivery.head", "Delivery.succ"}:
        return "Protocol inputs", "chain-and-sources", "Assemble independent birth coordinates and exact source queues, preserving token dates/ports while embedding receiving-cell indices."
    raise ValueError(f"No written-model correspondence registered for trusted declaration {name}")


def authenticate(manifest: dict, commit: str) -> None:
    if not re.fullmatch(r"[0-9a-f]{40}", commit):
        raise ValueError("--commit must be a full fixed commit SHA")
    trusted = manifest["trusted"]
    names = [entry["name"] for entry in trusted]
    if len(names) != len(set(names)):
        raise ValueError("Duplicate trusted declaration in manifest")
    files = manifest.get("sources", {})
    if not files:
        raise ValueError("Manifest must authenticate its source files with SHA-256 hashes")
    if VERIFICATION_SOURCES - files.keys():
        raise ValueError("Unauthenticated verification sources: "
                         + ", ".join(sorted(VERIFICATION_SOURCES - files.keys())))
    for path, digest in files.items():
        actual = git_bytes(commit, path)
        if hashlib.sha256(actual).hexdigest() != digest:
            raise ValueError(f"Pinned source hash mismatch: {path}")
        if (ROOT / path).read_bytes() != actual:
            raise ValueError(f"Current source differs from its pinned trusted checkpoint: {path}")
    for entry in [manifest["headline"], *trusted]:
        if entry["file"] not in files:
            raise ValueError(f"Unauthenticated declaration source: {entry['name']}")
        lines = git_bytes(commit, entry["file"]).decode().splitlines()
        start, end = entry["line"], entry.get("end_line", entry["line"])
        if not (1 <= start <= end <= len(lines)):
            raise ValueError(f"Out-of-range generated declaration location: {entry['name']}")
    model_headings = {path: headings(git_bytes(commit, path).decode())
                      for path in (CELL_LAWS, CHAIN_PROTOCOL)}
    for entry in trusted:
        _, anchor, _ = model_rule(entry["name"])
        path = model_source(anchor)
        if anchor not in model_headings[path]:
            raise ValueError(f"Written-model heading does not exist: {path}#{anchor}")


def render(manifest: dict, commit: str) -> str:
    authenticate(manifest, commit)
    headline = manifest["headline"]
    trusted = manifest["trusted"]
    by_group: dict[str, list[dict]] = {}
    for entry in trusted:
        by_group.setdefault(model_rule(entry["name"])[0], []).append(entry)
    out = ["# Trusted base of the finite-chain headline", "",
           "<!-- Generated by tools/generate_trusted_base.py; do not edit declaration lists or locations. -->", "",
           f"Code checkpoint: [`{commit}`]({REPOSITORY}/tree/{commit}).", "",
           "This list comes from `trustedDeclarations` and Lean's dependency manifest. "
           "Source locations are generated from declaration names. The checker starts "
           "from the headline's type and follows the definitions and data-type interfaces "
           "that determine its meaning; it does not unfold proof terms.", "",
           "## Reading order", "",
           f"1. Read [`{headline['name']}`]({source_link(commit, headline, statement_only=True)}). "
           "Its witnesses and universal conclusions use the supplied closed-form router; "
           "no construction structure occurs in the statement.",
           f"2. Compare the definitions below with the [cell laws]({REPOSITORY}/blob/{commit}/{CELL_LAWS}) "
           f"and the [chain protocol]({REPOSITORY}/blob/{commit}/{CHAIN_PROTOCOL}).",
           "3. Read the crossing semantics, including the actual left history, the full-cell right ODE germ and terminal saturation.",
           "4. Read the protocol inputs: birth/source program, explicit router, delay/jitter assumptions and horizon.",
           "5. Read the compared observations: physical endpoint, actual FIRE lists and counts, and memory increments.",
           "6. Check the verification trust: Lean and Mathlib pins, the axiom audit, the dependency checker and their CI controls.", "",
           "## Fixed declaration list", "",
           f"The allowlist contains **{len(trusted)} semantic parent declarations**. "
           "Generated projections, constructors, recursors, matchers and equation/proof "
           "helpers are attributed to their parents, but their relevant interfaces and "
           "computational dependencies are still traversed. An independently source-declared "
           "helper remains a separate semantic name, including one named `model.match_1`, "
           "`model.proof_1` or `model._f`. Matchers require Lean's matcher metadata; "
           "other generated support requires parent source metadata and no independent "
           "source range. Inline derived equality instances and their `decEq` helpers "
           "must have their source range "
           "inside the owning inductive declaration. An arbitrary definition in a trusted "
           "namespace does not become trusted merely because of that namespace.", ""]
    for group in ["Model", "Crossing semantics", "Protocol inputs", "Observations", "Statement"]:
        if not by_group.get(group):
            continue
        out += [f"### {group}", "", "| Trusted declaration | Corresponding written-model equation or rule |", "|---|---|"]
        for entry in by_group[group]:
            _, anchor, description = model_rule(entry["name"])
            model = f"{REPOSITORY}/blob/{commit}/{model_source(anchor)}#{anchor}"
            out.append(f"| [`{entry['name']}`]({source_link(commit, entry)}) | [{description}]({model}) |")
        out.append("")
    out += ["## What the check establishes", "",
            "CI checks that every listed name exists and that every reachable project "
            "dependency of the headline's type belongs to this fixed list after parent "
            "attribution. The closure is computed independently of the allowlist. "
            "The paired controls reject an untrusted construction-based statement, "
            "a required name removed from the list, altered routing contracts, and "
            "handwritten helpers with compiler-looking suffixes and literal-only bodies. "
            "Source-range attribution is tested both in the current module and across "
            "an actual compiled/imported module.", "",
            "The theorem proofs are machine-checked. Mathematical semantic review "
            "therefore focuses on the listed definitions and the headline statement. "
            "This does not claim that the checker or Lean's implementation is formally "
            "verified here, nor that formal model fidelity experimentally validates a device.", "",
            "## Verification trust", "",
            f"- [Axiom audit]({REPOSITORY}/blob/{commit}/proof/lean/Audit.lean): only `propext`, `Classical.choice` and `Quot.sound` are permitted.",
            f"- [Lean toolchain]({REPOSITORY}/blob/{commit}/proof/lean/lean-toolchain) and [dependency commits]({REPOSITORY}/blob/{commit}/proof/lean/lake-manifest.json): the compiler, kernel, Mathlib and library implementation are verification dependencies.",
            f"- [Dependency traversal]({REPOSITORY}/blob/{commit}/proof/lean/KernelR/TrustedBaseChecker.lean) and [explicit allowlist/check invocation]({REPOSITORY}/blob/{commit}/proof/lean/KernelR/TrustedBase.lean): definitions are followed, proofs are not unfolded, and imported library internals are leaves.",
            f"- [Generated declaration manifest]({REPOSITORY}/blob/{commit}/proof/lean/evidence/trusted_base.json): names, generated source ranges and authenticated source hashes.",
            f"- [CI build action]({REPOSITORY}/blob/{commit}/.github/actions/build-lean/action.yml): verifies the pinned Lean distribution and builds the Lake package.",
            f"- [Fresh Lean export]({REPOSITORY}/blob/{commit}/proof/lean/scripts/evidence/export_trusted_base.py), [source boundary]({REPOSITORY}/blob/{commit}/proof/lean/scripts/check_trusted_source_boundary.py), and [CI workflow]({REPOSITORY}/blob/{commit}/.github/workflows/lean.yml): the exported list is rechecked, existing Lean declarations are preserved, and the controls run at the recorded revision.",
            "",
            "Full CI status and validation counts must be read at their exact recorded "
            "commit. The generated declaration list is not itself a claim that a CI run passed.", ""]
    return "\n".join(out)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--commit", help="full fixed code commit; defaults to manifest or existing document pin")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--record-sources", action="store_true",
                        help="record current source hashes in the Lean-exported manifest, then exit")
    args = parser.parse_args()
    manifest = json.loads(args.manifest.read_text())
    if args.record_sources:
        if args.check:
            parser.error("--record-sources cannot be combined with --check")
        manifest = record_sources(manifest)
        args.manifest.write_text(json.dumps(manifest, indent=2) + "\n")
        print(f"Recorded hashes for {len(manifest['sources'])} trusted/verification source files.")
        return
    commit = args.commit or manifest.get("code_commit")
    if not commit and args.output.is_file():
        match = re.search(r"^Code checkpoint: \[`([0-9a-f]{40})`\]", args.output.read_text(), re.M)
        if match:
            commit = match.group(1)
    if not commit:
        parser.error("--commit or manifest code_commit is required")
    generated = render(manifest, commit)
    if args.check:
        if not args.output.is_file() or args.output.read_text() != generated:
            raise SystemExit(f"Stale generated trusted-base document: {args.output.relative_to(ROOT)}")
        print(f"Trusted-base document is current at {commit}: {len(manifest['trusted'])} declarations.")
    else:
        args.output.write_text(generated)
        print(f"Wrote {args.output.relative_to(ROOT)} at {commit}.")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError) as error:
        raise SystemExit(str(error)) from error
