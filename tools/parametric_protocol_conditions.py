#!/usr/bin/env python3
"""Index the existing protocol inequalities without changing their mathematics.

The generated catalogue records sufficient conditions of the historical written
certificate layers, not a dependency-complete extraction of the universal Lean
proof and not a certificate for any new cell constants.  Exact endpoint checks
below are distinct from the optional independent integer-arithmetic replay.
"""

from __future__ import annotations

import argparse
import ast
from collections import Counter
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "docs/parametric_protocol_conditions.json"
STAGES = (
    ("reciprocal_learning", ()),
    ("reciprocal_entry", ("reciprocal_learning",)),
    ("reciprocal_cadence", ("reciprocal_entry",)),
    ("reciprocal_composition", ("reciprocal_entry",)),
)
BOXES = (("eps3e-3", "0.003"), ("eps1e-1", "0.1"))
CURRENT_INTERFACES = (
    ("proof/lean/KernelR/Hybrid.lean", "PhysicalBox", "fixed fabrication box; other constants remain nominal"),
    ("proof/lean/KernelR/Hybrid.lean", "BirthState", "birth bands; queue and all-READY auxiliaries supplied separately"),
    ("proof/lean/KernelR/HybridBirthCadenceChain.lean", "birth_cadence_chain_exists", "current common-birth chain existence inputs"),
    ("proof/lean/KernelR/HybridPreparedCadenceChainDomain.lean", "PreparedCadenceChainDomain", "prepared-state, source, wire and resource interface"),
    ("proof/lean/KernelR/HybridLocalCadenceBudgetReceiver.lean", "local_cadence_budget_receiver_exists", "receiver budget, gain band and terminal margin"),
    ("proof/lean/KernelR/HybridCadenceChainEnvelope.lean", "propagate", "numeric relay-latency envelope for the current proof"),
    ("proof/lean/KernelR/HybridResponseBounds.lean", "response_emission_deadline", "direct real response bound outside historical certificate inventory"),
    ("proof/lean/KernelR/HybridResponseBounds.lean", "response_raw_window_upper", "direct real pulse-window bound outside historical certificate inventory"),
    ("proof/lean/KernelR/HybridFiniteChainDoseCounting.lean", "ConstructedBirthCadenceChain.terminal_learning_headroom", "terminal cap margins used to derive open gates"),
    ("proof/lean/KernelR/CrossingChainHeadline.lean", "every_finite_chain_every_crossing_execution", "model-facing crossing headline inputs"),
)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def relative(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def comparison_sites(path: Path) -> list[dict]:
    """Source formulas, retaining symbolic loop/helper arguments rather than guesses.

    A helper may instantiate one site many times (e.g. each staged pulse).  These
    sites are not asserted to be a one-to-one map to expanded obligation names.
    """
    source = path.read_text()
    tree = ast.parse(source, filename=str(path))
    sites = []
    for node in ast.walk(tree):
        if not (
            isinstance(node, ast.Call)
            and isinstance(node.func, ast.Name)
            and node.func.id in {"lt", "le", "leq"}
            and len(node.args) == 3
        ):
            continue
        sites.append({
            "line": node.lineno,
            "comparison_helper": node.func.id,
            "name_expression": ast.get_source_segment(source, node.args[0]),
            "left_expression": ast.get_source_segment(source, node.args[1]),
            "right_expression": ast.get_source_segment(source, node.args[2]),
        })
    return sorted(sites, key=lambda site: site["line"])


def lean_interface(path: str, name: str, scope: str) -> dict:
    """Record selected real interfaces, not a claimed transitive proof analysis."""
    source_path = ROOT / path
    source = source_path.read_text()
    pattern = r"^(?:noncomputable )?(theorem|def|structure) " + re.escape(name) + r"(?=[\s{(])"
    match = re.search(pattern, source, re.MULTILINE)
    require(match is not None, f"missing selected Lean interface: {path}:{name}")
    tail = source[match.start():]
    if match.group(1) == "theorem":
        end = tail.find(":=")
        require(end >= 0, f"theorem has no proof boundary: {name}")
        fragment = tail[:end].rstrip()
    else:
        next_declaration = re.search(
            r"\n(?:/--|namespace |(?:noncomputable )?(?:theorem|def|structure) )", tail
        )
        fragment = tail[:next_declaration.start() if next_declaration else len(tail)].rstrip()
    return {"source": path, "source_sha256": sha256(source_path),
            "line": source[:match.start()].count("\n") + 1,
            "declaration": name, "scope": scope, "source_fragment": fragment}


def read_certificate(stage: str, box: str, epsilon: str) -> tuple[dict, dict]:
    path = ROOT / "results" / stage / box / "certificate.json"
    document = json.loads(path.read_text())
    require(document["epsilon_relative"] == epsilon, f"wrong epsilon: {path}")
    sources = document["source_sha256"]
    require("verify.py" in sources, f"missing independent verifier: {path}")
    for name, expected in sources.items():
        require(Path(name).name == name, f"nonlocal source identity: {name}")
        source = ROOT / "certify" / stage / name
        require(sha256(source) == expected, f"source identity changed: {source}")

    names = [ob["name"] for ob in document["obligations"]]
    require(len(names) == len(set(names)), f"duplicate obligation name: {path}")
    relation_counts = Counter()
    smallest_strict_margin = None
    for obligation in document["obligations"]:
        relation = obligation["relation"]
        require(relation in {"strict_lt", "le"}, f"unknown relation: {relation}")
        for side in ("left", "right"):
            interval = document["bounds"][obligation[side]]
            require(
                isinstance(interval, list) and len(interval) == 2
                and all(isinstance(value, str) for value in interval),
                f"non-exact interval: {path}:{obligation['name']}",
            )
            require(Fraction(interval[0]) <= Fraction(interval[1]), "reversed interval")
        left = Fraction(document["bounds"][obligation["left"]][1])
        right = Fraction(document["bounds"][obligation["right"]][0])
        require(left < right if relation == "strict_lt" else left <= right,
                f"published inequality fails: {path}:{obligation['name']}")
        relation_counts[relation] += 1
        if relation == "strict_lt":
            margin = right - left
            if smallest_strict_margin is None or margin < smallest_strict_margin:
                smallest_strict_margin = margin

    info = {
        "epsilon_relative": epsilon,
        "certificate": relative(path),
        "sha256": sha256(path),
        "status": document["status"],
        "enclosures": len(document["bounds"]),
        "comparison_counts": dict(sorted(relation_counts.items())),
        "all_published_endpoint_comparisons_hold": True,
        "smallest_strict_endpoint_margin": str(smallest_strict_margin),
        "symbolic_identities": len(document.get("symbolic_identities", [])),
    }
    return document, info


def catalogue() -> dict:
    result = {
        "schema": 1,
        "scope": (
            "Named sufficient inequalities from the existing local, entry, staged "
            "cadence and finite-chain composition certificates. This is not a "
            "complete dependency inventory of the current universal Lean proof, "
            "a minimal condition set, or a protocol certificate for new constants."
        ),
        "comparison_semantics": {
            "strict_lt": "upper(bounds[left]) < lower(bounds[right])",
            "le": "upper(bounds[left]) <= lower(bounds[right])",
            "coordinates": "left and right are keys in the referenced certificate's bounds",
            "source_sites": "Source formulas can be instantiated repeatedly by helpers and loops.",
        },
        "arithmetic_status": (
            "Generation validates exact rational published endpoints and recorded "
            "source hashes; use --replay to run the existing independent integer "
            "verifiers, including authenticated predecessor certificates. Neither "
            "operation rebuilds Lean or proves the written analytic arguments."
        ),
        "stages": [],
        "selected_current_lean_interfaces": [lean_interface(*item) for item in CURRENT_INTERFACES],
    }
    for stage, predecessors in STAGES:
        documents, boxes = [], []
        for box, epsilon in BOXES:
            document, info = read_certificate(stage, box, epsilon)
            documents.append(document)
            boxes.append(info)
        require(documents[0]["obligations"] == documents[1]["obligations"],
                f"box-specific obligation lists need separate indexing: {stage}")
        require(documents[0]["source_sha256"] == documents[1]["source_sha256"],
                f"box-specific verifier sources: {stage}")
        verifier = ROOT / "certify" / stage / "verify.py"
        producer = ROOT / "certify" / stage / "certify.py"
        result["stages"].append({
            "stage": stage,
            "scope": documents[0]["scope"],
            "written_theorem": f"proof/{stage}/THEOREM.md",
            "predecessors": list(predecessors),
            "producer": relative(producer),
            "independent_verifier": relative(verifier),
            "authenticated_sources_sha256": documents[0]["source_sha256"],
            "verifier_comparison_sites": comparison_sites(verifier),
            "producer_comparison_sites": comparison_sites(producer),
            "boxes": boxes,
            "obligations": documents[0]["obligations"],
        })
    result["totals"] = {
        "stages": len(result["stages"]),
        "certificates": sum(len(stage["boxes"]) for stage in result["stages"]),
        "named_obligations_per_box": sum(len(stage["obligations"]) for stage in result["stages"]),
        "published_comparisons_across_both_boxes": sum(
            len(stage["obligations"]) * len(stage["boxes"]) for stage in result["stages"]
        ),
    }
    return result


def replay_command(stage: str, box: str) -> list[str]:
    verifier = ROOT / "certify" / stage / "verify.py"
    certificate = ROOT / "results" / stage / box / "certificate.json"
    bootstrap = (
        "import pathlib,runpy,sys; script=sys.argv.pop(1); "
        "sys.path.insert(0,str(pathlib.Path(script).parent)); "
        "sys.argv[0]=script; runpy.run_path(script,run_name='__main__')"
    )
    args = [sys.executable, "-I", "-S", "-B", "-c", bootstrap,
            str(verifier), str(certificate)]
    if stage == "reciprocal_entry":
        args += ["--link-certificate", str(ROOT / "results/reciprocal_learning" / box / "certificate.json"),
                 "--link-code", str(ROOT / "certify/reciprocal_learning")]
    elif stage in {"reciprocal_cadence", "reciprocal_composition"}:
        args += ["--entry-certificate", str(ROOT / "results/reciprocal_entry" / box / "certificate.json"),
                 "--entry-code", str(ROOT / "certify/reciprocal_entry"),
                 "--local-certificate", str(ROOT / "results/reciprocal_learning" / box / "certificate.json"),
                 "--local-code", str(ROOT / "certify/reciprocal_learning")]
    return args


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="refuse stale generated inventory")
    parser.add_argument("--replay", action="store_true", help="also run all eight independent integer verifiers")
    parser.add_argument("--output", type=Path, default=OUTPUT)
    args = parser.parse_args()
    document = catalogue()
    content = json.dumps(document, indent=2, ensure_ascii=False) + "\n"
    if args.check:
        require(args.output.is_file() and args.output.read_text() == content,
                f"stale inventory: run {Path(__file__).name}")
    else:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(content)
    if args.replay:
        for stage, _ in STAGES:
            for box, _ in BOXES:
                completed = subprocess.run(replay_command(stage, box), cwd=ROOT,
                                           capture_output=True, text=True, timeout=300)
                require(completed.returncode == 0,
                        f"integer replay refused: {stage}/{box}\n{completed.stderr}")
                result = json.loads(completed.stdout)
                expected = next(item for item in document["stages"] if item["stage"] == stage)
                info = next(item for item in expected["boxes"] if item["epsilon_relative"] == result["epsilon"])
                require(result["certificate_sha256"] == info["sha256"], "replayed certificate identity changed")
                print(json.dumps({"stage": stage, "epsilon": result["epsilon"],
                                  "status": result["status"]}), flush=True)
    print(json.dumps({"inventory": relative(args.output) if args.output.is_relative_to(ROOT) else str(args.output),
                      "checked": args.check, "independent_integer_replay": args.replay,
                      **document["totals"]}), flush=True)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (ValueError, OSError, KeyError, subprocess.SubprocessError) as error:
        print(f"REFUSED: {error}", file=sys.stderr)
        raise SystemExit(1)
