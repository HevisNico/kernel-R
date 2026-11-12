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
    if root_imports != expected or len(files) != 5:
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
