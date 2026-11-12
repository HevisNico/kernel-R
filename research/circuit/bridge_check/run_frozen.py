"""Run the frozen rest replays and DC sweeps on the machine of runtime amendment 2.

  run_frozen.py rest|gain --publication-commit COMMIT [--only NAME ...]

The decks, run lists, time limits and output layout are those of the frozen
rest_probe.py and gain_probe.py, imported unchanged. Only the executable and
the absence of the temporary-file adapter differ: see RUNTIME_AMENDMENT_2.md.
"""
import argparse
import gzip
import json
import os
from pathlib import Path
import subprocess
import time

import gain_probe
import rest_probe

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
digest = rest_probe.digest
FROZEN = {
    "rest": dict(manifest="manifest.json", commit="021580d", folder="runs", raw="trace.txt", timeout=600,
                 files=("REST_PROTOCOL.md", "manifest.json", "rest_probe.py", "rest_analyze.py"), deck=rest_probe.deck),
    "gain": dict(manifest="gain_manifest.json", commit="abcbb5b", folder="gain_runs", raw="dc.txt", timeout=120,
                 files=("GAIN_PROTOCOL.md", "gain_manifest.json", "gain_probe.py", "gain_analyze.py"), deck=gain_probe.deck),
}
AMENDMENT = ("RUNTIME_AMENDMENT_2.md", "runtime2.json", "run_frozen.py")


def published(commit, name):
    return subprocess.check_output(["git", "-C", str(ROOT), "show", f"{commit}:research/circuit/bridge_check/{name}"])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("kind", choices=sorted(FROZEN))
    parser.add_argument("--publication-commit", required=True, help="pushed commit that holds this amendment")
    parser.add_argument("--only", nargs="*", help="run only these names of the frozen list, each once")
    args = parser.parse_args()
    rule = FROZEN[args.kind]
    manifest = json.loads((HERE / rule["manifest"]).read_text())
    runtime = json.loads((HERE / "runtime2.json").read_text())
    for relative, expected in manifest["source_sha256"].items():          # the frozen sources are untouched
        assert digest(ROOT / relative) == expected, relative
    for name in rule["files"]:
        assert published(rule["commit"], name) == (HERE / name).read_bytes(), name
    for name in AMENDMENT:                                                # the amendment is the published one
        assert published(args.publication_commit, name) == (HERE / name).read_bytes(), name
    remote = subprocess.check_output(["git", "-C", str(ROOT), "branch", "-r", "--contains", args.publication_commit], text=True)
    assert remote.strip(), "the amendment commit is not pushed"
    ngspice = Path(runtime["ngspice_path"])
    assert digest(ngspice) == runtime["ngspice_sha256"], "executable changed"
    assert subprocess.check_output(["git", "-C", str(ROOT / "pdk"), "rev-parse", "HEAD"], text=True).strip() == manifest["pdk_commit"], "PDK changed"
    assert (ROOT / ".spiceinit").read_bytes() == (ROOT / "spiceinit.txt").read_bytes(), "compatibility settings changed"
    tmp = HERE / "tmp"
    tmp.mkdir(exist_ok=True)
    env = dict(os.environ, TMPDIR=str(tmp), SPICE_SCRIPTS=str(HERE / "runtime"))
    env.pop("LD_PRELOAD", None)
    for run in manifest["runs"]:
        if args.only and run["name"] not in args.only:
            continue
        out = HERE / rule["folder"] / run["name"]
        out.mkdir(parents=True, exist_ok=False)                           # a run is made once and never replaced
        raw, circuit = out / rule["raw"], out / "input.spice"
        circuit.write_text(rule["deck"](run, raw))
        meta = dict(run=run, publication_commit=subprocess.check_output(
                        ["git", "-C", str(ROOT), "rev-parse", rule["commit"]], text=True).strip(),
                    runtime_amendment=2, amendment_commit=args.publication_commit, started_unix=time.time(),
                    deck_sha256=digest(circuit), ngspice_sha256=digest(ngspice), ngspice_version=runtime["ngspice_version"],
                    tmpfile_adapter_sha256=None, status="running")
        if args.kind == "rest":
            meta["signals"] = rest_probe.SIGNALS
        (out / "metadata.json").write_text(json.dumps(meta, indent=2) + "\n")
        try:
            p = subprocess.run([str(ngspice), "-b", str(circuit)], cwd=ROOT, capture_output=True, text=True,
                               timeout=rule["timeout"], env=env)
            (out / "stdout.log").write_text(p.stdout)
            (out / "stderr.log").write_text(p.stderr)
            meta.update(returncode=p.returncode, status="produced_trace" if p.returncode == 0 and raw.exists() else "failed")
        except subprocess.TimeoutExpired as exc:
            (out / "stdout.log").write_bytes(exc.stdout or b"")
            (out / "stderr.log").write_bytes(exc.stderr or b"")
            meta.update(status="timeout")
        finally:
            meta["finished_unix"] = time.time()
            if raw.exists():
                meta["raw_sha256"] = digest(raw)
                with raw.open("rb") as src, (out / (rule["raw"] + ".gz")).open("wb") as dest:
                    with gzip.GzipFile(filename="", mode="wb", fileobj=dest, mtime=0) as zipped:
                        for block in iter(lambda: src.read(1024 * 1024), b""):
                            zipped.write(block)
                raw.unlink()
                meta["gz_sha256"] = digest(out / (rule["raw"] + ".gz"))
            (out / "metadata.json").write_text(json.dumps(meta, indent=2) + "\n")
        print(run["name"], meta["status"], flush=True)


if __name__ == "__main__":
    main()
