"""Frozen rest-state diagnostic. Does not change original campaign results."""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent
SIGNALS = ["v(vq)", "v(p)", "v(cmpm)", "v(vrefmn)", "v(vmem1)", "v(vmem2)"]
for port in (1, 2):
    SIGNALS += [f"v(x{port}.{node})" for node in ("vs", "sum", "a", "b", "si")]


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def deck(run, raw):
    text = (ROOT / "cell.spice").read_text()
    if run["noise"]:
        params = json.loads((ROOT / "noise.json").read_text())["params"]
        for node, white, flicker in (("nzc", params["vncw"], params["vncf"]),
                                    ("nzo", params["vnow"], params["vnof"]),
                                    ("nzi", params["inmw"], 0),
                                    ("nzm", params["vnmw"], params["vnmf"])):
            old = f"vnz{node[2]} {node} 0 dc 0"
            assert text.count(old) == 1
            text = text.replace(old, f"{old} trnoise({white:.6g} {params['tnz']:.6g} {1 if flicker else 0} {flicker:.6g})")
    lines = [f"* Bridge rest diagnostic: {run['name']}",
             f'.lib "pdk/models/sky130.lib.spice" {run["section"]}'] + text.splitlines()[1:-1]
    lines += [".param kp=10", f".option temp={run['temperature_C']}",
              ".save " + " ".join(SIGNALS), ".control"]
    if run["seed"] is not None:
        lines += [f"setseed {run['seed']}", "reset"]
    lines += [f"tran 1u {22*440e-6:.12g} 0 {run['max_step_s']:.12g}",
              "set wr_singlescale", "set numdgt=16",
              f"wrdata {raw} " + " ".join(SIGNALS), "quit", ".endc", ".end"]
    return "\n".join(lines) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ngspice", type=Path, required=True)
    parser.add_argument("--publication-commit", required=True)
    parser.add_argument("--run", required=True)
    args = parser.parse_args()
    manifest = json.loads((HERE / "manifest.json").read_text())
    run = next(r for r in manifest["runs"] if r["name"] == args.run)
    for relative, expected in manifest["source_sha256"].items():
        assert digest(ROOT / relative) == expected, relative
    assert digest(args.ngspice) == manifest["ngspice_sha256"], "executable changed"
    actual_pdk = subprocess.check_output(["git", "-C", str(ROOT / "pdk"), "rev-parse", "HEAD"], text=True).strip()
    assert actual_pdk == manifest["pdk_commit"], "PDK changed"
    # Require the declared protocol commit to be present and immutable inputs to match it.
    for relative in ("bridge_check/REST_PROTOCOL.md", "bridge_check/manifest.json", "bridge_check/rest_probe.py"):
        archived = subprocess.check_output(["git", "-C", str(ROOT), "show",
                                           f"{args.publication_commit}:research/circuit/{relative}"])
        assert archived == (ROOT / relative).read_bytes(), relative
    out = HERE / "runs" / run["name"]
    out.mkdir(parents=True, exist_ok=False)  # never silently replace a failed or successful draw
    raw = out / "trace.txt"
    circuit = out / "input.spice"
    circuit.write_text(deck(run, raw))
    started = time.time()
    metadata = dict(run=run, publication_commit=args.publication_commit,
                    started_unix=started, deck_sha256=digest(circuit), signals=SIGNALS,
                    ngspice_sha256=digest(args.ngspice), status="running")
    (out / "metadata.json").write_text(json.dumps(metadata, indent=2) + "\n")
    try:
        p = subprocess.run([str(args.ngspice.resolve()), "-b", str(circuit)], cwd=ROOT,
                           capture_output=True, text=True, timeout=600)
        (out / "stdout.log").write_text(p.stdout)
        (out / "stderr.log").write_text(p.stderr)
        metadata.update(returncode=p.returncode, status="produced_trace" if p.returncode == 0 and raw.exists() else "failed")
    except subprocess.TimeoutExpired as exc:
        (out / "stdout.log").write_bytes(exc.stdout or b"")
        (out / "stderr.log").write_bytes(exc.stderr or b"")
        metadata.update(status="timeout")
    finally:
        metadata["finished_unix"] = time.time()
        if raw.exists():
            metadata["raw_sha256"] = digest(raw)
            with raw.open("rb") as src, (out / "trace.txt.gz").open("wb") as dest:
                with gzip.GzipFile(filename="", mode="wb", fileobj=dest, mtime=0) as zipped:
                    for block in iter(lambda: src.read(1024*1024), b""):
                        zipped.write(block)
            raw.unlink()
        (out / "metadata.json").write_text(json.dumps(metadata, indent=2) + "\n")
    print(run["name"], metadata["status"], flush=True)


if __name__ == "__main__":
    main()
