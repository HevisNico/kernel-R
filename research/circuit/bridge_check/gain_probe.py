"""Independent DC mirror calibration on a publicly frozen finite grid."""
import argparse
import gzip
import hashlib
import json
import math
import os
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent


def digest(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def deck(run, out):
    return f'''* Frozen nominal READY mirror calibration
.lib "pdk/models/sky130.lib.spice" tt
.option scale=1e-6 reltol=1e-4 abstol=1e-13 vntol=1e-7 gmin=1e-16
.option temp={run['temperature_C']}
vdd vdd 0 1.8
vcm vcm 0 0.4
vstore vmem 0 0.35
vqhold vq 0 {run['vq_V']}
vdump vr0 0 1.25
vadm adm 0 1.8
vadmb admb 0 0
istim vdd gm {run['input_A']:.17g}
xmin gm gm vcm 0 sky130_fd_pr__nfet_01v8 w=40 l=2.5
xmout dq gm vmem 0 sky130_fd_pr__nfet_01v8 w=40 l=2.5
xms1 dq adm vq 0 sky130_fd_pr__nfet_01v8 w=1 l=0.15
xms2 dq admb vr0 0 sky130_fd_pr__nfet_01v8 w=1 l=0.15
.save v(vmem) i(vqhold)
.control
dc vstore 0.35 0.42 0.0005
set wr_singlescale
set numdgt=16
wrdata {out} v(vmem) i(vqhold)
quit
.endc
.end
'''


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--ngspice', type=Path, required=True)
    p.add_argument('--tmpfile-adapter', type=Path, required=True)
    p.add_argument('--tmpdir', type=Path, required=True)
    p.add_argument('--publication-commit', required=True)
    args = p.parse_args()
    manifest = json.loads((HERE/'gain_manifest.json').read_text())
    for rel, expected in manifest['source_sha256'].items():
        assert digest(ROOT/rel) == expected, rel
    for rel in ('GAIN_PROTOCOL.md','gain_manifest.json','gain_probe.py','gain_analyze.py'):
        old = subprocess.check_output(['git','-C',str(ROOT),'show',
            f'{args.publication_commit}:research/circuit/bridge_check/{rel}'])
        assert old == (HERE/rel).read_bytes(), rel
    assert digest(args.ngspice) == manifest['ngspice_sha256']
    assert digest(args.tmpfile_adapter) == manifest['tmpfile_adapter_sha256']
    assert subprocess.check_output(['git','-C',str(ROOT/'pdk'),'rev-parse','HEAD'],text=True).strip() == manifest['pdk_commit']
    assert (ROOT/'.spiceinit').read_bytes() == (ROOT/'spiceinit.txt').read_bytes()
    args.tmpdir.mkdir(parents=True,exist_ok=True)
    env=dict(os.environ,TMPDIR=str(args.tmpdir.resolve()),LD_PRELOAD=str(args.tmpfile_adapter.resolve()),SPICE_SCRIPTS=str(HERE/'runtime'))
    for run in manifest['runs']:
        out=HERE/'gain_runs'/run['name']
        out.mkdir(parents=True,exist_ok=False)
        circuit=out/'input.spice'; raw=out/'dc.txt'
        circuit.write_text(deck(run,raw))
        meta=dict(run=run,publication_commit=args.publication_commit,started_unix=time.time(),deck_sha256=digest(circuit),status='running')
        (out/'metadata.json').write_text(json.dumps(meta,indent=2)+'\n')
        try:
            result=subprocess.run([str(args.ngspice.resolve()),'-b',str(circuit)],cwd=ROOT,env=env,capture_output=True,text=True,timeout=120)
            (out/'stdout.log').write_text(result.stdout);(out/'stderr.log').write_text(result.stderr)
            meta.update(returncode=result.returncode,status='produced_trace' if result.returncode==0 and raw.exists() else 'failed')
        except subprocess.TimeoutExpired as exc:
            (out/'stdout.log').write_bytes(exc.stdout or b'');(out/'stderr.log').write_bytes(exc.stderr or b'')
            meta['status']='timeout'
        finally:
            meta['finished_unix']=time.time()
            if raw.exists():
                meta['raw_sha256']=digest(raw)
                with (out/'dc.txt.gz').open('wb') as dest:
                    with gzip.GzipFile(filename='',mode='wb',fileobj=dest,mtime=0) as zipped:
                        zipped.write(raw.read_bytes())
                raw.unlink()
            (out/'metadata.json').write_text(json.dumps(meta,indent=2)+'\n')
        print(run['name'],meta['status'],flush=True)


if __name__ == '__main__':
    main()
