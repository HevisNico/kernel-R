"""Pin and independently verify the already published prepared-section theorem."""
from pathlib import Path
import hashlib,json,subprocess,sys,tempfile

ANCHORS={'0.003': '09ab5bb22dcfe967e8f3bd78c156c45cd7ad6a60c061990370c0ea9c91e06c96', '0.1': '8334b5d0b4110782944405e7e364679f3e7b6bf5f04594e95882f524328c72e1'}


def verify_dependency(epsilon,certificate,code):
    if epsilon not in ANCHORS:raise RuntimeError('no pinned local theorem for this epsilon')
    artifact=certificate.read_bytes()
    digest=hashlib.sha256(artifact).hexdigest()
    if digest!=ANCHORS[epsilon]:raise RuntimeError('local theorem certificate differs from pinned published artifact')
    document=json.loads(artifact)
    required={'certify.py','verify.py','tests.py','decimal_intervals.py','integer_intervals.py'}
    if set(document['source_sha256'])!=required:raise RuntimeError('local source set differs')
    sources={}
    for name,want in document['source_sha256'].items():
        data=(code/name).read_bytes()
        if hashlib.sha256(data).hexdigest()!=want:
            raise RuntimeError('local theorem source identity mismatch: '+name)
        sources[name]=data
    # Execute the exact bytes just authenticated. Never put the caller's code
    # directory, extra modules, packages or bytecode caches on the import path.
    with tempfile.TemporaryDirectory(prefix='r-local-replay-') as temporary:
        root=Path(temporary);clean=root/'code';clean.mkdir()
        for name,data in sources.items():(clean/name).write_bytes(data)
        pinned=root/'certificate.json';pinned.write_bytes(artifact)
        bootstrap='import runpy,sys; source=sys.argv.pop(1); sys.argv=sys.argv[1:]; sys.path.insert(0,source); runpy.run_path(sys.argv[0],run_name="__main__")'
        result=subprocess.run([sys.executable,'-I','-S','-B','-c',bootstrap,str(clean),str(clean/'verify.py'),str(pinned)],
            cwd=root,capture_output=True,text=True)
    if result.returncode:raise RuntimeError('local theorem verification refused: '+result.stderr)
    checked=json.loads(result.stdout)
    if checked['status']!='VERIFIED_WITH_INDEPENDENT_INTEGER_ARITHMETIC' or checked['certificate_sha256']!=digest:
        raise RuntimeError('unexpected local checker result')
    return document,dict(certificate_sha256=digest,source_sha256=document['source_sha256'],independent_check=checked)
