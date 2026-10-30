"""Pin and independently verify the already published prepared-section theorem."""
from pathlib import Path
import hashlib,json,subprocess,sys

ANCHORS={'0.003': '09ab5bb22dcfe967e8f3bd78c156c45cd7ad6a60c061990370c0ea9c91e06c96', '0.1': '8334b5d0b4110782944405e7e364679f3e7b6bf5f04594e95882f524328c72e1'}


def verify_dependency(epsilon,certificate,code):
    if epsilon not in ANCHORS:raise RuntimeError('no pinned local theorem for this epsilon')
    digest=hashlib.sha256(certificate.read_bytes()).hexdigest()
    if digest!=ANCHORS[epsilon]:raise RuntimeError('local theorem certificate differs from pinned published artifact')
    document=json.loads(certificate.read_text())
    for name,want in document['source_sha256'].items():
        if hashlib.sha256((code/name).read_bytes()).hexdigest()!=want:
            raise RuntimeError('local theorem source identity mismatch: '+name)
    result=subprocess.run([sys.executable,'-E','-B',str((code/'verify.py').resolve()),str(certificate.resolve())],capture_output=True,text=True)
    if result.returncode:raise RuntimeError('local theorem verification refused: '+result.stderr)
    checked=json.loads(result.stdout)
    if checked['status']!='VERIFIED_WITH_INDEPENDENT_INTEGER_ARITHMETIC' or checked['certificate_sha256']!=digest:
        raise RuntimeError('unexpected local checker result')
    return document,dict(certificate_sha256=digest,source_sha256=document['source_sha256'],independent_check=checked)
