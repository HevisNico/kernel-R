"""Authenticate and replay the preceding composed theorem before using its state."""
from pathlib import Path
import hashlib, json, subprocess, sys

ANCHORS = {
    '0.003':'50fa4ae306d62e8ec13f90bd20779aa6d1a51636e3f2dd3dc0c07215ed9f716e',
    '0.1':'db7ab2d38d56504446bca019f0f17c298507123009e50b82831d4ab570d703c1',
}

def verify_dependency(epsilon, entry_certificate, entry_code, local_certificate, local_code):
    if epsilon not in ANCHORS:
        raise RuntimeError('no published prefix theorem for this box')
    digest = hashlib.sha256(entry_certificate.read_bytes()).hexdigest()
    if digest != ANCHORS[epsilon]:
        raise RuntimeError('entry certificate differs from pinned published theorem')
    document = json.loads(entry_certificate.read_text())
    required = {'certify.py','verify.py','tests.py','dependency.py','decimal_intervals.py','integer_intervals.py'}
    if set(document['source_sha256']) != required:
        raise RuntimeError('entry source set differs')
    for name, want in document['source_sha256'].items():
        if hashlib.sha256((entry_code/name).read_bytes()).hexdigest() != want:
            raise RuntimeError('entry source changed: '+name)
    # The entry check authenticates the older local certificate and all its
    # sources itself, before executing that second checker.
    result = subprocess.run([sys.executable,'-E','-B',str((entry_code/'verify.py').resolve()),
        str(entry_certificate.resolve()),'--link-certificate',str(local_certificate.resolve()),
        '--link-code',str(local_code.resolve())],capture_output=True,text=True)
    if result.returncode:
        raise RuntimeError('prefix replay refused: '+result.stderr)
    checked = json.loads(result.stdout)
    if checked['status'] != 'VERIFIED_ENTRY_AND_COMPOSITION_WITH_INTEGER_ARITHMETIC' or checked['certificate_sha256'] != digest:
        raise RuntimeError('unexpected prefix checker response')
    return dict(certificate_sha256=digest,source_sha256=document['source_sha256'],independent_check=checked)

def arguments(parser):
    parser.add_argument('--entry-certificate',required=True,type=Path)
    parser.add_argument('--entry-code',required=True,type=Path)
    parser.add_argument('--local-certificate',required=True,type=Path)
    parser.add_argument('--local-code',required=True,type=Path)

def replay(epsilon, args):
    return verify_dependency(epsilon,args.entry_certificate,args.entry_code,args.local_certificate,args.local_code)
