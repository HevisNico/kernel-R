"""Authenticate and replay the preceding composed theorem before using its state."""
from pathlib import Path
import hashlib, json, subprocess, sys, tempfile

ANCHORS = {
    '0.003':'15953bd414f201fcdba7a4e37ac10ef35186ac841088c8dfd711647e2d32d7ef',
    '0.1':'faa093a143073ccb96bad743d1b8a10e1ff2b8a6726f3c11c67b8ace29929edd',
}

def verify_dependency(epsilon, entry_certificate, entry_code, local_certificate, local_code):
    if epsilon not in ANCHORS:
        raise RuntimeError('no published prefix theorem for this box')
    artifact = entry_certificate.read_bytes()
    digest = hashlib.sha256(artifact).hexdigest()
    if digest != ANCHORS[epsilon]:
        raise RuntimeError('entry certificate differs from pinned published theorem')
    document = json.loads(artifact)
    required = {'certify.py','verify.py','tests.py','dependency.py','decimal_intervals.py','integer_intervals.py'}
    if set(document['source_sha256']) != required:
        raise RuntimeError('entry source set differs')
    sources = {}
    for name, want in document['source_sha256'].items():
        data = (entry_code/name).read_bytes()
        if hashlib.sha256(data).hexdigest() != want:
            raise RuntimeError('entry source changed: '+name)
        sources[name] = data
    # The entry check authenticates the older local certificate and all its
    # sources itself, before executing that second checker.
    # Copy authenticated bytes, not the supplied directory. The authenticated
    # entry wrapper applies the same isolation to its local-theorem dependency.
    with tempfile.TemporaryDirectory(prefix='r-entry-replay-') as temporary:
        root = Path(temporary); clean = root/'code'; clean.mkdir()
        for name, data in sources.items(): (clean/name).write_bytes(data)
        pinned = root/'certificate.json'; pinned.write_bytes(artifact)
        bootstrap = 'import runpy,sys; source=sys.argv.pop(1); sys.argv=sys.argv[1:]; sys.path.insert(0,source); runpy.run_path(sys.argv[0],run_name="__main__")'
        result = subprocess.run([sys.executable,'-I','-S','-B','-c',bootstrap,str(clean),str(clean/'verify.py'),
            str(pinned),'--link-certificate',str(local_certificate.resolve()),
            '--link-code',str(local_code.resolve())],cwd=root,capture_output=True,text=True)
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
