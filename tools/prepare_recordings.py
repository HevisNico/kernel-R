"""Restore recorded experiment inputs from the pinned, self-contained prototype ZIP."""
from pathlib import Path,PurePosixPath
import argparse,hashlib,json,stat,zipfile

ROOT=Path(__file__).resolve().parents[1]
BUNDLE=ROOT/'downloads'/'R_Reciprocal_Prototype.zip'
BUNDLE_SHA256='5a48e26b4eb0696e3ce546c4e4f0c5de487680aa1627e776b40d524f0437cfa6'
PREFIX='R_Reciprocal_Prototype/'


def verify_bundle():
    if hashlib.sha256(BUNDLE.read_bytes()).hexdigest()!=BUNDLE_SHA256:
        raise RuntimeError('prototype bundle identity differs from the pinned research snapshot')
    with zipfile.ZipFile(BUNDLE) as archive:
        names=archive.namelist()
        if len(names)!=len(set(names)) or archive.testzip() is not None:
            raise RuntimeError('duplicate or corrupt bundle entries')
        manifest_name=PREFIX+'05_Verification/SHA256SUMS.json'
        manifest=json.loads(archive.read(manifest_name))
        if set(names)!={PREFIX+name for name in manifest}|{manifest_name}:
            raise RuntimeError('bundle manifest does not cover all entries')
        data={}
        for info in archive.infolist():
            path=PurePosixPath(info.filename)
            if path.is_absolute() or '..' in path.parts or not info.filename.startswith(PREFIX):
                raise RuntimeError('unsafe bundle path')
            if stat.S_IFMT(info.external_attr>>16)==stat.S_IFLNK:
                raise RuntimeError('bundle symlinks are forbidden')
            relative=info.filename[len(PREFIX):]
            contents=archive.read(info)
            if info.filename!=manifest_name and hashlib.sha256(contents).hexdigest()!=manifest[relative]:
                raise RuntimeError('bundle hash mismatch: '+relative)
            data[relative]=contents
    return data


def restoration_plan(data):
    files={}
    for name,content in data.items():
        path=PurePosixPath(name);folder=path.parts[0];filename=path.name
        destinations=[]
        if folder=='04_Results' and path.suffix=='.json':destinations.append('audit_runs/reciprocal/'+filename)
        elif folder=='05_Verification' and filename in ['validation.json','interface_validation.json']:
            destinations.append('audit_runs/reciprocal/'+filename)
        elif folder=='06_Learning_To_Teach' and path.suffix in ['.json','.jsonl']:
            destinations.append('audit_runs/teaching/'+filename)
        elif folder=='07_Learned_Pedagogy' and path.suffix in ['.json','.jsonl','.html','.md']:
            destinations.append('audit_runs/pedagogy/'+filename)
            if filename.startswith('development_'):
                destinations.append('audit_runs/pedagogy_development/'+filename.removeprefix('development_'))
            if filename.startswith('pilot_'):
                destinations.append('audit_runs/pedagogy_pilot/'+filename.removeprefix('pilot_'))
        elif folder=='08_Adaptive_Lessons' and path.suffix in ['.json','.jsonl','.html','.md']:
            destinations.append('audit_runs/adaptive/'+filename)
            if filename in ['development_prefixes.json','development_blocks.json','development_preferences.json']:
                destinations.append('audit_runs/adaptive_development/'+filename.removeprefix('development_'))
        elif name=='08_Adaptive_Lessons/development_training_abort.log':
            destinations.append('audit_runs/adaptive.log')
        elif name.startswith('02_R_Simulation/pedagogy/development/') and path.suffix=='.py':
            destinations.append('audit_runs/pedagogy_development/'+filename)
        for destination in destinations:
            if destination in files and files[destination]!=content:raise RuntimeError('conflicting restoration path')
            files[destination]=content
    return files


def restore():
    files=restoration_plan(verify_bundle())
    # Check every destination before writing anything; never overwrite different local work.
    for relative,content in files.items():
        target=ROOT/relative
        if not target.resolve().is_relative_to(ROOT.resolve()):raise RuntimeError('unsafe restoration destination')
        if target.exists() and (not target.is_file() or target.read_bytes()!=content):
            raise RuntimeError('existing output differs; preserve or move it first: '+relative)
    created=0
    for relative,content in files.items():
        target=ROOT/relative
        if target.exists():continue
        target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(content);created+=1
    return dict(restored=created,available=len(files),archive_sha256=BUNDLE_SHA256)

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--verify-only',action='store_true');args=parser.parse_args()
    print(json.dumps(dict(bundle_files=len(verify_bundle()),verified=True) if args.verify_only else restore()))
