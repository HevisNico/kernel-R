"""Create the user's compact, titled English prototype bundle."""
from pathlib import Path
import argparse
import shutil,json,hashlib,zipfile
ROOT=Path(__file__).resolve().parents[2]
SOURCE=Path(__file__).resolve().parent
WORKSPACE=ROOT/'dist'
STAGE=WORKSPACE/'R_Reciprocal_Prototype'
RESULTS=ROOT/'audit_runs'/'reciprocal'


def package(adaptive_results=None):
    WORKSPACE.mkdir(parents=True,exist_ok=True)
    if STAGE.exists():shutil.rmtree(STAGE)
    folders=['01_Guide','02_R_Simulation','03_Visualization','04_Results','05_Verification']
    for folder in folders:(STAGE/folder).mkdir(parents=True,exist_ok=True)
    shutil.copyfile(SOURCE/'README.md',STAGE/'01_Guide'/'README.md')
    shutil.copyfile(SOURCE/'DATA_DICTIONARY.md',STAGE/'01_Guide'/'DATA_DICTIONARY.md')
    shutil.copyfile(ROOT/'LICENSE',STAGE/'01_Guide'/'R_LICENSE.txt')
    shutil.copyfile(ROOT/'LICENSE-docs.md',STAGE/'01_Guide'/'LICENSE_SCOPE.md')
    for name in ['simulate.py','analyse.py','validate.py','engine.py','ode_reference.py','make_viewer.py','viewer_template.html','requirements.txt']:
        shutil.copyfile(SOURCE/name,STAGE/'02_R_Simulation'/name)
    html=(SOURCE/'viewer.html').read_text()
    for url in ['https://unpkg.com/@floating-ui/core@1.7.3/dist/floating-ui.core.umd.min.js','https://unpkg.com/@floating-ui/dom@1.7.4/dist/floating-ui.dom.umd.min.js']:
        html=html.replace(url,'data:text/javascript,')
    (STAGE/'03_Visualization'/'OPEN_IN_BROWSER.html').write_text(html)
    shutil.copyfile(SOURCE/'recorded_viewer_fragment.html',STAGE/'03_Visualization'/'SOURCE_FRAGMENT.html')
    for name in ['plan.json','analysis.json','complet.json','impulsions.json','reglages.json','sans_transfert.json','sans_retour.json','sans_plasticite.json']:
        shutil.copyfile(RESULTS/name,STAGE/'04_Results'/name)
    for name in ['validation.json','interface_validation.json']:
        shutil.copyfile(RESULTS/name,STAGE/'05_Verification'/name)
    (STAGE/'START_HERE.txt').write_text('R RECIPROCAL — THREE CELLS THAT STAY ALIVE AND RELEARN\n\n1. Open 03_Visualization/OPEN_IN_BROWSER.html\n2. Read 01_Guide/README.md for results and limitations.\n3. Runnable code is in 02_R_Simulation.\n4. Recorded observations are in 04_Results.\n5. Checks are in 05_Verification.\n\nThe viewer replays recordings. It does not recompute R.\nHistorical machine identifiers are explained in 01_Guide/DATA_DICTIONARY.md.\n')
    teaching_results=ROOT/'audit_runs'/'teaching'
    if (teaching_results/'summary.json').exists():
        teaching_source=SOURCE/'teaching'
        (STAGE/'02_R_Simulation'/'teaching').mkdir(parents=True,exist_ok=True)
        (STAGE/'06_Learning_To_Teach').mkdir(parents=True,exist_ok=True)
        for name in ['run.py','validate.py']:
            shutil.copyfile(teaching_source/name,STAGE/'02_R_Simulation'/'teaching'/name)
        shutil.copyfile(teaching_source/'README.md',STAGE/'06_Learning_To_Teach'/'README.md')
        shutil.copyfile(teaching_source/'RESULTS.html',STAGE/'06_Learning_To_Teach'/'RESULTS.html')
        for name in ['plan.json','classrooms.json','teachers.json','evaluation.jsonl','summary.json','main_result.json','validation.json']:
            shutil.copyfile(teaching_results/name,STAGE/'06_Learning_To_Teach'/name)
        with (STAGE/'START_HERE.txt').open('a') as guide:
            guide.write('\nLEARNING TO TEACH EXPERIMENT\nOpen 06_Learning_To_Teach/RESULTS.html\nProtocol and limitations: 06_Learning_To_Teach/README.md\n')
    pedagogy_results=ROOT/'audit_runs'/'pedagogy'
    if (pedagogy_results/'validation.json').exists():
        pedagogy_source=SOURCE/'pedagogy'
        source_dir=STAGE/'02_R_Simulation'/'pedagogy'
        source_dir.mkdir(parents=True,exist_ok=True)
        for name in ['run.py','validate.py','report.py']:
            shutil.copyfile(pedagogy_source/name,source_dir/name)
        development=ROOT/'audit_runs'/'pedagogy_development'
        (source_dir/'development').mkdir(parents=True,exist_ok=True)
        for name in ['explore.py','precision.py','curricula.py']:
            shutil.copyfile(development/name,source_dir/'development'/name)
        target=STAGE/'07_Learned_Pedagogy'
        target.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(pedagogy_source/'README.md',target/'README.md')
        for name in ['plan.json','training.json','policies.json','evaluation.json','summary.json','validation.json',
                     'development_grid.json','development_precision.json','development_curricula.json',
                     'pilot_plan.json','pilot_summary.json','RESULTS.html']:
            shutil.copyfile(pedagogy_results/name,target/name)
        with (STAGE/'START_HERE.txt').open('a') as guide:
            guide.write('\nLATEST: LEARNED CURRICULUM SELECTION\nOpen 07_Learned_Pedagogy/RESULTS.html\nFull protocol, added architecture and limits: 07_Learned_Pedagogy/README.md\n')
    adaptive_results=Path(adaptive_results) if adaptive_results is not None else ROOT/'audit_runs'/'adaptive'
    if (adaptive_results/'live_validation.json').exists():
        adaptive_source=SOURCE/'adaptive'
        plan=json.loads((adaptive_results/'plan.json').read_text())
        required={'model.py','run.py','provenance.py','../engine.py','../simulate.py'}
        if plan.get('source_manifest_version')!=2 or set(plan.get('source_sha256',{}))!=required:
            raise RuntimeError('adaptive packaging requires complete source provenance')
        for name,want in plan['source_sha256'].items():
            if hashlib.sha256((adaptive_source/name).read_bytes()).hexdigest()!=want:
                raise RuntimeError('adaptive source identity mismatch: '+name)
        # Packaging copies recorded results; it does not replay their numerical
        # runtime. The two experiment validators require the exact versions.
        runtime=plan.get('runtime_versions',{})
        if set(runtime)!={'python','numpy','scipy'} or not all(isinstance(v,str) and v for v in runtime.values()):
            raise RuntimeError('adaptive runtime provenance is missing')
        validation=json.loads((adaptive_results/'validation.json').read_text())
        live=json.loads((adaptive_results/'live_validation.json').read_text())
        if validation['passed']!=validation['checks'] or not live['passed']:
            raise RuntimeError('adaptive results must pass both validators before packaging')
        source_dir=STAGE/'02_R_Simulation'/'adaptive'
        source_dir.mkdir(parents=True,exist_ok=True)
        for name in ['model.py','run.py','provenance.py','validate.py','live_validate.py','analyze.py','report.py']:
            shutil.copyfile(adaptive_source/name,source_dir/name)
        target=STAGE/'08_Adaptive_Lessons'
        target.mkdir(parents=True,exist_ok=True)
        for name in ['README.md','INVENTION_PROTOCOL.md']:
            shutil.copyfile(adaptive_source/name,target/name)
        for name in ['plan.json','training.json','policies.json','evaluation.json','summary.json','validation.json',
                     'online_validation.json','live_validation.json','POSTHOC_ANALYSIS.json','RESULTS.html']:
            shutil.copyfile(adaptive_results/name,target/name)
        if (adaptive_results/'REPRODUCTION.json').exists():
            shutil.copyfile(adaptive_results/'REPRODUCTION.json',target/'REPRODUCTION.json')
        with (STAGE/'START_HERE.txt').open('a') as guide:
            guide.write('\nLATEST: LEARNED ADAPTATION DURING A LESSON\nOpen 08_Adaptive_Lessons/RESULTS.html\nFull method and boundaries: 08_Adaptive_Lessons/README.md\nProposed next invention test: 08_Adaptive_Lessons/INVENTION_PROTOCOL.md\n')
    certified=ROOT/'results'/'reciprocal_learning'
    if (certified/'eps1e-1'/'independent_check.json').exists():
        target=STAGE/'09_Certified_A_Learns_From_B'
        target.mkdir(parents=True,exist_ok=True)
        for name in ['README.md','RESULTS.html','tests.json','SOURCE_MANIFEST.json']:
            shutil.copyfile(certified/name,target/name)
        shutil.copyfile(ROOT/'proof'/'reciprocal_learning'/'THEOREM.md',target/'THEOREM.md')
        for box in ['eps3e-3','eps1e-1']:
            (target/box).mkdir(parents=True,exist_ok=True)
            for name in ['certificate.json','independent_check.json']:
                shutil.copyfile(certified/box/name,target/box/name)
        (target/'code').mkdir(parents=True,exist_ok=True)
        for name in ['certify.py','verify.py','decimal_intervals.py','integer_intervals.py','tests.py']:
            shutil.copyfile(ROOT/'certify'/'reciprocal_learning'/name,target/'code'/name)
        with (STAGE/'START_HERE.txt').open('a') as guide:
            guide.write('\nLATEST: CERTIFIED LOCAL FEEDBACK LEARNING\nOpen 09_Certified_A_Learns_From_B/RESULTS.html\nFull prepared-section theorem: 09_Certified_A_Learns_From_B/THEOREM.md\nThis folder is the conditional local theorem; folder 10 supplies pulses-only section entry.\n')
    entry=ROOT/'results'/'reciprocal_entry'
    if (entry/'eps1e-1'/'independent_check.json').exists():
        target=STAGE/'10_Certified_Section_Entry'
        target.mkdir(parents=True,exist_ok=True)
        for name in ['README.md','RESULTS.html','tests.json','SOURCE_MANIFEST.json']:
            shutil.copyfile(entry/name,target/name)
        shutil.copyfile(ROOT/'proof'/'reciprocal_entry'/'THEOREM.md',target/'THEOREM.md')
        for box in ['eps3e-3','eps1e-1']:
            (target/box).mkdir(parents=True,exist_ok=True)
            for name in ['certificate.json','independent_check.json']:
                shutil.copyfile(entry/box/name,target/box/name)
        (target/'code').mkdir(parents=True,exist_ok=True)
        for name in ['certify.py','verify.py','tests.py','dependency.py','decimal_intervals.py','integer_intervals.py']:
            shutil.copyfile(ROOT/'certify'/'reciprocal_entry'/name,target/'code'/name)
        with (STAGE/'START_HERE.txt').open('a') as guide:
            guide.write('\nLATEST: BIRTH-TO-SECTION ENTRY AND COMPOSED FEEDBACK LEARNING\nOpen 10_Certified_Section_Entry/RESULTS.html\nComplete proof: 10_Certified_Section_Entry/THEOREM.md\nScope: pulses-only READY birth family through 459.9; settings copies and later phases remain separate.\n')
    cadence=ROOT/'results'/'reciprocal_cadence'
    if (cadence/'eps1e-1'/'independent_check.json').exists():
        target=STAGE/'11_Certified_Cadence_Cascade'
        target.mkdir(parents=True,exist_ok=True)
        for name in ['README.md','RESULTS.html','tests.json','SOURCE_MANIFEST.json']:
            shutil.copyfile(cadence/name,target/name)
        for name in ['README.md','RESULTS.html']:
            page=target/name
            page.write_text(page.read_text().replace('../../proof/reciprocal_cadence/THEOREM.md','THEOREM.md'))
        shutil.copyfile(ROOT/'proof'/'reciprocal_cadence'/'THEOREM.md',target/'THEOREM.md')
        for box in ['eps3e-3','eps1e-1']:
            (target/box).mkdir(parents=True,exist_ok=True)
            for name in ['certificate.json','independent_check.json']:
                shutil.copyfile(cadence/box/name,target/box/name)
        (target/'code').mkdir(parents=True,exist_ok=True)
        for name in ['certify.py','verify.py','tests.py','dependency.py','decimal_intervals.py','integer_intervals.py']:
            shutil.copyfile(ROOT/'certify'/'reciprocal_cadence'/name,target/'code'/name)
        with (STAGE/'START_HERE.txt').open('a') as guide:
            guide.write('\nLATEST: CERTIFIED C-TO-B-TO-A CADENCE CASCADE\nOpen 11_Certified_Cadence_Cascade/RESULTS.html\nComplete proof: 11_Certified_Cadence_Cascade/THEOREM.md\nRun: python -B 11_Certified_Cadence_Cascade/code/tests.py\nScope: pulses-only birth family through 789.9; 45 physical parameters, no settings copies or open recurrence.\n')
    composition=ROOT/'results'/'reciprocal_composition'
    if (composition/'eps1e-1'/'independent_check.json').exists():
        target=STAGE/'12_Certified_N_Cell_Composition'
        target.mkdir(parents=True,exist_ok=True)
        for name in ['README.md','RESULTS.html','tests.json','SOURCE_MANIFEST.json','instances.json','numerical_checks.json']:
            shutil.copyfile(composition/name,target/name)
        for name in ['README.md','RESULTS.html']:
            page=target/name
            page.write_text(page.read_text().replace('../../proof/reciprocal_composition/THEOREM.md','THEOREM.md'))
        shutil.copyfile(ROOT/'proof/reciprocal_composition/THEOREM.md',target/'THEOREM.md')
        for box in ['eps3e-3','eps1e-1']:
            (target/box).mkdir(parents=True,exist_ok=True)
            for name in ['certificate.json','independent_check.json']:
                shutil.copyfile(composition/box/name,target/box/name)
        (target/'code').mkdir(parents=True,exist_ok=True)
        for name in ['certify.py','verify.py','tests.py','dependency.py','algebra.py','decimal_intervals.py','integer_intervals.py']:
            shutil.copyfile(ROOT/'certify/reciprocal_composition'/name,target/'code'/name)
        (STAGE/'02_R_Simulation/composition').mkdir(parents=True,exist_ok=True)
        shutil.copyfile(ROOT/'experiments/composition/run.py',STAGE/'02_R_Simulation/composition/run.py')
        with (STAGE/'START_HERE.txt').open('a') as guide:
            guide.write('\nLATEST: EVERY FINITE CHAIN BY COMPOSITION\nOpen 12_Certified_N_Cell_Composition/RESULTS.html\nComplete written induction: 12_Certified_N_Cell_Composition/THEOREM.md\nRun: python -B 12_Certified_N_Cell_Composition/code/tests.py\nScope: directed finite chains, K>=4*N+12 source pulses, summed link jitter<=0.15; not arbitrary graphs or cycles.\n')
    files=[p for p in STAGE.rglob('*') if p.is_file() and p.name!='SHA256SUMS.json']
    manifest={str(p.relative_to(STAGE)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
    (STAGE/'05_Verification'/'SHA256SUMS.json').write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
    dest=WORKSPACE/'R_Reciprocal_Prototype.zip'
    with zipfile.ZipFile(dest,'w',zipfile.ZIP_DEFLATED,compresslevel=9) as z:
        for p in sorted(STAGE.rglob('*')):
            if p.is_file():z.write(p,str(Path(STAGE.name)/p.relative_to(STAGE)))
    assert dest.stat().st_size<30_000_000
    with zipfile.ZipFile(dest) as z:
        assert z.testzip() is None
        assert len(z.namelist())==len(files)+1
        for name,want in manifest.items():assert hashlib.sha256(z.read(str(Path(STAGE.name)/name))).hexdigest()==want
    print(json.dumps(dict(file=str(dest),bytes=dest.stat().st_size,files=len(files)+1,limit_bytes=30_000_000,sha256=hashlib.sha256(dest.read_bytes()).hexdigest()),indent=2))
    return dest
if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--adaptive-results',type=Path)
    package(parser.parse_args().adaptive_results)
