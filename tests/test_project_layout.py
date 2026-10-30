"""Keep the focused research checkout, certificate identities and bundle usable."""
from pathlib import Path
import hashlib,importlib.util,json,re,unittest

ROOT=Path(__file__).resolve().parents[1]

class ProjectLayout(unittest.TestCase):
    def test_proof_source_manifests_match(self):
        for result in ['reciprocal_learning','reciprocal_entry','reciprocal_cadence']:
            manifest=json.loads((ROOT/'results'/result/'SOURCE_MANIFEST.json').read_text())
            for name,want in manifest['files'].items():
                with self.subTest(path=name):self.assertEqual(hashlib.sha256((ROOT/name).read_bytes()).hexdigest(),want)
    def test_maintained_project_markdown_links_resolve(self):
        paths=[ROOT/'README.md',ROOT/'docs/PROVENANCE.md']
        for folder in ['experiments/reciprocal','proof','results']:
            paths.extend((ROOT/folder).rglob('*.md'))
        for path in paths:
            for target in re.findall(r'\]\(([^)]+)\)',path.read_text()):
                if re.match(r'\w+://|#|mailto:',target):continue
                target=target.split('#')[0]
                if target:
                    with self.subTest(file=path.relative_to(ROOT),target=target):self.assertTrue((path.parent/target).exists())
    def test_bundle_is_complete_and_contains_required_recordings(self):
        spec=importlib.util.spec_from_file_location('recordings',ROOT/'tools/prepare_recordings.py')
        module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
        files=module.restoration_plan(module.verify_bundle())
        for name in ['audit_runs/reciprocal/impulsions.json','audit_runs/teaching/summary.json',
          'audit_runs/pedagogy/evaluation.json','audit_runs/adaptive/live_validation.json',
          'audit_runs/pedagogy_development/explore.py','audit_runs/adaptive.log']:
            self.assertIn(name,files)
        self.assertLess(module.BUNDLE.stat().st_size,30_000_000)

if __name__=='__main__':unittest.main()
