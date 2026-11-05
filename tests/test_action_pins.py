"""Keep third-party CI execution tied to reviewed immutable commits."""
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]


class ActionPins(unittest.TestCase):
    def test_external_workflow_actions_use_full_commit_ids(self):
        for path in (ROOT / '.github/workflows').glob('*.yml'):
            for reference in re.findall(r'^\s*-?\s*uses:\s*(\S+)', path.read_text(), re.M):
                if reference.startswith('./'):
                    continue
                with self.subTest(workflow=path.name, action=reference):
                    self.assertRegex(reference, r'^[^@\s]+@[0-9a-f]{40}$')


if __name__ == '__main__':
    unittest.main()
