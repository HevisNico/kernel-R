"""Reproduce pinned exploratory evidence; never generates registered v5 cases."""
from pathlib import Path
import tempfile
import unittest
from reproduce import generate,verify,manifest


class ReproductionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp=tempfile.TemporaryDirectory()
        cls.output=Path(cls.temp.name)/'traces'
        cls.count=generate(cls.output)

    @classmethod
    def tearDownClass(cls):
        cls.temp.cleanup()

    def test_all_published_trace_fingerprints(self):
        self.assertEqual(self.count,50)
        self.assertEqual(verify(self.output),50)

    def test_byte_change_is_rejected(self):
        path=self.output/next(iter(manifest()))
        original=path.read_bytes()
        try:
            path.write_bytes(original+b'\n')
            with self.assertRaisesRegex(ValueError,'SHA-256 mismatch'):
                verify(self.output)
        finally:
            path.write_bytes(original)

    def test_missing_file_is_rejected(self):
        path=self.output/next(iter(manifest()))
        original=path.read_bytes()
        try:
            path.unlink()
            with self.assertRaisesRegex(ValueError,'Missing or unexpected'):
                verify(self.output)
        finally:
            path.write_bytes(original)

    def test_extra_file_is_rejected(self):
        path=self.output/'extra.txt'
        try:
            path.write_text('unexpected')
            with self.assertRaisesRegex(ValueError,'Missing or unexpected'):
                verify(self.output)
        finally:
            path.unlink()


if __name__=='__main__':
    unittest.main()
