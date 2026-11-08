"""Complete source/runtime identity for new adaptive runs.

Historical two-file plans are intentionally not promoted to complete provenance.
This records identity, not a proof that a result was produced by these sources.
"""
from pathlib import Path
import hashlib
import platform
import numpy as np
import scipy

HERE = Path(__file__).resolve().parent
SOURCES = ('model.py', 'run.py', 'provenance.py', '../engine.py', '../simulate.py')


def capture(here=HERE):
    return dict(source_manifest_version=2,
                source_sha256={name: hashlib.sha256((here / name).read_bytes()).hexdigest()
                               for name in SOURCES},
                runtime_versions=dict(python=platform.python_version(), numpy=np.__version__,
                                      scipy=scipy.__version__))


def verify(plan, here=HERE):
    if plan.get('source_manifest_version') != 2:
        raise RuntimeError('incomplete legacy provenance: a fresh run with the full source/runtime manifest is required')
    if not isinstance(plan.get('source_sha256'), dict) or set(plan['source_sha256']) != set(SOURCES):
        raise RuntimeError('source manifest must cover the adaptive code and both simulation engines')
    current = capture(here)
    for name in SOURCES:
        if plan['source_sha256'][name] != current['source_sha256'][name]:
            raise RuntimeError('locked source identity mismatch: ' + name)
    if plan.get('runtime_versions') != current['runtime_versions']:
        raise RuntimeError('locked numerical runtime mismatch: Python/NumPy/SciPy versions must match')
    return current
