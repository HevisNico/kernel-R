"""Ordinary imports of range derivations with explicit interval input policies.

The three checked-in modules retain the pinned point formulas. tests.py checks
AST parity, allowing only the declared input-policy and zero-disturbance changes.
Pinned point modules are never rewritten or executed in synthetic namespaces.
"""
from pathlib import Path
import hashlib
import sys

ROBUST = Path(__file__).resolve().parents[1]
if str(ROBUST) not in sys.path:
    sys.path.insert(0, str(ROBUST))

from ranges.local_bounds import derive as local_derive
from ranges.birth_bounds import derive as birth_derive
from ranges.latency_bounds import derive as latency_derive

SOURCES = ('birth/local_bounds.py', 'birth/obligations.py', 'latency/obligations.py')


def source_hashes():
    return {name: hashlib.sha256((ROBUST / name).read_bytes()).hexdigest() for name in SOURCES}


def derivations():
    """Return (local, birth, latency) derivations accepting interval nu and alpha."""
    return local_derive, birth_derive, latency_derive
