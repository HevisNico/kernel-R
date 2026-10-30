"""Load the pinned robust derivations with parameter ranges allowed.

The local, birth and latency derivations of research/robust require the noise bound nu and
the amplitude deviation alpha to be exact numbers. Every formula in them is an interval
expression, so evaluating it with nu and alpha as intervals encloses its value for every nu
and alpha in those intervals. Only the exactness checks, and one branch that tests nu.lo and
alpha.lo for the zero-disturbance case, assume point parameters.

This loader reads the pinned sources unchanged and applies the textual patches below, each
checked by its exact number of occurrences, then executes the patched code in private module
namespaces. Nothing in research/robust is modified, so the published point certificates and
the generated Lean evidence keep their source hashes. ranges/tests.py checks that zero-width
ranges reproduce every published point certificate.
"""
from pathlib import Path
import hashlib
import sys
import types

ROBUST = Path(__file__).resolve().parents[1]
if str(ROBUST) not in sys.path:
    sys.path.insert(0, str(ROBUST))

LOCAL_OLD = """    for name, x in (('epsilon', eps), ('nu', nu), ('alpha', alpha), ('Q', Q)):
        require(x.lo == x.hi, name + ' must be exact')
    require(0 < eps.lo < 1 and nu.lo >= 0 and 0 <= alpha.lo < 1 and Q.lo > 0, 'parameter range')
"""
LOCAL_NEW = """    for name, x in (('epsilon', eps), ('Q', Q)):
        require(x.lo == x.hi, name + ' must be exact')
    require(0 < eps.lo < 1 and nu.lo >= 0 and 0 <= alpha.lo and alpha.hi < 1 and Q.lo > 0, 'parameter range')
"""
BIRTH_OLD = "require(eps.lo==eps.hi and nu.lo==nu.hi and 0<eps.lo<1 and nu.lo>=0,'parameter range')"
BIRTH_NEW = "require(eps.lo==eps.hi and 0<eps.lo<1 and nu.lo>=0,'parameter range')"
LATENCY_OLD_EXACT = "require(all(x.lo==x.hi for x in (nu,alpha,d,low,high)),'exact latency parameters required')"
LATENCY_NEW_EXACT = "require(all(x.lo==x.hi for x in (d,low,high)),'exact latency parameters required')"
LATENCY_OLD_ZERO = "if nu.lo==0 and alpha.lo==0:"
LATENCY_NEW_ZERO = "if nu.hi==0 and alpha.hi==0:"

# (pinned source, [(old, new, expected count)], imports replaced by injected names)
PATCHES = {
    'birth/local_bounds.py': [(LOCAL_OLD, LOCAL_NEW, 1)],
    'birth/obligations.py': [(BIRTH_OLD, BIRTH_NEW, 1),
                             ('from birth.local_bounds import derive as local_derive\n', '', 1)],
    'latency/obligations.py': [(LATENCY_OLD_EXACT, LATENCY_NEW_EXACT, 1),
                               (LATENCY_OLD_ZERO, LATENCY_NEW_ZERO, 1),
                               ('from birth.obligations import derive as birth_derive\n', '', 1)],
}
SOURCES = tuple(PATCHES)


class PatchError(RuntimeError):
    pass


def source_hashes():
    return {name: hashlib.sha256((ROBUST / name).read_bytes()).hexdigest() for name in SOURCES}


def _module(name, inject):
    text = (ROBUST / name).read_text()
    for old, new, count in PATCHES[name]:
        if text.count(old) != count:
            raise PatchError(f'{name}: expected {count} occurrence(s) of a patched line')
        text = text.replace(old, new)
    module = types.ModuleType('ranges_' + name.replace('/', '_')[:-3])
    module.__file__ = str(ROBUST / name)
    module.__dict__.update(inject)
    exec(compile(text, str(ROBUST / name), 'exec'), module.__dict__)
    return module


def derivations():
    """Return (local_derive, birth_derive, latency_derive) accepting interval nu and alpha."""
    local = _module('birth/local_bounds.py', {})
    birth = _module('birth/obligations.py', {'local_derive': local.derive})
    latency = _module('latency/obligations.py', {'birth_derive': birth.derive})
    return local.derive, birth.derive, latency.derive
