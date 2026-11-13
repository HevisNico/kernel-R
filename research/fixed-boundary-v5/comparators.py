"""Frozen finite-family hindsight comparators; no registered input is generated."""
import importlib.util
from common import ROOT,H


def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    obj=importlib.util.module_from_spec(spec)
    import sys
    sys.modules[name]=obj
    spec.loader.exec_module(obj)
    return obj


import sys
sys.path.insert(0,str(ROOT.parent/'boundary-cost-study'))

STUDY=module('v5_frozen_study',ROOT.parent/'boundary-cost-study/study.py')
FORWARD=module('v5_frozen_forward',ROOT.parent/'boundary-cost-study/test_study.py')


def compare(scenario):
    rates,errors=scenario['rates'],scenario['reserve_errors']
    n=len(rates)-1
    backward=STUDY.oracle(H,n,rates.__getitem__,errors.__getitem__)
    forward=FORWARD.forward_optimum(H,n,rates.__getitem__,errors.__getitem__)
    return dict(backward=backward,forward_cost=forward)
