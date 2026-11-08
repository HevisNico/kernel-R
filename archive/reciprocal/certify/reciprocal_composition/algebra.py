"""Exact polynomial identities and finite-chain resource/budget instantiation.

The local inequalities do not depend on N. These identities check the algebra
of the written induction; the induction rule itself remains a written proof.
"""
import ast
from fractions import Fraction

VARIABLES=('N','K','j','R')
ZERO=(0,0,0,0)

def add(left,right):
    result=left.copy()
    for power,coefficient in right.items():
        result[power]=result.get(power,0)+coefficient
        if result[power]==0: del result[power]
    return result

def multiply(left,right):
    result={}
    for a,x in left.items():
        for b,y in right.items():
            power=tuple(i+j for i,j in zip(a,b))
            result[power]=result.get(power,0)+x*y
    return {p:c for p,c in result.items() if c}

def normal(expression,substitute_K=False):
    def parse(node):
        if isinstance(node,ast.Constant) and type(node.value) is int:
            return {ZERO:node.value} if node.value else {}
        if isinstance(node,ast.Name) and node.id in VARIABLES:
            if node.id=='K' and substitute_K: return normal('4*N+12+R')
            power=tuple(int(name==node.id) for name in VARIABLES)
            return {power:1}
        if isinstance(node,ast.UnaryOp) and isinstance(node.op,ast.USub):
            return {p:-c for p,c in parse(node.operand).items()}
        if isinstance(node,ast.BinOp):
            left,right=parse(node.left),parse(node.right)
            if isinstance(node.op,ast.Add): return add(left,right)
            if isinstance(node.op,ast.Sub): return add(left,{p:-c for p,c in right.items()})
            if isinstance(node.op,ast.Mult): return multiply(left,right)
        raise ValueError('expression is outside the exact polynomial grammar')
    return parse(ast.parse(expression,mode='eval').body)

def identities():
    statements=[
        ('base_prefix','3+2*0','3',False),
        ('base_tail','K-8-4*0','K-8',False),
        ('prefix_step','3+2*(j+1)','(3+2*j)+2',False),
        ('tail_step','K-8-4*(j+1)','(K-8-4*j)-4',False),
        ('node_outputs','(3+2*j)+(K-8-4*j)','K-5-2*j',False),
        ('remaining_tail','K-8-4*j','8+4*(N-1-j)+R',True),
        ('last_tail','K-8-4*(N-1)','8+R',True),
        ('root_outputs','K-5-2*(N-1)','K-2*N-3',False),
        ('root_outputs_surplus','K-2*N-3','2*N+9+R',True),
        ('traffic_base','1*(K-1-4)','K-5',False),
        ('traffic_step','(N+1)*(K-(N+1)-4)','N*(K-N-4)+(K-5-2*N)',False),
        ('traffic_at_minimum','N*(K-N-4)','3*N*N+8*N+N*R',True),
    ]
    result=[]
    for name,left,right,substitution in statements:
        a,b=normal(left,substitution),normal(right,substitution)
        if a!=b: raise RuntimeError('symbolic identity failed: '+name)
        result.append(dict(name=name,left=left,right=right,substitute_K=substitution,
            normal_form=[dict(powers=list(p),coefficient=c) for p,c in sorted(a.items())]))
    return result

def instantiate(cells,pulses=None,jitter=None):
    if type(cells) is not int or cells<1: raise ValueError('N must be a positive integer')
    minimum=4*cells+12
    if pulses is None: pulses=minimum
    if type(pulses) is not int or pulses<minimum: raise ValueError('source pulses K must be at least 4*N+12')
    if isinstance(jitter,float) or isinstance(jitter,bool): raise TypeError('exact jitter required')
    if jitter is None: sigma=Fraction(0) if cells==1 else min(Fraction(1,20),Fraction(3,20*(cells-1)))
    else: sigma=Fraction(jitter)
    if sigma<0 or sigma>Fraction(1,20): raise ValueError('each link jitter must be in [0,1/20]')
    if cells==1 and sigma: raise ValueError('N=1 has no wire jitter')
    total=(cells-1)*sigma
    if total>Fraction(3,20): raise ValueError('sum of link jitter budgets exceeds 3/20')
    return dict(cells=cells,source_pulses=pulses,independent_physical_parameters=15*cells,
        fixed_link_count=cells-1,per_link_jitter=str(sigma),total_jitter=str(total),
        allowed_fixed_delay_centres=[str(Fraction(3,10)+sigma),str(Fraction(2,5)-sigma)],
        source_period='4',fast_start='160',preparation_sources_per_cell=16,
        root_slow_prefix=2*cells+1,root_fast_tail=pulses-4*cells-4,
        root_total_emissions=pulses-2*cells-3,total_fast_block_emissions=cells*(pulses-cells-4),
        quiescent_by=str(Fraction(160)+4*(pulses-1)+Fraction(11,10)*(cells-1)+8),
        root_probe_before='0/8' if cells==1 else '4/8',root_probe_after='8/8',
        recovery_increment_in_each_cell='1/5',scope='Directed finite chain; no settings copies, live resets or feedback cycles')
