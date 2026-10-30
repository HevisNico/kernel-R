"""Independent fixed-point intervals using Python integers only.

All operations round outwards on the grid 10^-70. exp uses its positive Taylor
series plus an explicit geometric tail; ln uses the atanh series plus its tail.
No Decimal, float, libmpdec, numpy, scipy or inherited interval code is imported.
"""
from fractions import Fraction

SCALE=10**70
EXP_TERMS=160
LOG_TERMS=256


def floor_ratio(n,d):
    if d<=0:raise ValueError('positive denominator required')
    return n//d


def ceil_ratio(n,d):return -floor_ratio(-n,d)


class Q:
    __slots__=('l','u')
    def __init__(self,a=0,b=None):
        if isinstance(a,Q):
            if b is not None:raise TypeError('second endpoint with Q')
            self.l,self.u=a.l,a.u;return
        if isinstance(a,float) or isinstance(b,float):raise TypeError('float endpoints forbidden')
        low=Fraction(a);high=Fraction(a if b is None else b)
        if low>high:raise ValueError('reversed interval')
        self.l=floor_ratio(low.numerator*SCALE,low.denominator)
        self.u=ceil_ratio(high.numerator*SCALE,high.denominator)
    @classmethod
    def raw(cls,l,u):
        if l>u:raise ValueError('reversed raw interval')
        obj=object.__new__(cls);obj.l=l;obj.u=u;return obj
    @property
    def lo(self):return Fraction(self.l,SCALE)
    @property
    def hi(self):return Fraction(self.u,SCALE)
    def __add__(self,o):
        o=Q(o);return Q.raw(self.l+o.l,self.u+o.u)
    __radd__=__add__
    def __neg__(self):return Q.raw(-self.u,-self.l)
    def __sub__(self,o):return self+-Q(o)
    def __rsub__(self,o):return Q(o)+-self
    def __mul__(self,o):
        o=Q(o);products=[a*b for a in (self.l,self.u) for b in (o.l,o.u)]
        return Q.raw(floor_ratio(min(products),SCALE),ceil_ratio(max(products),SCALE))
    __rmul__=__mul__
    def __truediv__(self,o):
        o=Q(o)
        if o.l<=0<=o.u:raise ZeroDivisionError('interval contains zero')
        if o.u<0:return (-self)/(-o)
        reciprocal=Q.raw(floor_ratio(SCALE*SCALE,o.u),ceil_ratio(SCALE*SCALE,o.l))
        return self*reciprocal
    def __rtruediv__(self,o):return Q(o)/self
    def exp(self):
        left=_exp_point(self.l);right=_exp_point(self.u)
        return Q.raw(left.l,right.u)
    def ln(self):
        if self.l<=0:raise ValueError('ln domain')
        left=_ln_point(self.l);right=_ln_point(self.u)
        return Q.raw(left.l,right.u)


def _exp_point(p):
    if p==0:return Q(1)
    if p<0:return Q(1)/_exp_point(-p)
    if p>16*SCALE:raise ValueError('exp input exceeds verified series range')
    x=Q.raw(p,p);term=Q(1);total=Q(1)
    for n in range(1,EXP_TERMS+1):
        term=term*x/n;total=total+term
    next_term=term*x/(EXP_TERMS+1)
    tail=next_term/(1-x/(EXP_TERMS+2))
    return Q.raw(total.l,total.u+tail.u)


def _ln_point(p):
    if p==SCALE:return Q(0)
    if p<=0:raise ValueError('ln domain')
    x=Q.raw(p,p);v=(x-1)/(x+1);square=v*v
    if square.u>=SCALE:raise ValueError('log tail denominator not separated from zero')
    power=Q(v);total=Q(0)
    for k in range(LOG_TERMS):
        total=total+power/(2*k+1);power=power*square
    magnitude=-power if p<SCALE else power
    tail=2*magnitude/((2*LOG_TERMS+1)*(1-square))
    result=2*total
    return Q.raw(result.l-tail.u,result.u) if p<SCALE else Q.raw(result.l,result.u+tail.u)
