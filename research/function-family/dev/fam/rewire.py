"""Every map of the four first-layer ports (a1,a2,b1,b2) to inputs, c selecting both lines. Which give a valid
first layer (targets incomparable and distinct, every input used), and which class each gives."""
import itertools
L="ABCD"
seen={}; bad={}
for M in range(1,5):
    for phi in itertools.product(range(M),repeat=4):
        if set(phi)!=set(range(M)): continue
        Ta=frozenset(L[j] for j in phi[:2]); Tb=frozenset(L[j] for j in phi[2:])
        key=None
        ok = not (Ta<=Tb or Tb<=Ta)
        # class up to renaming: sizes and overlap
        cls=(len(Ta),len(Tb),len(Ta&Tb)) if len(Ta)>=len(Tb) else (len(Tb),len(Ta),len(Ta&Tb))
        (seen if ok else bad).setdefault(cls,0)
        if ok: seen[cls]+=1
        else: bad[cls]+=1
print("valid classes (|Ta|,|Tb|,|overlap|): maps", seen)
print("refused by reachable/antichain:", bad)
