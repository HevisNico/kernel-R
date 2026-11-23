"""Enumerate every cascade within: terms <=2 inputs, OR cells <=2 lines, every OR cell receives every line (A<=2),
M<=4 used inputs, B<=2 outputs, no constant outputs, every cell used, outputs distinct, terms an antichain."""
import itertools, json
L="ABCD"
def fn(terms, lines, M):
    rows=[]
    for m in range(2**M):
        x={L[j] for j in range(M) if m>>(M-1-j)&1}   # maskIndex order: input 0 most significant
        rows.append(tuple(int(any(set(terms[a])<=x for a in ls)) for ls in lines))
    return tuple(rows)
out=[]
for M in range(1,5):
    ins=L[:M]
    cand=[frozenset(c) for k in (1,2) for c in itertools.combinations(ins,k)]
    for A in (1,2):
        for T in itertools.combinations(cand,A):
            if any(s<t for s in T for t in T): continue          # antichain (and distinct)
            if set().union(*T)!=set(ins): continue                # every input used
            subsets=[frozenset(s) for k in range(1,A+1) for s in itertools.combinations(range(A),k)]
            for B in (1,2):
                for Ls in itertools.combinations(subsets,B):
                    if set().union(*Ls)!=set(range(A)): continue  # every cell used
                    out.append(dict(M=M,A=A,B=B,terms=[sorted(t) for t in T],lines=[sorted(l) for l in Ls],tt=fn([sorted(t) for t in T],[sorted(l) for l in Ls],M)))
# canonical class under input permutation, cell permutation, output permutation
def canon(e):
    M=e['M']; best=None
    for perm in itertools.permutations(range(M)):
        mp={L[j]:L[perm[j]] for j in range(M)}
        T=[frozenset(mp[v] for v in t) for t in e['terms']]
        outs=sorted(tuple(sorted(tuple(sorted(T[a])) for a in ls)) for ls in e['lines'])
        k=(M,tuple(outs))
        best=k if best is None or k<best else best
    return best
cls={}
for e in out: cls.setdefault(canon(e),[]).append(e)
print(len(out),"labelled cascades (cell order fixed by sorting), ",len(cls),"classes")
for k,v in sorted(cls.items(),key=lambda kv:(len(kv[1][0]['lines']),kv[0][0],kv[0])):
    e=v[0]
    print(k, "labelled:",len(v))
json.dump([dict(key=str(k),n=len(v),ex=v[0]) for k,v in cls.items()],open('classes.json','w'),indent=0)
