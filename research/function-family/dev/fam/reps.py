import itertools
L="ABCD"
REPS=[ # id, M, terms, lines  (representatives chosen to match the repo's names)
("F1",4,[["A","B"],["C","D"]],[[0,1]]),
("F2",3,[["A","B"],["B","C"]],[[0,1]]),
("F3",3,[["A","B"],["C"]],[[0,1]]),
("F4",2,[["A"],["B"]],[[0,1]]),
("X1",1,[["A"]],[[0]]),
("X2",2,[["A","B"]],[[0]]),
("D1",4,[["A","B"],["C","D"]],[[0],[1]]),
("D2",4,[["A","B"],["C","D"]],[[0],[0,1]]),
("D3",3,[["A","B"],["B","C"]],[[0],[1]]),
("D4",3,[["A","B"],["B","C"]],[[0],[0,1]]),
("D5",3,[["A","B"],["C"]],[[0],[1]]),
("D6",3,[["A","B"],["C"]],[[0],[0,1]]),
("D7",3,[["A","B"],["C"]],[[1],[0,1]]),
("D8",2,[["A"],["B"]],[[0],[1]]),
("D9",2,[["A"],["B"]],[[0],[0,1]]),
]
def name(t): return "∧".join(t)
for rid,M,T,Ls in REPS:
    pats=[]
    for w in range(2**M):
        x=[L[j] for j in range(M) if w>>(M-1-j)&1]
        pats.append(("".join(x) or "-", [int(any(set(T[a])<=set(x) for a in ls)) for ls in Ls]))
    outs=["∨".join("("+name(T[a])+")" if len(T[a])>1 else T[a][0] for a in ls) for ls in Ls]
    cols=["".join(str(p[1][i]) for p in pats) for i in range(len(Ls))]
    true=[[p[0] for p in pats if p[1][i]] for i in range(len(Ls))]
    fan=[v for v in L[:M] if sum(v in t for t in T)>1]
    print(f"| {rid} | Cascade {len(T)} {len(Ls)} {M} | terms {', '.join('{'+','.join(t)+'}' for t in T)} | lines {Ls} | "+" ; ".join(f"out{i}: {o} = {c} true on {' '.join(tr)}" for i,(o,c,tr) in enumerate(zip(outs,cols,true)))+f" | fan-out {fan or '-'} | cells {len(T)+len(Ls)} |")
