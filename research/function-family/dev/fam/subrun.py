"""Is a tied-port run of F2, F3 or F4 a sub-run of F1's (A∧B)∨(C∧D) run, port by port? F1's ports: A->a1, B->a2,
C->b1, D->b2. A member's wiring maps each of its inputs to a set of F1 ports; a slot pulses the union. Compare the
port sets of every slot of the member's calendar with F1's slots."""
import itertools
F1 = {"A": {"a1"}, "B": {"a2"}, "C": {"b1"}, "D": {"b2"}}
M = {
 "F2 tied-shared B": {"A": {"a1"}, "B": {"a2", "b1"}, "C": {"b2"}},
 "F3 tied C":        {"A": {"a1"}, "B": {"a2"}, "C": {"b1", "b2"}},
 "F4 tied A,B":      {"A": {"a1", "a2"}, "B": {"b1", "b2"}},
}
def ports(w, pat): return frozenset().union(*[w[x] for x in pat]) if pat else frozenset()
def cal(w, terms):
    ins = sorted(w)
    s = {"train": [ports(w, set().union(*terms))], "lesson": [ports(w, t) for t in terms],
         "test": [ports(w, set(p)) for k in range(len(ins)+1) for p in itertools.combinations(ins, k)]}
    return s
f1 = cal(F1, [{"A","B"}, {"C","D"}])
T = {"F2 tied-shared B": [{"A","B"},{"B","C"}], "F3 tied C": [{"A","B"},{"C"}], "F4 tied A,B": [{"A"},{"B"}]}
for name, w in M.items():
    c = cal(w, T[name])
    print(name, {k: [sorted(p) for p in v if p not in f1[k]] for k, v in c.items()})
