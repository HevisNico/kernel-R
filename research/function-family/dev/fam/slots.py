"""Port-level slot tables of each member, tied and unary, against F1's slots. A slot is (kind, writers, pulsed
ports with amplitude). F1's names: 'L1' (layer 1), 'lesson a', 'lesson b', 'test X'. Prints markdown rows."""
import itertools
def member(wiring, terms, amp):
    ins = sorted(wiring)
    def P(pat): return frozenset((p, amp[p]) for x in pat for p in wiring[x])
    rows = [("L1", "a, b", P(set().union(*terms)))]
    rows += [(f"lesson {'ab'[i]}", "c", P(t)) for i, t in enumerate(terms)]
    rows += [("test " + ("".join(p) or "-"), "none", P(p)) for k in range(len(ins)+1) for p in itertools.combinations(ins, k)]
    return rows
A49, A1 = "0.49", "1.0"
F1 = member({"A":["a1"],"B":["a2"],"C":["b1"],"D":["b2"]}, [{"A","B"},{"C","D"}], {p:A49 for p in ("a1","a2","b1","b2")})
f1 = {}
for name, w, ports in F1: f1.setdefault((w, ports), name); f1.setdefault(("none", ports), None)
f1_any = {ports: name for name, w, ports in F1}
f1_kind = {(w, ports): name for name, w, ports in F1}
M = {
 "F2": ({"A":["a1"],"B":["a2","b1"],"C":["b2"]}, [{"A","B"},{"B","C"}], {p:A49 for p in ("a1","a2","b1","b2")}),
 "F3 tied": ({"A":["a1"],"B":["a2"],"C":["b1","b2"]}, [{"A","B"},{"C"}], {p:A49 for p in ("a1","a2","b1","b2")}),
 "F4 tied": ({"A":["a1","a2"],"B":["b1","b2"]}, [{"A"},{"B"}], {p:A49 for p in ("a1","a2","b1","b2")}),
 "F3 unary": ({"A":["a1"],"B":["a2"],"C":["b1"]}, [{"A","B"},{"C"}], {"a1":A49,"a2":A49,"b1":A1}),
 "F4 unary": ({"A":["a1"],"B":["b1"]}, [{"A"},{"B"}], {"a1":A1,"b1":A1}),
}
fmt = lambda ports: "{" + ", ".join(f"{p}" + ("@1.0" if a == A1 else "") for p, a in sorted(ports)) + "}"
for m, (w, t, a) in M.items():
    print(f"\n{m}:")
    new = 0
    for name, wr, ports in member(w, t, a):
        same = f1_kind.get((wr, ports))
        other = f1_any.get(ports)
        tag = f"= F1 {same}" if same else (f"pulses as F1 {other}, but writers {wr}" if other else "NEW: in no F1 slot")
        new += not same
        print(f"  {name:10s} writers {wr:5s} ports {fmt(ports):28s} {tag}")
    print(f"  slots not in F1 (same writers and ports): {new}")
