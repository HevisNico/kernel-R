"""The candidate networks of LAYERED_GENERATOR_DESIGN.md section 2, checked against search.py's node rules: every
trained group has an external stimulus giving exactly its group mask, and the network computes its function."""
import sys
sys.argv = ["search"]
exec(open(__file__.replace("network_chosen.py", "network_search.py")).read().split("# depth 1")[0])
def build(spec):
    lower, net = INPUTS, []
    for layer in spec:
        cands = nodes_over(lower)
        row = []
        for g, src in layer:
            src = tuple(src) + (None,) * (2 - len(src))
            nd = next((c for c in cands if c[0] == g and c[1] == src), None)
            assert nd is not None, f"no valid node {g}{src}: a group has no stimulus giving its mask"
            row.append(nd)
        net.append(row)
        lower = [nd[2] for nd in row]
    return net, lower[0]
N = dict(A=0, B=1, C=2)
CANDS = {
  "AND3-a  L1 both(A,B), copy(C); L2 both":            ("AND3", [[("both", (0, 1)), ("copy", (2,))], [("both", (0, 1))]]),
  "AND3-b  L1 both(A,B), both(C,C); L2 both":          ("AND3", [[("both", (0, 1)), ("both", (2, 2))], [("both", (0, 1))]]),
  "AND3-c  L1 both(A,B), both(B,C); L2 both":          ("AND3", [[("both", (0, 1)), ("both", (1, 2))], [("both", (0, 1))]]),
  "OR3-a   L1 either(A,B), copy(C); L2 either":        ("OR3",  [[("either", (0, 1)), ("copy", (2,))], [("either", (0, 1))]]),
  "OR3-b   L1 either(A,B), both(C,C); L2 either":      ("OR3",  [[("either", (0, 1)), ("both", (2, 2))], [("either", (0, 1))]]),
  "OR3-c   L1 either(A,B), either(B,C); L2 either":    ("OR3",  [[("either", (0, 1)), ("either", (1, 2))], [("either", (0, 1))]]),
  "MAJ-a   L1 both(A,B), both(A,C), both(B,C); L2 either(0,1), copy(2); L3 either":
           ("MAJ", [[("both", (0, 1)), ("both", (0, 2)), ("both", (1, 2))], [("either", (0, 1)), ("copy", (2,))], [("either", (0, 1))]]),
  "MAJ-b   L1 both(A,B), both(A,C), both(B,C); L2 either(0,1), both(2,2); L3 either":
           ("MAJ", [[("both", (0, 1)), ("both", (0, 2)), ("both", (1, 2))], [("either", (0, 1)), ("both", (2, 2))], [("either", (0, 1))]]),
  "MAJ-c   L1 both(A,B), either(A,B), copy(C); L2 copy(0), both(1,2); L3 either":
           ("MAJ", [[("both", (0, 1)), ("either", (0, 1)), ("copy", (2,))], [("copy", (0,)), ("both", (1, 2))], [("either", (0, 1))]]),
}
for name, (fn, spec) in CANDS.items():
    net, out = build(spec)
    groups = sum(nd[3] for row in net for nd in row)
    ports_per_input = [sum(1 for g, src, *_ in net[0] for s in src if s == j) for j in range(M)]
    ports_per_cell = [[sum(1 for g, src, *_ in net[li + 1] for s in src if s == i) for i in range(len(net[li]))] for li in range(len(net) - 1)]
    stim = ["/".join(",".join("".join(NAMES[j] for j in range(M) if x >> j & 1) or "-" for x in s) for s in nd[4]) for row in net for nd in row]
    print(f"{name}\n   computes {fn}: {out == TARGETS[fn]}; cells {sum(len(r) for r in net)}; trained groups {groups}; "
          f"ports driven per input {dict(zip(NAMES, ports_per_input))}; ports driven per cell output by layer {ports_per_cell}\n   valid stimuli per node (groups separated by /): {stim}")
