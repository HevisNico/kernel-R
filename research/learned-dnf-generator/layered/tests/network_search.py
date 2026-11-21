"""Exhaustive search of layered networks of two-port cells (LayeredMonotoneTarget.lean semantics), M = 3 inputs.
A node: gate in off/on/copy/both/either, sources from the layer below (copy: port 0 only; both/either: two ports).
Node.Valid's stimulus condition: for each active group g, some external pattern x makes the node's two inputs
(predicted outputs of its sources, an absent source reads false) equal groupMask g exactly.
Truth tables are 8-bit ints over patterns x = 0..7 (bit j of x is input j: A=0, B=1, C=2)."""
import itertools, sys
M = 3
X = range(2 ** M)
def tt(f): return sum(1 << x for x in X if f(x))
INPUTS = [tt(lambda x, j=j: x >> j & 1) for j in range(M)]
NAMES = "ABC"
def bit(t, x): return t >> x & 1
GROUPMASK = {"copy": [(1, 0)], "both": [(1, 1)], "either": [(1, 0), (0, 1)], "on": [], "off": []}
def nodes_over(lower):
    """All valid nodes over a lower layer (list of truth tables): (gate, sources, truth table, groups, stimuli)."""
    n = len(lower)
    out = [("off", (None, None), 0, 0, ()), ("on", (None, None), 255, 0, ())]
    cand = [("copy", (i, None)) for i in range(n)] + [(g, (i, j)) for g in ("both", "either") for i in range(n) for j in range(n)]
    for g, (i, j) in cand:
        def inp(x):
            return (bit(lower[i], x), 0 if j is None else bit(lower[j], x))
        f = {"copy": lambda a, b: a, "both": lambda a, b: a & b, "either": lambda a, b: a | b}[g]
        t = tt(lambda x: f(*inp(x)))
        stims = []
        ok = True
        for gm in GROUPMASK[g]:
            s = [x for x in X if inp(x) == gm]
            if not s: ok = False; break
            stims.append(s)
        if ok:
            out.append((g, (i, j), t, len(GROUPMASK[g]), tuple(stims)))
    return out
TARGETS = {"AND3": tt(lambda x: x == 7), "OR3": tt(lambda x: x != 0), "MAJ": tt(lambda x: bin(x).count("1") >= 2)}
best = {k: [] for k in TARGETS}
def record(widths, net, out_t):
    for k, t in TARGETS.items():
        if out_t == t:
            best[k].append((sum(widths), widths, net))
# depth 1
for nd in nodes_over(INPUTS):
    record((1,), [[nd]], nd[2])
# depth 2 and 3, widths up to 3 below the top, top width 1
L1 = nodes_over(INPUTS)
for w1 in (1, 2, 3):
    for layer1 in itertools.combinations_with_replacement(range(len(L1)), w1):
        l1 = [L1[k] for k in layer1]
        t1 = [nd[2] for nd in l1]
        L2 = nodes_over(t1)
        for nd in L2:
            record((w1, 1), [l1, [nd]], nd[2])
        for w2 in (1, 2):
            for layer2 in itertools.combinations_with_replacement(range(len(L2)), w2):
                l2 = [L2[k] for k in layer2]
                for nd in nodes_over([x[2] for x in l2]):
                    record((w1, w2, 1), [l1, l2, [nd]], nd[2])
def show(net):
    s = []
    for li, layer in enumerate(net):
        below = (lambda i: NAMES[i]) if li == 0 else (lambda i, li=li: f"L{li}.{i}")
        s.append(f"L{li+1}: " + ", ".join(f"{g}({','.join(below(i) for i in src if i is not None)})" for g, src, *_ in layer))
    return "; ".join(s)
for k, xs in best.items():
    m = min(c for c, _, _ in xs)
    mins = [x for x in xs if x[0] == m]
    print(f"{k}: smallest network has {m} cells; {len(mins)} minimal networks (sources ordered, layers as multisets)")
    seen = set()
    for c, w, net in sorted(mins, key=lambda x: (sum(nd[3] for layer in x[2] for nd in layer), str(x[1]))):
        groups = sum(nd[3] for layer in net for nd in layer)
        key = show(net)
        if key in seen: continue
        seen.add(key)
        print(f"   widths {w}, trained groups {groups}: {key}")
        if len(seen) >= 12: break

print("\n--- ranked by (external fan-out, internal fan-out, copies, trained groups) ---")
def fan(net):
    ext = [0] * M
    for g, src, *_ in net[0]:
        for i in set(s for s in src if s is not None):
            ext[i] += 1
    inner = 0
    for li in range(1, len(net)):
        cnt = [0] * len(net[li - 1])
        for g, src, *_ in net[li]:
            for i in set(s for s in src if s is not None):
                cnt[i] += 1
        inner = max([inner] + cnt)
    return max(ext), inner
for k, xs in best.items():
    m = min(c for c, _, _ in xs)
    rows = {}
    for c, w, net in xs:
        if c != m: continue
        # skip networks with off/on cells or unused cells
        used = all(any(i in src for g, src, *_ in net[li + 1] for i in [j]) for li in range(len(net) - 1) for j in range(len(net[li])))
        if not used: continue
        copies = sum(nd[0] == "copy" for layer in net for nd in layer)
        groups = sum(nd[3] for layer in net for nd in layer)
        fe, fi = fan(net)
        key = show(net)
        rows[key] = (fe, fi, copies, groups, w, net)
    print(k, "minimal networks with every cell used:", len(rows))
    for key, (fe, fi, copies, groups, w, net) in sorted(rows.items(), key=lambda kv: kv[1][:4])[:8]:
        stim = [[[ "".join(NAMES[j] for j in range(M) if x >> j & 1) or "-" for x in s][:3] for s in nd[4]] for layer in net for nd in layer]
        print(f"   ext fan-out {fe}, inner fan-out {fi}, copies {copies}, groups {groups}: {key}\n      stimuli per node and group (first 3): {stim}")
