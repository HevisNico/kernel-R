"""The nine networks of LAYERED_GENERATOR_DESIGN.md 2.2, as (gate, sources) per layer, with each function stated
independently of the network, as a Lean Bool expression in x : Pattern 3."""
AND3 = "x 0 && x 1 && x 2"
OR3 = "x 0 || x 1 || x 2"
MAJ = "decide (2 ≤ card x)"
NETWORKS = {
    "AND3a": ([[("both", (0, 1)), ("copy", (2, None))], [("both", (0, 1))]], AND3),
    "AND3b": ([[("both", (0, 1)), ("both", (2, 2))], [("both", (0, 1))]], AND3),
    "AND3c": ([[("both", (0, 1)), ("both", (1, 2))], [("both", (0, 1))]], AND3),
    "OR3a": ([[("either", (0, 1)), ("copy", (2, None))], [("either", (0, 1))]], OR3),
    "OR3b": ([[("either", (0, 1)), ("both", (2, 2))], [("either", (0, 1))]], OR3),
    "OR3c": ([[("either", (0, 1)), ("either", (1, 2))], [("either", (0, 1))]], OR3),
    "MAJa": ([[("both", (0, 1)), ("both", (0, 2)), ("both", (1, 2))], [("either", (0, 1)), ("copy", (2, None))], [("either", (0, 1))]], MAJ),
    "MAJb": ([[("both", (0, 1)), ("both", (0, 2)), ("both", (1, 2))], [("either", (0, 1)), ("both", (2, 2))], [("either", (0, 1))]], MAJ),
    "MAJc": ([[("both", (0, 1)), ("either", (0, 1)), ("copy", (2, None))], [("copy", (0, None)), ("both", (1, 2))], [("either", (0, 1))]], MAJ),
}
TRUTH = dict(AND3=lambda x: len(x) == 3, OR3=lambda x: len(x) >= 1, MAJ=lambda x: len(x) >= 2)
