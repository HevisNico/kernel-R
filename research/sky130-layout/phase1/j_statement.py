"""The statement that the report of stage J must carry, by ../AMENDMENT_2.md.

  python3 -I j_statement.py          after `j_stage.py report`; writes J_STATEMENT.md

The sentences are fixed here, before any run. Which one is written depends only on the verdicts
of JK (run J5, with areas: the port falls silent again after its stop) and JL (run J6, without
areas: it does not).
"""
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

ARTIFACT = ("**JK and JL hold.** At 125 °C the nominal cell with junction areas falls silent again after "
            "its stop, and the same cell without areas does not. The earlier result of the circuit campaign "
            "at 125 °C, a stop with no relapse after it (run `pvt_tt_125`, prediction P12), was an artifact "
            "of netlists without junction areas. This is a nominal simulation, with the areas of devices "
            "drawn alone and no layout.")
NOT_CARRIED = ("**JK fails.** With junction areas the nominal cell at 125 °C does not fall silent again every "
               "5 to 11 periods after its stop. The arithmetic of phase 0, made on one device, does not carry "
               "to the cell as predicted. No artifact of the earlier 125 °C result is claimed from this stage.")
NOT_THE_AREAS = ("**JK holds and JL fails.** The cell without areas also falls silent again after its stop at "
                 "125 °C. The relapse is then not shown to come from the junction areas, and no artifact of the "
                 "earlier 125 °C result is claimed from this stage.")
NOT_EVALUABLE = ("**JK or JL is not evaluable.** A run of the pair J5, J6 has no result. Nothing is stated "
                 "about the earlier 125 °C result.")


def statement(verdicts):
    """verdicts: key -> 'holds', 'fails' or 'not evaluable'."""
    jk, jl = verdicts["JK"], verdicts["JL"]
    if "not evaluable" in (jk, jl):
        return NOT_EVALUABLE
    if jk == "fails":
        return NOT_CARRIED
    return ARTIFACT if jl == "holds" else NOT_THE_AREAS


if __name__ == "__main__":
    import j_stage
    analyze, runs, why = j_stage.load()
    V = {k: s for k, t, s, m in j_stage.verdicts(runs, why, analyze)}
    text = "# Stage J: statement on the earlier result at 125 °C\n\nWritten by `j_statement.py` under [`../AMENDMENT_2.md`](../AMENDMENT_2.md).\n\n" + statement(V) + "\n"
    (HERE / "J_STATEMENT.md").write_text(text)
    print(statement(V))
