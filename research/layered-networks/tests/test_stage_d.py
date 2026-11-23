"""Tests of stage_d.py, seal.py and compare_d.py (no simulation). Run: python3 -B tests/test_stage_d.py"""
import json
from pathlib import Path
import sys
import tempfile

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
import compare_d  # noqa: E402
import seal  # noqa: E402
import spec as specmod  # noqa: E402
import stage_d  # noqa: E402

SPECS = HERE / "specs"
GATE_TABLE = dict(copy={(1,): True}, both={(1,): False, (2,): False, (1, 2): True},
                  either={(1,): True, (2,): True, (1, 2): True})


def gate_tables(s):
    return {c: dict(GATE_TABLE[g]) for c, _, _, g in stage_d.cell_names(s)}


def test_compose_equals_function():
    for name in ("not1", "andor3", "xor3"):
        s = specmod.load(SPECS / f"{name}.json")
        cells, outs = stage_d.compose(s, gate_tables(s))
        for x, e in zip(specmod.patterns(s["m"]), s["expect"]):
            assert outs[str(specmod.code(x))] == e, (name, x)
            assert cells[str(specmod.code(x))] == {c: b for c, b in zip([n for n, *_ in stage_d.cell_names(s)],
                                                                       [b for layer in specmod.predict_layers(s, specmod.rails(s, x)) for b in layer])}


def test_compose_reads_the_observed_table():
    s = specmod.load(SPECS / "not1.json")
    _, outs = stage_d.compose(s, {"c1_0": {(1,): False}})       # a copy cell observed silent: NOT1 never fires
    assert outs == {"0": False, "1": False}
    _, outs = stage_d.compose(s, {"c1_0": {}})                   # a mask not read: unknown
    assert outs == {"0": None, "1": False}


def test_cell_view():
    rec = dict(slots=[dict(kind="lesson", info=dict(stage="D"), reads=[dict(layer=1, index=0), dict(layer=2, index=0)]),
                      dict(kind="scan", actions={})], tests=[])
    v = stage_d.cell_view(rec, "c2_0", 2)
    assert v["slots"][0]["reads"] == [dict(layer=2, index=0)] and v["slots"][0]["info"]["layer"] == 2
    assert len(rec["slots"][0]["reads"]) == 2 and "layer" not in rec["slots"][0]["info"]   # the record is not changed


def test_inverter_gate():
    s = specmod.load(SPECS / "not1.json")
    assert stage_d.inverter_gate(s, None)["K0"] is False
    assert stage_d.inverter_gate(s, "assumed")["K3"] is True
    with tempfile.TemporaryDirectory() as d:
        p = Path(d) / "g.json"
        p.write_text(json.dumps(dict(kit_commit="x", inverters={"n0": dict(K0=True, K3=False)})))
        g = stage_d.inverter_gate(s, str(p))
        assert g["K0"] and not g["K3"]
    a = specmod.load(SPECS / "andor3.json")
    assert stage_d.inverter_gate(a, None)["K0"] is True                         # no front end, nothing to gate


def fake_prediction(tag="NOT1", seed=9801, eligible=True, room=True, word="ssFF"):
    pred = dict(words={"1/0/0": word}, outputs={"0": True, "1": False},
                cells={"0": {"c1_0": True}, "1": {"c1_0": False}}, skew_silent=[], output_equals_function=True)
    return dict(format=stage_d.FORMAT, tag=tag, seed=seed, status="done", inverter_gate=dict(source="assumed"),
                eligible_K0=eligible, room_K3=room and eligible, applies=dict(noiseless=eligible, noisy=room and eligible),
                prediction=pred if eligible else None)


def write_instance(root, name, pred):
    d = Path(root) / name
    d.mkdir()
    (d / "prediction.json").write_bytes(stage_d.canon(pred))
    return d


def fake_record(word="ssFF", out0=True, noise=None, seed=9801):
    def test(pattern, fired):
        return dict(kind="test", info=dict(pattern=[pattern]),
                    reads=[dict(layer=1, index=0, emission=123 if fired else None)])
    rec = dict(tag="NOT1", seed=seed, status="done", words={"1/0/0": word}, tests=[0, 1],
               slots=[test(0, out0), test(1, False)])
    if noise:
        rec["noise"] = noise
    return rec


def test_seal_reproducible_and_tamper():
    with tempfile.TemporaryDirectory() as d:
        a = write_instance(d, "a", fake_prediction())
        b = write_instance(d, "b", fake_prediction("ANDOR3", 9802, eligible=False))
        assert seal.seal(Path(d) / "S1", a, b) and seal.seal(Path(d) / "S2", b, a)
        for f in ("SHA256SUMS", "MANIFEST.json", "NOT1_9801.json", "ANDOR3_9802.json"):
            assert (Path(d) / "S1" / f).read_bytes() == (Path(d) / "S2" / f).read_bytes(), f
        assert seal.verify(Path(d) / "S1")
        try:
            seal.seal(Path(d) / "S1", a)
            raise AssertionError("an existing seal was overwritten")
        except SystemExit:
            pass
        p = Path(d) / "S1" / "NOT1_9801.json"
        p.write_bytes(p.read_bytes().replace(b"ssFF", b"sssF"))
        assert not seal.verify(Path(d) / "S1")
        try:
            seal.load(Path(d) / "S1", "NOT1", 9801)
            raise AssertionError("a broken seal was read")
        except SystemExit:
            pass


def compare_with(pred, rec, kind="auto"):
    with tempfile.TemporaryDirectory() as d:
        inst = write_instance(d, "i", pred)
        seal.seal(Path(d) / "S", inst)
        n = Path(d) / "N"
        n.mkdir()
        (n / "record.json").write_text(json.dumps(rec))
        return compare_d.compare(Path(d) / "S", SPECS / "not1.json", n, kind)


def test_compare():
    r = compare_with(fake_prediction(), fake_record())
    assert r["verdict"] == "agrees" and r["compared"]["letters"] == 4 and r["compared"]["outputs"] == 2
    r = compare_with(fake_prediction(), fake_record(word="sFFF"))
    assert r["verdict"] == "refuted" and [x["position"] for x in r["differences"]] == [1]
    r = compare_with(fake_prediction(), fake_record(word="ssFFF"))
    assert r["verdict"] == "refuted" and r["differences"][0]["position"] == 4
    r = compare_with(fake_prediction(), fake_record(out0=False))
    assert r["verdict"] == "refuted" and {x["what"] for x in r["differences"]} == {"output", "cell"}
    r = compare_with(fake_prediction(eligible=False), fake_record(word="sFFF"))      # no prediction: observed only
    assert r["verdict"].startswith("observed only") and r["why"] == "not eligible at K0" and "differences" not in r
    noisy = dict(b_mV=0.111, w_mV=0.094, d_mV=0.009)
    r = compare_with(fake_prediction(room=False), fake_record(noise=noisy))
    assert r["run_kind"] == "noisy" and r["verdict"].startswith("observed only") and r["why"] == "no room at K3"
    r = compare_with(fake_prediction(room=True), fake_record(noise=noisy, word="sFFF"))
    assert r["verdict"] == "refuted"
    r = compare_with(fake_prediction(), fake_record(noise=dict(b_mV=0, w_mV=0, d_mV=0)))
    assert r["run_kind"] == "noiseless" and r["verdict"] == "agrees"
    r = compare_with(fake_prediction(), fake_record(seed=9809))
    assert r["verdict"].startswith("observed only") and "no sealed prediction" in r["why"]
    try:
        compare_with(fake_prediction(), fake_record(), kind="noisy")
        raise AssertionError("a stated kind contradicting the record was accepted")
    except SystemExit:
        pass


if __name__ == "__main__":
    n = 0
    for k, f in list(globals().items()):
        if k.startswith("test_"):
            f()
            n += 1
            print("ok", k)
    print(f"{n} tests passed")
