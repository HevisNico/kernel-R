"""Verify pinned public CSV evidence and regenerate its small Lean projection.

This checks recorded summaries and rational budgets, not simulator binaries,
peak-to-gain correspondence, actual gain bounds or six-cell calibration coverage.
All arithmetic uses Fraction; the five displayed budget quantities are widened
outward by 1e-10. --check refuses a stale generated file, without rewriting it.
"""
import argparse
import copy
import csv
from fractions import Fraction as Q
import hashlib
import io
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
EVIDENCE = HERE / "evidence"
GENERATED = HERE / "PhysicalEvaluator/RecordedData.lean"
COMMIT = "9a30f822c8b01fddf11e2514c4aa4059750644cf"
PROVENANCE_SHA256 = "c588891ca6a773c2d4fc49fc0dcdf9588466062fac04271179985647dcc5b4b9"
PAD = Q(1, 10**10)
CELLS = ("t6004", "t6007")


class EvidenceError(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise EvidenceError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def integrity(blobs):
    require(digest(blobs["provenance.json"]) == PROVENANCE_SHA256, "provenance hash")
    provenance = json.loads(blobs["provenance.json"])
    require(provenance["commit"] == COMMIT and provenance["pull_request"] == 107,
            "pinned revision")
    files = provenance["files"]
    require(len(files) == 7 and len({f["local"] for f in files}) == 7, "file manifest")
    for item in files:
        require(digest(blobs[item["local"]]) == item["sha256"], "source hash: " + item["local"])
    return provenance


def rows(data):
    reader = csv.DictReader(io.StringIO(data.decode("utf-8")))
    result = list(reader)
    require(all(None not in r and all(v is not None for v in r.values()) for r in result),
            "malformed CSV row")
    return result


def parse(blobs):
    return {"ports": rows(blobs["ports.csv"]), "predictions": rows(blobs["predictions.csv"]),
            "calibration": json.loads(blobs["calibration.json"], parse_float=Q),
            "runs": {c: {"rows": rows(blobs[c + "_train.csv"]),
                         "metadata": json.loads(blobs[c + "_train.json"]),
                         "csv_hash": digest(blobs[c + "_train.csv"])} for c in CELLS}}


def indexed(table):
    result = {(r["cell"], int(r["port"])): r for r in table}
    require(len(result) == len(table), "duplicate port record")
    return result


def widened(row):
    return {"a": Q(row["a"]) + PAD, "B": Q(row["B"]) + PAD,
            "ell": Q(row["ell"]) + PAD, "half_d0": Q(row["half_d0"]) - PAD,
            "level0": Q(row["level0"]) - PAD}


def domain(values):
    budget = values["a"] + values["B"] + Q(20, 17) * values["ell"] + Q(1, 8000)
    return (budget < values["half_d0"] and
            Q(19, 20) <= values["level0"] - values["ell"]), budget


def analyse(data):
    ports, predictions = indexed(data["ports"]), indexed(data["predictions"])
    require(len(ports) == 200 and ports.keys() == predictions.keys(), "summary cohort")
    calibration = data["calibration"]
    require(calibration["status"] == "evaluated" and calibration["problems"] == [],
            "calibration status")
    require(len(calibration["leak_scans"]) == 6, "six-cell calibration scope")
    results = []
    for cell in CELLS:
        run = data["runs"][cell]
        meta, trace = run["metadata"], run["rows"]
        require(meta["csv_sha256"] == run["csv_hash"], "metadata csv_sha256")
        require(meta["status"] == "done" and meta["stage"] == "test" and
                meta["run"]["name"] == cell + "_train" and
                meta["run"]["mode"] == "train" and meta["run"]["noise"] is True and
                meta["run"]["seed"] == int(cell[1:]), "run metadata")
        require(meta["rest_fire"] is False, "rest FIRE")
        require(len(trace) == 21 and [int(r["pulse"]) for r in trace] == list(range(21)),
                "complete ordered train")
        require([int(r["port"]) for r in trace] == [1]*10 + [2]*10 + [0], "port schedule")
        for port in (1, 2):
            row, prediction = ports[cell, port], predictions[cell, port]
            selected = [r for r in trace if int(r["port"]) == port]
            require(all(r["fired"] in ("0", "1") for r in selected), "Boolean readings")
            readings = [r["fired"] == "1" for r in selected]
            first = next((i for i, b in enumerate(readings) if b), None)
            require(first is not None, "missing first FIRE")
            m = int(prediction["m"])
            require(m == int(row["m"]) and 0 <= m < len(selected), "prediction index")
            require(first == int(row["count"]), "first FIRE crosscheck")
            require(row["count_agrees"] == str(first == m), "count agreement crosscheck")
            require(int(row["r"]) == min(first, m), "certified prefix extent")
            require(Q(row["level0"]) == Q(prediction["level0"]), "level0 crosscheck")
            require(abs(2 * Q(row["half_d0"]) - calibration["d0"]) <= 2 * PAD,
                    "dose calibration crosscheck")
            require(abs(Q(prediction["static_level"]) + calibration["mu"] -
                        Q(row["level0"])) <= 2 * PAD, "threshold offset crosscheck")
            require(abs(Q(row["noise"]) + calibration["h_mu"] + Q(1, 5000) -
                        Q(row["ell"])) <= 2 * PAD, "threshold uncertainty crosscheck")
            for r in selected[:first + 1]:
                fired = int(r["fired"])
                require(Q(1, 10) <= Q(r["c_pre"]) - PAD and
                        Q(r["c_pre"]) + PAD <= Q(1, 10) + Q(1, 10000), "resting charge band")
                require(int(r["latch_rises"]) == fired and int(r["second_rise"]) == 0,
                        "single latch prefix")
                for axis in (1, 2):
                    expected = int(axis == port and not fired)
                    require(int(r[f"steered{axis}"]) == expected and
                            int(r[f"steer_rises{axis}"]) == expected, "steering prefix")
            values = widened(row)
            require(all(values[k] >= 0 for k in ("a", "B", "ell", "half_d0")),
                    "nonnegative budget quantities")
            in_domain, budget = domain(values)
            raw_room = Q(row["half_d0"]) - Q(row["a"]) - Q(row["B"]) - Q(20,17)*Q(row["ell"]) - Q(1,8000)
            require(abs(raw_room - Q(row["room"])) <= 5 * PAD, "reported room crosscheck")
            claimed = row["status"] == "certified, count confirmed"
            require(row["status"] in ("certified, count confirmed", "outside the certified domain"),
                    "unknown status")
            require(claimed == in_domain, "domain status crosscheck")
            require(not in_domain or first == m, "in-domain count contradiction")
            results.append({"cell": cell, "port": port, "predicted": m, "observed": first,
                            "readings": readings, "charges": [Q(r["c_pre"]) for r in selected[:m+1]],
                            "in_domain": in_domain, "values": values,
                            "nominal_level0": Q(row["level0"]), "dose0": calibration["d0"],
                            "conservative_room": values["half_d0"] - budget,
                            "conservative_floor": values["level0"] - values["ell"]})
    require([(r["predicted"], r["observed"], r["in_domain"]) for r in results] ==
            [(6,6,True), (4,4,True), (5,4,False), (3,3,False)], "pinned outcomes")
    return results


def literal(q):
    return f"({q.numerator} / {q.denominator} : ℝ)"


def render(results):
    out = ['import PhysicalEvaluator.Counts', '',
           '/-! Generated by evidence_check.py from PR #107 public CSV summaries at',
           f'{COMMIT}. All decimal arithmetic is exact rational;',
           'budget fields are widened outward by 1e-10. These are recorded readings',
           'and arithmetic checks, NOT a constructed FiniteProbeCertificate.',
           'Gain bounds, threshold bounds and scalar correspondence remain premises.',
           'No binary trace is re-extracted and no calibration coverage is inferred. -/',
           'namespace ReusableController.PhysicalEvaluator.RecordedData', '']
    suffixes = {"a":"A", "B":"B", "ell":"Ell", "half_d0":"HalfDose", "level0":"Level0"}
    for r in results:
        name = f'{r["cell"]}p{r["port"]}'
        reads = ', '.join(str(b).lower() for b in r['readings'])
        out += [f'def {name}Readings : List Bool := [{reads}]',
                f'def {name}Prefix : List Bool := {name}Readings.take {r["predicted"]+1}']
        for k, suffix in suffixes.items():
            out += [f'noncomputable def {name}{suffix} : ℝ := {literal(r["values"][k])}']
        out += [f'noncomputable def {name}NominalLevel0 : ℝ := {literal(r["nominal_level0"])}',
                f'noncomputable def {name}Dose0 : ℝ := {literal(r["dose0"])}']
        gate = f'{name}A + {name}B + 20 / 17 * {name}Ell + 1 / 8000 < {name}HalfDose'
        floor = f'19 / 20 ≤ {name}Level0 - {name}Ell'
        out += [f'def {name}Gate : Prop := ({gate}) ∧ ({floor})',
                f'theorem {name}FirstFire : firstFire {name}Readings = some {r["observed"]} := by decide',
                f'theorem {name}PrefixFirstFire : firstFire {name}Prefix = some {r["observed"]} := by decide',
                f'theorem {name}Count : decodedCount {name}Readings = {r["observed"]} := by decide']
        definitions = ', '.join(name + suffix for suffix in suffixes.values())
        if r['in_domain']:
            charges = ', '.join(literal(c) for c in r['charges'])
            out += [f'noncomputable def {name}Charges : List ℝ := [{charges}]',
                    f'theorem {name}ChargeBand : ∀ c ∈ {name}Charges, 1 / 10 ≤ c ∧ c ≤ 1 / 10 + 1 / 10000 := by',
                    f'  norm_num [{name}Charges]',
                    f'theorem {name}Room : {gate} := by', f'  norm_num [{definitions}]',
                    f'theorem {name}Floor : {floor} := by', f'  norm_num [{definitions}]',
                    f'theorem {name}CalibratedRoom : {name}A + {name}B + 20 / 17 * {name}Ell + 1 / 8000 < {name}Dose0 / 2 := by',
                    f'  norm_num [{definitions}, {name}Dose0]',
                    f'theorem {name}NominalFloor : 19 / 20 ≤ {name}NominalLevel0 - {name}Ell := by',
                    f'  norm_num [{name}NominalLevel0, {name}Ell]',
                    f'theorem {name}InDomain : {name}Gate := ⟨{name}Room, {name}Floor⟩',
                    f'theorem {name}PrefixShape : {name}Prefix = List.replicate {r["predicted"]} false ++ [true] := by decide']
        else:
            out += [f'theorem {name}OutsideDomain : ¬ {name}Gate := by',
                    f'  norm_num [{name}Gate, {definitions}]']
        out += ['']
    out += ['theorem mismatching_count_is_outside :',
            '    firstFire t6007p1Readings = some 4 ∧ (4 : ℕ) ≠ 5 ∧ ¬ t6007p1Gate :=',
            '  ⟨t6007p1FirstFire, by decide, t6007p1OutsideDomain⟩', '',
            'theorem agreeing_count_does_not_certify :',
            '    firstFire t6007p2Readings = some 3 ∧ ¬ t6007p2Gate :=',
            '  ⟨t6007p2FirstFire, t6007p2OutsideDomain⟩', '',
            'end ReusableController.PhysicalEvaluator.RecordedData', '']
    return '\n'.join(out).encode()


def negative_controls(blobs, parsed):
    results = []
    def rejected(name, action, marker, layer):
        try:
            action()
        except EvidenceError as e:
            require(marker in str(e), name + ': wrong rejection: ' + str(e))
            results.append({"mutation": name, "rejected": True, "check": str(e), "layer": layer})
        else:
            raise EvidenceError(name + ': mutation was accepted')
    changed = dict(blobs)
    changed['t6004_train.csv'] += b'\n'
    rejected('modified_source_hash', lambda: integrity(changed), 'source hash', 'integrity')
    changed_manifest = dict(blobs)
    changed_manifest['provenance.json'] += b'\n'
    rejected('modified_manifest', lambda: integrity(changed_manifest), 'provenance hash', 'integrity')
    def semantic(name, edit, marker):
        changed = copy.deepcopy(parsed)
        edit(changed)
        rejected(name, lambda: analyse(changed), marker, 'semantic; integrity deliberately bypassed')
    semantic('metadata_wrong_csv_hash', lambda d: d['runs']['t6004']['metadata'].__setitem__('csv_sha256','0'*64), 'metadata csv_sha256')
    semantic('wrong_first_reading', lambda d: d['runs']['t6004']['rows'][0].__setitem__('fired','1'), 'first FIRE crosscheck')
    semantic('truncated_train', lambda d: d['runs']['t6004']['rows'].pop(), 'complete ordered train')
    semantic('rest_fire', lambda d: d['runs']['t6004']['metadata'].__setitem__('rest_fire',True), 'rest FIRE')
    semantic('extra_latch_rise', lambda d: d['runs']['t6004']['rows'][0].__setitem__('latch_rises','1'), 'single latch prefix')
    semantic('wrong_steering', lambda d: d['runs']['t6004']['rows'][0].__setitem__('steer_rises2','1'), 'steering prefix')
    semantic('charge_outside_band', lambda d: d['runs']['t6004']['rows'][0].__setitem__('c_pre','0.1002'), 'resting charge band')
    semantic('false_certificate_despite_agreeing_count',
             lambda d: next(r for r in d['ports'] if r['cell']=='t6007' and r['port']=='2').__setitem__('status','certified, count confirmed'),
             'domain status crosscheck')
    def destroy_room(data):
        row = next(r for r in data['ports'] if r['cell']=='t6004' and r['port']=='1')
        row['a'] = str(Q(row['a']) + Q(1,10))
        row['room'] = str(Q(row['room']) - Q(1,10))
    semantic('insufficient_room_even_with_matching_count', destroy_room, 'domain status crosscheck')
    def destroy_floor(data):
        row = next(r for r in data['ports'] if r['cell']=='t6004' and r['port']=='1')
        pred = next(r for r in data['predictions'] if r['cell']=='t6004' and r['port']=='1')
        row['level0'] = pred['level0'] = '0.95'
        pred['static_level'] = str(Q(19,20) - data['calibration']['mu'])
    semantic('threshold_floor_violated', destroy_floor, 'domain status crosscheck')
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true', help='Compare generated Lean byte for byte; do not rewrite it')
    parser.add_argument('--report', type=Path, help='Write deterministic validation report')
    args = parser.parse_args()
    names = ['provenance.json','ports.csv','calibration.json','predictions.csv'] + [c+'_train'+s for c in CELLS for s in ('.csv','.json')]
    blobs = {n: (EVIDENCE/n).read_bytes() for n in names}
    provenance = integrity(blobs)
    parsed = parse(blobs)
    results = analyse(parsed)
    generated = render(results)
    if args.check:
        require(GENERATED.read_bytes() == generated, 'generated Lean differs; regenerate and review')
    else:
        GENERATED.write_bytes(generated)
    controls = negative_controls(blobs, parsed)
    report = {"commit": COMMIT, "pull_request":107, "positive_integrity":True,
              "positive_domain_checks":True, "generated_matches":True,
              "arithmetic":"exact rational decimals; outward padding 1/10000000000",
              "source_sha256":{n:digest(b) for n,b in sorted(blobs.items())},
              "checker_sha256":digest(Path(__file__).read_bytes()),
              "generated_sha256":digest(generated),
              "ports":[{k:(str(v) if isinstance(v,Q) else v) for k,v in r.items()
                        if k not in ('values','charges','readings')} for r in results],
              "negative_controls":controls,
              "scope":provenance['scope'],
              "unproved_premises":["gain and threshold bounds from physical traces",
                                  "scalar peak-to-gain/fire correspondence", "six-cell h_mu transfer"]}
    if args.report:
        args.report.write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    print(f'Pinned evidence verified: 7 files; 2 in-domain ports, 2 excluded ports; {len(controls)} negative controls rejected.')


if __name__ == '__main__':
    main()
