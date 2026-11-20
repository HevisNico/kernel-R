"""Test of batch2x_report.py on campaign 6's own development batch (seeds 7701 to 7710, development data), whose
predictions are on record. No simulation; it reads that batch's decks and records.
  python -B test_batch2x_report.py REPO OLD_BATCH_EVIDENCE_DIR PREDICTIONS_BATCH.json"""
import json
from pathlib import Path
import sys
import unittest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import batch2x_report
import dosedev2

REPO, OLD, RECORD = Path(sys.argv.pop(1)).resolve(), Path(sys.argv.pop(1)).resolve(), Path(sys.argv.pop(1)).resolve()
dosedev2.repo_paths(REPO)
import batch6       # noqa: E402

ROWS = None


def rows():
    global ROWS
    if ROWS is None:
        status = {}
        for m in ("a", "b"):
            status.update({r["id"]: r["status"] for r in json.loads((OLD / m / "RUNS.json").read_text())})
        ROWS = [batch2x_report.one_instance(s, batch6.MACHINE_OF[s], {k: v for k, v in status.items() if k.startswith(f"{s}-")},
                                            lambda tail, s=s: OLD / batch6.MACHINE_OF[s] / f"{s}-{tail}") for s in batch6.SEEDS]
    return ROWS


class OldBatch(unittest.TestCase):
    def test_the_frozen_rule_gives_the_batch_s_own_record(self):
        ref = {x["seed"]: x for x in json.loads(RECORD.read_text())["instances"]}
        for r in rows():
            x = ref[r["seed"]]
            self.assertEqual(r["measured"], bool(x.get("measured")), r["seed"])
            if "frozen" not in r:
                self.assertNotIn("budgets", x, r["seed"])
                continue
            self.assertEqual(r["needs"], x["needs"])
            self.assertEqual(r["frozen"]["eligible_K0"], x["eligible"])
            self.assertEqual(r["frozen"]["room_at_K3"], x["room_at_K3"])
            self.assertEqual(json.loads(json.dumps(r["budgets_units"]["frozen"])), x["budgets"])

    def test_the_summary(self):
        s = batch2x_report.summary(rows())
        self.assertEqual((s["instances"], s["measured"], s["with_a_prediction"]), (10, 9, 7))
        self.assertEqual((s["k_elig"], s["k_all3"]), (6, 0))
        self.assertEqual(s["eligible_K0"], dict(frozen=[7701, 7702, 7703, 7706, 7708, 7710], one_port=[7701, 7702, 7703, 7706, 7708, 7710]))
        self.assertEqual(s["room_at_K3"], dict(a=[7701, 7703, 7710], b=[7703, 7706], c_frozen=[], c_one_port=[7710]))
        self.assertEqual(s["a_b_and_c_all_have_room_at_K3"], dict(frozen=[], one_port=[]))
        self.assertEqual(s["crossings"], dict(n=28, in_their_window=10))
        self.assertEqual(sorted(s["without_a_prediction"]), ["7705", "7707", "7709"])

    def test_the_window_agrees_with_the_room(self):
        """For a and b, the pair's crossing in its window is the cell's room at K = 3; for c under the one-port rule,
        both lines in their windows."""
        for r in rows():
            if "frozen" not in r:
                continue
            p = r["crossings_in_their_steps"]
            self.assertEqual(p["a"]["in_its_window"], r["frozen"]["room_at_K3"]["a"], r["seed"])
            self.assertEqual(p["b"]["in_its_window"], r["frozen"]["room_at_K3"]["b"], r["seed"])
            self.assertEqual(p["c1"]["in_its_window"] and p["c2"]["in_its_window"], r["one_port"]["room_at_K3"]["c"], r["seed"])


class Walls(unittest.TestCase):
    def test_kinds_and_means(self):
        import tempfile
        with tempfile.TemporaryDirectory() as t:
            (Path(t) / "W1").mkdir()
            (Path(t) / "W2").mkdir()
            (Path(t) / "W1" / "STATE.json").write_text(json.dumps(dict(runs={
                "8301-cal-on": dict(status="complete", wall_s=1000.0, limit_s=2260), "8301-cal-off": dict(status="complete", wall_s=800.0, limit_s=1810),
                "8302-cal-on": dict(status="cut at its limit", wall_s=2260.0, limit_s=2260), "8302-cal-off": dict(status="complete", wall_s=900.0, limit_s=1810)})))
            (Path(t) / "W2" / "STATE.json").write_text(json.dumps(dict(runs={
                "8301-scan-a-pair": dict(status="complete", wall_s=600.0, limit_s=1390), "8301-scan-c-line2": dict(status="complete", wall_s=500.0, limit_s=1310),
                "8301-bothfire-c": dict(status="complete", wall_s=40.0, limit_s=110)})))
            w = batch2x_report.walls(t)
            self.assertEqual(w["mean_wall_s_of_complete_runs"], {"cal-on": 1000.0, "cal-off": 850.0, "pair": 600.0, "line": 500.0, "bothfire": 40.0})
            self.assertEqual(w["runs"]["8302-cal-on"], dict(kind="cal-on", status="cut at its limit", wall_s=2260.0, limit_s=2260))
            self.assertEqual(batch2x_report.statuses(t)["8301-scan-a-pair"], "complete")


if __name__ == "__main__":
    unittest.main(verbosity=2)
