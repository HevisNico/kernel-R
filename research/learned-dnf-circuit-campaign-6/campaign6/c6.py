"""Campaign 6 (PREDICTION.md, df1a3cb): its constants and its seed guard. New code. It imports the batch's code and
campaign 5's frozen modules, and edits none of them.

The seed guard. The batch's own guard (batch6.guard_seed) accepts only 7701 to 7710 and the nominal cell, and the
batch's command lines (batch6.main, scan6.main) call it. So campaign 6 never calls those command lines: its runners
call the module functions under this guard, which runs before any deck is written or any simulator starts, and never
patches batch6.SEEDS. Accepted:
  - a campaign seed (7801 to 7805) only in a campaign stage (M1, M2, M3, Q, N1, N2, N3, N) and inside a launch of the kit;
  - a rehearsal seed (7701, 7706) only in the network rehearsal stage RN, inside a launch of the kit;
  - the nominal cell (none) only in the measure rehearsal stages RM1, RM2, RM3, or with no stage (the tests). The
    nominal cell is not required to run inside the kit: it carries no claim, and the tests run it without one.
Every other seed, every other stage, and every other combination is refused.

Instances are named by their seed alone: "7801" to "7805", and "none-a", "none-b" for the two nominal instances of the
measure rehearsal (two distinct instances, measured first on machine a and on machine b). Since amendment 1, an M2 or
M3 run may execute on the other machine than its instance's: the machine that ran it is read from the kit's state file
and recorded as `machine`, the instance's assigned machine as `instance_machine`.

Safeguard (i), as campaign 5's run4.stage_check: every runner takes its stage file (STAGE_<name>.md, written by
stages6 and pushed before the stage's manifest) and refuses the run, before any deck is written, unless that file names
the governing protocol PREDICTION.md with the SHA-256 PROTOCOL_SHA256, and the file in the repository has that SHA-256.
"""
from fractions import Fraction as F
import json
import math
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
BATCH = HERE.parent / "batch"
C5 = HERE.parent.parent / "learned-dnf-circuit-campaign-5"
for p in (str(BATCH), str(C5)):
    if p not in sys.path:
        sys.path.insert(0, p)
import batch6                                           # noqa: E402  (the batch's code, unchanged)
import c4                                               # noqa: E402  (campaign 5, frozen)

BASE = "research/learned-dnf-circuit-campaign-6"
PROTOCOL = f"{BASE}/PREDICTION.md"
PROTOCOL_COMMIT = "df1a3cbcf73ed0ad71e04ded987f756a466e3902"
PROTOCOL_SHA256 = "8e7392c5654975049de3d25adf8a511105fba425fdb07b4d841a12fdc6342240"

SEEDS = (7801, 7802, 7803, 7804, 7805)                  # PREDICTION.md 1: I = 5, never extended
MACHINE_OF = {s: ("a" if i < math.ceil(len(SEEDS) / 2) else "b") for i, s in enumerate(SEEDS)}
REHEARSAL_SEEDS = {7701: "a", 7706: "b"}                # PREDICTION.md 7, R-N: two eligible development instances
DELTA = F(1, 2)                                         # PREDICTION.md 2: option C

CAMPAIGN_STAGES = ("M1", "M2", "M3", "Q", "N1", "N2", "N3", "N")
MEASURE_REHEARSAL = ("RM1", "RM2", "RM3")
NETWORK_REHEARSAL = ("RN",)
STAGES = CAMPAIGN_STAGES + MEASURE_REHEARSAL + NETWORK_REHEARSAL

# The batch's mean wall time of each measure kind (BATCH_REPORT.md 1; REPORT.json on the analysis branch, 0bd3b60)
MEASURE_S = {"cal-on": F("33735174979/41943040"), "cal-off": F("12176667341/18874368"), "pair": F("12451002557/25165824"),
             "line": F("35136838235/75497472"), "bothfire": F("466990469/12582912"), "onesided": F("16565757919/75497472")}
# The network runs' costs at need 4 (STOPPING_RULE.md; PREDICTION.md 4)
QUIET_SKEW_NEED4_S, NOISY_NEED4_S, UNTRAINED_S = F(718), F(1400), F(132)


def limit(expected_s):
    """10 ceil(2 e / 10) (PREDICTION.md 4 and 6)."""
    return c4.limit(expected_s)


def noise_seed(seed, n):
    """10 S + n (PREDICTION.md 4): 78 011 to 78 053 for the campaign, 77 011 and 77 061 for the rehearsal."""
    assert seed is not None and n in (1, 2, 3)
    if seed in REHEARSAL_SEEDS:
        assert n == 1, "the network rehearsal has one noisy run per instance, round 1 (PREDICTION.md 7)"
    return 10 * seed + n


def inside_kit(out):
    """The run's folder is a run the kit started (the kit's STATE.json of the folder above), as run4.inside_kit."""
    state = Path(out).parent / "STATE.json"
    if not state.exists():
        return False
    s = json.loads(state.read_text())
    return s.get("status") == "running" and any(r.get("id") == Path(out).name and r.get("status") == "started" for r in s.get("records", []))


NOMINAL_INSTANCES = {"none-a": "a", "none-b": "b"}


def instance_machine(instance):
    """The machine an instance is assigned to: MACHINE_OF for the campaign, the rehearsal's own for the rest."""
    if instance in NOMINAL_INSTANCES:
        return NOMINAL_INSTANCES[instance]
    seed = int(instance)
    return MACHINE_OF.get(seed, REHEARSAL_SEEDS.get(seed))


def seed_text(instance):
    """An instance's seed as the batch's code reads it: "none" for the nominal instances."""
    return "none" if instance in NOMINAL_INSTANCES else instance


def running_machine(out):
    """The machine the kit runs this run on, from its state file; None outside the kit (the tests)."""
    state = Path(out).parent / "STATE.json" if out is not None else None
    if state is None or not state.exists():
        return None
    return json.loads(state.read_text()).get("machine")


def stage_check(stage_file):
    """Safeguard (i): the stage file's governing protocol is PREDICTION.md with PROTOCOL_SHA256, and the repository's
    file has it. Returns the record's `stage` (as run4.stage_check), refuses otherwise."""
    import hashlib
    import plan
    st = plan.read_stage(stage_file)
    assert st.get("stage") in STAGES, f"refused: {st.get('stage')} is not a stage of campaign 6"
    gov = st["governing_protocol"]
    assert gov["path"] == PROTOCOL and gov["sha256"] == PROTOCOL_SHA256, f"refused (safeguard i): stage {st['stage']} does not name PREDICTION.md as pushed"
    got = hashlib.sha256((HERE.parent.parent.parent / PROTOCOL).read_bytes()).hexdigest()
    assert got == PROTOCOL_SHA256, f"refused (safeguard i): PREDICTION.md has SHA-256 {got} in the repository, not {PROTOCOL_SHA256}"
    return dict(stage=st["stage"], governing_protocol=gov, stage_file_sha256=hashlib.sha256(Path(stage_file).read_bytes()).hexdigest())


def guard_seed(text, stage=None, out=None):
    """The seed of a run, or a refusal (AssertionError) before anything is written. `text` is "none" or a seed."""
    assert stage is None or stage in STAGES, f"refused: {stage} is not a stage of campaign 6"
    if text == "none":
        assert stage is None or stage in MEASURE_REHEARSAL, f"refused: the nominal cell runs only in the measure rehearsal or the tests, not in {stage}"
        return None
    seed = int(text)
    if seed in REHEARSAL_SEEDS:
        assert stage in NETWORK_REHEARSAL, f"refused: development seed {seed} runs only in the network rehearsal, not in {stage}"
    else:
        assert seed in SEEDS, f"refused: seed {seed} is not one of campaign 6's 7801 to 7805"
        assert stage in CAMPAIGN_STAGES, f"refused: campaign seed {seed} runs only in a campaign stage, not in {stage}"
    assert out is not None and inside_kit(out), f"refused: seed {seed} runs only inside a launch of the kit"
    return seed


def run_header(instance, cell, kind, stage, out=None):
    return dict(campaign="learned-dnf-circuit-campaign-6", protocol=PROTOCOL_COMMIT, instance=instance, cell=cell, kind=kind, stage=stage,
                machine=running_machine(out), instance_machine=instance_machine(instance), interpreter=c4.interpreter())


def require_debug():
    batch6.require_debug()
