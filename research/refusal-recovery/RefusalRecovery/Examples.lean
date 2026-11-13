import RefusalRecovery.Machine
import RefusalRecovery.Restoration
import SelfCertifyingLearning.RepairPlant

namespace RefusalRecovery.Examples
open SelfCertifyingLearning

def hardware : Hardware := ⟨100, 220, 660, 40, 8, 2⟩
def start : State := enter 0 0 false
def permit : Permit := ⟨1, 5, 85, 150, 2⟩
def readyReading : Reading := ⟨5, 68, true⟩
def readyState : State := ⟨1, 5, true⟩

def inputs (s : State) : Option Reading × Option Permit :=
  let report := if s.now = 0 then -62 else -212 + 70 * ((s.now : Int) - 1)
  (some ⟨s.now, report, s.pending⟩, if s.now = 5 then some permit else none)

theorem five_repairs_then_resume :
    (run hardware inputs 5 start).map Frame.action =
      [.repair, .repair, .repair, .repair, .repair, .resume permit] := by decide

theorem recovery_claims_remain_limited :
    (run hardware inputs 5 start).map Frame.sampledSafe =
      [false, false, false, false, false, false] := by decide

theorem complete_recovery_bill : cost 1 10 (run hardware inputs 5 start) = 56 := by decide

theorem permit_admitted : Admissible hardware readyState readyReading permit := by decide

theorem resumed_witness_service :
    SafeUntil (RepairPlant.simulate (config hardware permit) 2 286) 100
      (ClosedLoop.clock (config hardware permit) 2 286) :=
  RepairPlant.simulated_service (by decide) 2 (by decide)

theorem negative_entry_rejected :
    authorized hardware start ⟨0, -62, false⟩ { permit with issued := 0 } = false := by decide

theorem insufficient_buffer_rejected :
    authorized hardware readyState ⟨5, 0, true⟩ permit = false := by decide

theorem stale_generation_rejected :
    authorized hardware readyState readyReading { permit with generation := 0 } = false := by decide

theorem stale_issue_rejected :
    authorized hardware readyState readyReading { permit with issued := 4 } = false := by decide

theorem short_expiry_rejected :
    authorized hardware readyState readyReading { permit with expires := 6 } = false := by decide

theorem zero_gain_rejected :
    authorized hardware readyState readyReading { permit with bound := 220 } = false := by decide

theorem empty_phase_rejected :
    authorized hardware readyState readyReading { permit with decisions := 0 } = false := by decide

theorem phase_limit_rejected :
    authorized hardware readyState readyReading { permit with decisions := 9 } = false := by decide

theorem stale_probe_faults :
    choose hardware readyState 2 (some { readyReading with time := 4 }) (some permit) = .fault := by decide

theorem missing_probe_faults :
    choose hardware readyState 2 none (some permit) = .fault := by decide

theorem missing_delivery_faults :
    choose hardware readyState 2 (some { readyReading with delivered := false }) (some permit) = .fault := by decide

theorem endpoint_no_command :
    choose hardware start 0 (some ⟨0, -62, false⟩) none = .exhausted := by decide

theorem unavailable_exhausts :
    (run hardware (fun s => (some ⟨s.now, -1000, s.pending⟩, none)) 3 start).map Frame.action =
      [.repair, .repair, .repair, .exhausted] := by decide

theorem second_refusal_cannot_reuse_permit :
    choose hardware (enter 1 10 false) 2 (some ⟨10, 400, false⟩)
      (some { permit with issued := 10 }) = .repair := by decide

theorem adequate_reserve_alone_does_not_resume :
    choose hardware start 1 (some ⟨0, 662, false⟩) none = .repair := by decide

end RefusalRecovery.Examples
