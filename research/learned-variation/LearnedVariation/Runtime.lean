import LearnedVariation.Learner
import Lean.Data.Json

namespace LearnedVariation.Runtime
open Lean SelfCertifyingLearning

def parseSample (line : String) : Option Sample := do
  match line.splitOn " " with
  | [ts, ys, es] =>
    let time ← ts.toNat?
    let report ← ys.toNat?
    let error ← es.toNat?
    some ⟨time, Renewal.measurement report error⟩
  | _ => none

def parseInitial (line : String) : Option (Policy × State) := do
  match line.splitOn " " with
  | ["init", hs, cs, ws, ts, ns] =>
    let horizon ← hs.toNat?
    let cap ← cs.toNat?
    let window ← ws.toNat?
    let start ← ts.toNat?
    let budget ← ns.toNat?
    let p : Policy := ⟨horizon, cap, window⟩
    if p.Valid then some (p, initial p start budget) else none
  | _ => none

def modeName : Mode → String
  | .validating => "validating-unguaranteed"
  | .provisional => "provisional-unguaranteed"
  | .exhausted => "exhausted-unguaranteed"
  | .fault => "fault-unguaranteed"

def sampleJson (s : Sample) : Json := Json.mkObj [
  ("time", toJson s.time), ("lower", toJson s.interval.lo), ("upper", toJson s.interval.hi)]

def annotationJson (a : Annotation) : Json := Json.mkObj [
  ("through", toJson a.through), ("old_bound", toJson a.oldBound),
  ("required", toJson a.required), ("demonstrated", toJson a.demonstrated),
  ("witnesses", toJson (a.witnesses.map sampleJson)), ("trigger", sampleJson a.trigger)]

def snapshot (p : Policy) (s : State) : Json := Json.mkObj [
  ("mode", toJson (modeName s.mode)), ("bound", toJson s.bound),
  ("next_time", toJson s.nextTime), ("remaining", toJson s.remaining),
  ("window_start", toJson s.windowStart), ("attempts", toJson s.attempts),
  ("credit", toJson s.credit), ("refinements", toJson s.refinements),
  ("can_observe", toJson (s.mode.live && decide (0 < s.credit))),
  ("validation_steps", toJson s.validationSteps), ("history_size", toJson s.history.length),
  ("future_guarantee", toJson false),
  ("proposal", match proposal p s with
    | none => Json.null
    | some e => Json.mkObj [("bound", toJson e.bound), ("horizon", toJson e.horizon),
        ("from", toJson e.fromTime), ("through", toJson e.throughTime)]),
  ("annotations", toJson (s.annotations.reverse.map annotationJson))]

def receive (p : Policy) (s : State) (line : String) : State := step p s (parseSample line)

theorem malformed_fails_closed (p s line) (live : s.mode.live = true) (paid : 0 < s.credit)
    (malformed : parseSample line = none) :
    (receive p s line).mode = .fault ∧ (receive p s line).attempts = s.attempts + 1 := by
  have nonzero : s.credit ≠ 0 := by omega
  simp [receive, malformed, step, live, nonzero, charge]

end LearnedVariation.Runtime
