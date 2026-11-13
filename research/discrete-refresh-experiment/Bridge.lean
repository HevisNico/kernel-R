import SelfCertifyingLearning.ClosedLoop
import SelfCertifyingLearning.Renewal

/-! Calls frozen #111 definitions. Input: signed reserve report, rate report,
anchor rate report, delivery flag. No truth or jump time is supplied. -/
open SelfCertifyingLearning

def experimentConfig : Repair.Config := ⟨100, 22, 1, 220, 660, 40⟩
theorem experimentConfig_valid : experimentConfig.Valid := by decide

def respond (line : String) : String :=
  match line.splitOn " " with
  | [xs, rs, ans, ds] =>
    match xs.toInt?, rs.toNat?, ans.toNat?, ds.toNat? with
    | some x, some rate, some anchor, some delivered =>
      if delivered > 1 then "ERROR delivery flag" else
      let lower := if delivered = 1 then min (660 : Int) (x - 2 + 220) else x - 2
      let reviewed := Renewal.review 5 (Renewal.measurement anchor 1) (Renewal.measurement rate 1)
      let newAnchor := if reviewed.2 then rate else anchor
      let action := if lower < 0 then ClosedLoop.Action.refuse
        else ClosedLoop.choose experimentConfig lower.toNat
      let kind := match action with
        | .wait _ => "wait"
        | .write => "write"
        | .refuse => "refuse"
      s!"{lower} {kind} {ClosedLoop.duration experimentConfig action} {newAnchor} {if reviewed.2 then 1 else 0}"
    | _, _, _, _ => "ERROR numeric input"
  | _ => "ERROR field count"

partial def serve (input : IO.FS.Stream) (output : IO.FS.Stream) : IO Unit := do
  let line ← input.getLine
  if line.isEmpty then return
  output.putStrLn (respond line.trimAscii.toString)
  output.flush
  serve input output

def main : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  output.putStrLn "READY"
  output.flush
  serve input output
