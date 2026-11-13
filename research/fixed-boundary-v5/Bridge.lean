import Model

namespace FixedBoundaryV5

def actionName : Action → String
  | .wait1 => "wait"
  | .wait2 => "wait"
  | .write => "write"
  | .refuse => "refuse"

/-- policy(0 prudent,1 early), reserve report, rate report, delivery(0/1), carry.
No state truth, future losses, seeds or scenario identity enter this interface. -/
def response (line : String) : String :=
  match line.splitOn " " with
  | [ps, rs, ls, ds, cs] =>
    match ps.toNat?, rs.toInt?, ls.toInt?, ds.toNat?, cs.toInt? with
    | some p, some report, some rate, some delivered, some carried =>
      if p > 1 || delivered > 1 then "ERROR enum" else
      let policy := if p = 1 then Policy.early else Policy.prudent
      let reply := kernel policy report rate (delivered = 1) carried
      s!"{actionName reply.action} {duration reply.action} {reply.lower} {reply.upper} {reply.nextCarry}"
    | _, _, _, _, _ => "ERROR number"
  | _ => "ERROR fields"

end FixedBoundaryV5

partial def serve (input output : IO.FS.Stream) : IO Unit := do
  let line ← input.getLine
  if line.isEmpty then return
  output.putStrLn (FixedBoundaryV5.response line.trimAscii.toString)
  output.flush
  serve input output

def main : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  output.putStrLn "READY"
  output.flush
  serve input output
