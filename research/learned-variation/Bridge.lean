import LearnedVariation.Runtime

partial def serve (p : LearnedVariation.Policy) (s : LearnedVariation.State)
    (input : IO.FS.Stream) (output : IO.FS.Stream) : IO Unit := do
  if !s.mode.live || s.credit == 0 then return
  let line ← input.getLine
  if line.isEmpty then return
  let next := LearnedVariation.Runtime.receive p s line.trimAscii.toString
  output.putStrLn ((LearnedVariation.Runtime.snapshot p next).compress)
  output.flush
  serve p next input output

def main : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  let line ← input.getLine
  match LearnedVariation.Runtime.parseInitial line.trimAscii.toString with
  | none => output.putStrLn "ERROR invalid initialization"
  | some (p, s) =>
    output.putStrLn ((LearnedVariation.Runtime.snapshot p s).compress)
    output.flush
    serve p s input output
