import RefusalRecovery.Runtime

partial def serve (input : IO.FS.Stream) (output : IO.FS.Stream) : IO Unit := do
  let line ← input.getLine
  if line.isEmpty then return
  output.putStrLn (RefusalRecovery.Runtime.response line.trimAscii.toString)
  output.flush
  serve input output

def main : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  output.putStrLn "READY"
  output.flush
  serve input output
