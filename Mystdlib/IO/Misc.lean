import Lean

-- get terminal device path with `tty`
def printToTerminal (termPath : String) (message : String) : IO Unit := do
  let handle ← IO.FS.Handle.mk termPath IO.FS.Mode.write
  handle.putStr message
  handle.flush

open Lean Elab Command in
def printLogsToTerminal (termPath : String) [Monad m] [MonadStateOf Lean.Core.State m] [MonadLift m CommandElabM] (x : m α) : CommandElabM Unit := do
  let aux := x >>= fun _ => getThe Core.State
  for i in (<- aux).messages.toList do printToTerminal termPath (<- i.toString)



  
