import Lake
/-!
Helper of `check-integration.sh`: print Lake's text hash of each file given on the command line
(the hash Lake records for a module's source in its `.trace` file).  Run with `lean --run`.
-/
open Lake

def main (args : List String) : IO Unit := do
  for f in args do
    let h ← computeTextFileHash f
    IO.println s!"{h} {f}"
