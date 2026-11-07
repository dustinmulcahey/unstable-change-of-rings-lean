import Lean
import ThesisLean

open Lean

unsafe def main (args : List String) : IO UInt32 := do
  let declFile := args.headD "blueprint/lean_decls"
  let content ← IO.FS.readFile declFile
  let decls := content.splitOn "\n"
    |>.map (fun s => s.trimAscii.toString)
    |>.filter (fun s => !s.isEmpty)
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := `ThesisLean }] {} 0
  let mut missing : List String := []
  for d in decls do
    let name := d.toName
    if !env.contains name then
      IO.eprintln s!"Missing declaration: {d}"
      missing := d :: missing
  if missing.isEmpty then
    IO.println s!"All {decls.length} blueprint declarations verified in ThesisLean!"
    return 0
  else
    return 1
