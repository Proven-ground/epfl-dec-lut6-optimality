import DecoderOptimality.Encoder

/-- Write `Bound.cnf` as DIMACS with Lean's own writer (atom `v` becomes DIMACS variable `v + 1`). -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
    IO.FS.writeFile path (Std.Sat.CNF.dimacs DecoderOptimality.Bound.cnf)
    IO.println s!"wrote {DecoderOptimality.Bound.cnf.clauses.size} clauses to {path}"
    return 0
  | _ =>
    IO.eprintln "usage: emit OUT.cnf"
    return 2
