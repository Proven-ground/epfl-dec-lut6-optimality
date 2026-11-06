import Std.Tactic.BVDecide.Reflect
import DecoderOptimality.Encoder

/-!
# The certified refutation

`cert` is CaDiCaL's LRAT refutation of `Bound.cnf` in text form, read into the module at compile time.
`Std.Tactic.BVDecide.Reflect.verifyCert` parses it and runs Lean's LRAT checker, whose soundness is the library
theorem `verifyCert_correct`. The check itself is evaluated by the compiled code, so `cert_ok` depends on
the axiom `native_decide` generates for it, `cert_ok._native.native_decide.ax_1_1` in the recorded build, which
records that Lean's native compiler evaluated the check to `true`.
-/

namespace DecoderOptimality.Certificate

/-- The LRAT refutation, as produced by `cadical --lrat --binary=false` on the emitted DIMACS. -/
def cert : String := include_str "../bound.lrat"

theorem cert_ok : Std.Tactic.BVDecide.Reflect.verifyCert Bound.cnf cert = true := by
  native_decide

theorem unsat : Bound.cnf.Unsat :=
  Std.Tactic.BVDecide.Reflect.verifyCert_correct _ _ cert_ok

end DecoderOptimality.Certificate
