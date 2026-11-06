import Std.Sat.CNF
import Std.Sat.CNF.Dimacs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card

/-!
# The 64-point question as CNF

Points `z < 64` are the patterns on the six inputs of `Y`; bit `k` of `z` is the value of input `k`. A free
set is a mask `m < 64` with at least three bits (`valid`); its bound is `u = pop m - 3`. The members of the
`m`-subcube of `z` other than `z` are the points `z ^^^ s` for the nonzero `s ⊆ m` (`member m s`).

Atoms, each block closed-form in its indices:
* `yA z` (`z < 64`): the value `Y z`; `yA 0` is forced false, complementing `Y` changes nothing.
* `pA a b` (`a < b < 64`): `a` is built before `b`; `prec a b` is that literal for any `a ≠ b`.
* `cA z m`: option `(z, m)` is the free set of `z`.
* `gA z m s`: guard, `cA z m ∧ (Y z ↔ Y (z ^^^ s))`, one per member.
* `sA z m i j`: register `j` of the sequential counter of option `(z, m)` after position `i`.
* `falseA`: an atom forced false, the literal of the non-member positions of each counter.

Clauses: `yA 0` false; `falseA` false; transitivity of `prec` on every ordered triple of distinct points;
for every point some valid option; for every option and member: a class member is built before `z`
(`cA ∧ eq → prec`), the guard definition, and Sinz's sequential counter bounding the guards by `u`.
-/

namespace DecoderOptimality.Bound

open Std.Sat

abbrev Lit := Literal Nat

def pos (a : Nat) : Lit := (a, true)
def neg (a : Nat) : Lit := (a, false)
def flipLit (l : Lit) : Lit := (l.1, !l.2)

/-- A clause from its literals. -/
def cl (l : List Lit) : CNF.Clause Nat :=
  l.foldl (fun c x => c.add x.1 x.2) CNF.Clause.empty

/-- Number of set bits among the six low bits of `m`. -/
def pop (m : Nat) : Nat := (Finset.univ.filter fun k : Fin 6 => m.testBit k = true).card

/-- A free set has at least three inputs. -/
def valid (m : Nat) : Bool := decide (3 ≤ pop m)

/-- The number of other outputs an option may read. -/
def bound (m : Nat) : Nat := pop m - 3

/-- The bits of `s` lie inside the bits of `m`. -/
def sub (s m : Nat) : Bool := decide (∀ k : Fin 6, s.testBit k = true → m.testBit k = true)

/-- `z ^^^ s` is a member of the `m`-subcube of `z` other than `z`. -/
def member (m s : Nat) : Bool := (s != 0) && sub s m

def yA (z : Nat) : Nat := z
def pA (a b : Nat) : Nat := 64 + 64 * a + b
def cA (z m : Nat) : Nat := 4160 + 64 * z + m
def gA (z m s : Nat) : Nat := 8256 + 4096 * z + 64 * m + s
def sA (z m i j : Nat) : Nat := 270400 + 16384 * z + 256 * m + 4 * i + j
def falseA : Nat := 1318976

/-- The literal "a is built before b", for `a ≠ b`. -/
def prec (a b : Nat) : Lit := if a < b then pos (pA a b) else neg (pA b a)

def unitClauses : List (CNF.Clause Nat) := [cl [neg (yA 0)], cl [neg falseA]]

def transClauses : List (CNF.Clause Nat) :=
  (List.range 64).flatMap fun a => (List.range 64).flatMap fun b => (List.range 64).filterMap fun c =>
    if a ≠ b ∧ b ≠ c ∧ a ≠ c then some (cl [flipLit (prec a b), flipLit (prec b c), prec a c]) else none

/-- Some valid option holds for `z`. -/
def optionClause (z : Nat) : CNF.Clause Nat :=
  cl ((List.range 64).filterMap fun m => if valid m then some (pos (cA z m)) else none)

/-- The clauses of member `z ^^^ s` of option `(z, m)`: a class member precedes `z`, and the guard. -/
def memberClauses (z m s : Nat) : List (CNF.Clause Nat) :=
  [ cl [neg (cA z m), neg (yA z), neg (yA (z ^^^ s)), prec (z ^^^ s) z],
    cl [neg (cA z m), pos (yA z), pos (yA (z ^^^ s)), prec (z ^^^ s) z],
    cl [neg (gA z m s), pos (cA z m)],
    cl [neg (gA z m s), neg (yA z), pos (yA (z ^^^ s))],
    cl [neg (gA z m s), pos (yA z), neg (yA (z ^^^ s))],
    cl [pos (gA z m s), neg (cA z m), neg (yA z), neg (yA (z ^^^ s))],
    cl [pos (gA z m s), neg (cA z m), pos (yA z), pos (yA (z ^^^ s))] ]

/-- The counted literal at position `s` of option `(z, m)`: its guard for a member, else the false atom. -/
def guardLit (z m s : Nat) : Lit := if member m s then pos (gA z m s) else pos falseA

/-- Sinz's sequential counter: at most `k` of `lit 0, …, lit (L-1)`, registers `reg i j`, `k ≥ 1`. -/
def counterClauses (L k : Nat) (lit : Nat → Lit) (reg : Nat → Nat → Nat) : List (CNF.Clause Nat) :=
  (List.range L).flatMap fun i =>
    cl [flipLit (lit i), pos (reg i 0)] ::
    (if i = 0 then [] else
      ((List.range k).map fun j => cl [neg (reg (i - 1) j), pos (reg i j)]) ++
      ((List.range k).filterMap fun j =>
        if j = 0 then none else some (cl [flipLit (lit i), neg (reg (i - 1) (j - 1)), pos (reg i j)])) ++
      [cl [flipLit (lit i), neg (reg (i - 1) (k - 1))]])

/-- At most `bound m` guards of option `(z, m)` hold. -/
def atMostClauses (z m : Nat) : List (CNF.Clause Nat) :=
  if bound m = 0 then (List.range 64).map fun s => cl [flipLit (guardLit z m s)]
  else counterClauses 64 (bound m) (guardLit z m) (sA z m)

/-- The members of mask `m`, in increasing order. -/
def members (m : Nat) : List Nat :=
  (List.range 64).filterMap fun s => if member m s then some s else none

def optionClauses (z m : Nat) : List (CNF.Clause Nat) :=
  if valid m then (members m).flatMap (memberClauses z m) ++ atMostClauses z m else []

def pointClauses (z : Nat) : List (CNF.Clause Nat) :=
  optionClause z :: (List.range 64).flatMap (optionClauses z)

def clauses : List (CNF.Clause Nat) :=
  unitClauses ++ transClauses ++ (List.range 64).flatMap pointClauses

/-- The formula. -/
def cnf : CNF Nat := ⟨clauses.toArray⟩

/-! ### Semantics of the building blocks -/

theorem eval_foldl (a : Nat → Bool) (l : List Lit) (c : CNF.Clause Nat) :
    (l.foldl (fun c x => c.add x.1 x.2) c).eval a = (c.eval a || l.any fun x => a x.1 == x.2) := by
  induction l generalizing c with
  | nil => simp
  | cons x l ih =>
    rw [List.foldl_cons, ih, CNF.Clause.eval_add, List.any_cons]
    cases CNF.Clause.eval a c <;> cases (a x.1 == x.2) <;> simp

theorem eval_cl_iff (a : Nat → Bool) (l : List Lit) :
    (cl l).eval a = true ↔ ∃ x ∈ l, a x.1 = x.2 := by
  unfold cl
  rw [eval_foldl, CNF.Clause.eval_empty, Bool.false_or, List.any_eq_true]
  constructor
  · rintro ⟨x, hx, h⟩
    exact ⟨x, hx, by simpa using h⟩
  · rintro ⟨x, hx, h⟩
    exact ⟨x, hx, by simpa using h⟩

theorem sat_iff (a : Nat → Bool) : CNF.Sat a cnf ↔ ∀ c ∈ clauses, c.eval a = true := by
  show CNF.eval a cnf = true ↔ _
  unfold CNF.eval cnf
  rw [Array.all_eq_true_iff_forall_mem]
  constructor
  · intro h c hc
    exact h c (List.mem_toArray.mpr hc)
  · intro h c hc
    exact h c (List.mem_toArray.mp hc)

theorem mem_members {m s : Nat} : s ∈ members m ↔ s < 64 ∧ member m s = true := by
  unfold members
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨t, ht, hts⟩
    rw [List.mem_range] at ht
    split at hts
    · cases hts
      exact ⟨ht, by assumption⟩
    · cases hts
  · rintro ⟨hs, hm⟩
    exact ⟨s, List.mem_range.mpr hs, by rw [if_pos hm]⟩

theorem pop_le (m : Nat) : pop m ≤ 6 := by
  unfold pop
  exact (Finset.card_le_univ _).trans (by simp)

theorem bound_le (m : Nat) : bound m ≤ 3 := by
  unfold bound
  have := pop_le m
  omega

theorem bound_pos_of_valid {m : Nat} (h : valid m = true) (hb : bound m ≠ 0) : 0 < bound m := by
  omega

end DecoderOptimality.Bound
