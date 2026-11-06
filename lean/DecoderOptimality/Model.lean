import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Function.Basic

/-!
# The single-output LUT model of the paper

A LUT network over `n` inputs is a list of nodes in build order. Node `j` has `K` pins and an arbitrary
table over the `K` pin values. A pin reads a signal, directly or through an inverter: the signal is a
primary input, an earlier node, or a constant. Reading through an inverter costs nothing, a constant
costs nothing, and a wire needs no node, so this is the paper's convention that constants, buffers and
inversions are free. Every node is a counted LUT.

The network computes the `n`-input decoder when, for every pattern `q`, some node computes the minterm
of `q`, directly or through a free output inverter (`computesDecoder`).
-/

namespace DecoderOptimality

/-- A signal a pin can read. -/
inductive Signal (n : Nat) where
  | input (i : Fin n)
  | node (j : Nat)
  | const (b : Bool)
  deriving DecidableEq, Repr

/-- A pin: a signal, read directly (`neg = false`) or through a free inverter (`neg = true`). -/
structure Pin (n : Nat) where
  sig : Signal n
  neg : Bool
  deriving DecidableEq, Repr

/-- One lookup table: `K` pins and a table over the pin values. -/
structure Lut (n K : Nat) where
  pins : Fin K → Pin n
  table : (Fin K → Bool) → Bool

/-- A network: nodes in build order. Node `j` may read node `j'` only when `j' < j`. -/
structure Network (n K : Nat) where
  nodes : Array (Lut n K)
  acyclic : ∀ (j : Nat) (h : j < nodes.size) (p : Fin K) (j' : Nat),
    ((nodes[j]'h).pins p).sig = Signal.node j' → j' < j

/-- The minterm of pattern `q`: true exactly at `q`. -/
def minterm {n : Nat} (q : Fin n → Bool) : (Fin n → Bool) → Bool :=
  fun x => decide (x = q)

/-- Flip pattern `q` at coordinate `i`. -/
def flip {n : Nat} (q : Fin n → Bool) (i : Fin n) : Fin n → Bool :=
  Function.update q i (!q i)

namespace Network

variable {n K : Nat}

/-- The function computed by node `j`; a node index outside the network computes `false`.
A pin naming a node at or beyond `j` reads `false`; by `acyclic` this never happens in a network. -/
def nodeFun (net : Network n K) (j : Nat) (x : Fin n → Bool) : Bool :=
  if h : j < net.nodes.size then
    (net.nodes[j]'h).table fun p =>
      Bool.xor ((net.nodes[j]'h).pins p).neg
        (match ((net.nodes[j]'h).pins p).sig with
          | .input i => x i
          | .const b => b
          | .node j' => if h' : j' < j then net.nodeFun j' x else false)
  else false
termination_by j

/-- The value of a signal at input pattern `x`. -/
def sigVal (net : Network n K) (x : Fin n → Bool) : Signal n → Bool
  | .input i => x i
  | .const b => b
  | .node j => net.nodeFun j x

/-- The value a pin delivers at input pattern `x`. -/
def pinVal (net : Network n K) (x : Fin n → Bool) (pin : Pin n) : Bool :=
  Bool.xor pin.neg (net.sigVal x pin.sig)

/-- One step of `nodeFun`: the table applied to the pin values. -/
theorem nodeFun_eq (net : Network n K) (j : Nat) (h : j < net.nodes.size) (x : Fin n → Bool) :
    net.nodeFun j x = (net.nodes[j]'h).table fun p => net.pinVal x ((net.nodes[j]'h).pins p) := by
  rw [nodeFun, dif_pos h]
  congr 1
  funext p
  rcases hs : ((net.nodes[j]'h).pins p).sig with i | j' | b
  · simp [pinVal, sigVal, hs]
  · have hj : j' < j := net.acyclic j h p j' hs
    simp [pinVal, sigVal, hs, hj]
  · simp [pinVal, sigVal, hs]

/-- The function of node `j` read through polarity `b` (`b = true` inverts): a free output inverter. -/
def signed (net : Network n K) (j : Nat) (b : Bool) : (Fin n → Bool) → Bool :=
  fun x => Bool.xor b (net.nodeFun j x)

/-- `net` computes the `n`-input decoder: every minterm is some node, up to a free inverter.
Asking for a node loses no generality against a model whose outputs may also be constants or wires: for
`n ≥ 2` the minterm of `q` is true on exactly one of the `2 ^ n` patterns, a constant on none or all of them,
and a primary input, direct or inverted, on exactly half, so no constant, input or inverted input is a decoder
output. For the 8-input decoder the counts are 1 against 0, 256 and 128. -/
def computesDecoder (net : Network n K) : Prop :=
  ∀ q : Fin n → Bool, ∃ j, j < net.nodes.size ∧ ∃ b : Bool, net.signed j b = minterm q

end Network

/-! ### Minterms and flips -/

variable {n : Nat}

@[simp] theorem minterm_self (q : Fin n → Bool) : minterm q q = true := by
  simp [minterm]

theorem minterm_of_ne {x q : Fin n → Bool} (h : x ≠ q) : minterm q x = false := by
  simp [minterm, h]

theorem minterm_injective : Function.Injective (minterm (n := n)) := by
  intro q q' h
  by_contra hne
  have := congrFun h q
  simp [minterm, hne] at this

theorem flip_apply_self (q : Fin n → Bool) (i : Fin n) : flip q i i = !q i := by
  simp [flip]

theorem flip_apply_of_ne (q : Fin n → Bool) {i r : Fin n} (h : r ≠ i) : flip q i r = q r := by
  simp [flip, Function.update_apply, h]

theorem flip_ne (q : Fin n → Bool) (i : Fin n) : flip q i ≠ q := by
  intro h
  have := congrFun h i
  simp [flip] at this

theorem flip_flip (q : Fin n → Bool) (i : Fin n) : flip (flip q i) i = q := by
  funext r
  by_cases hr : r = i
  · subst hr; simp [flip_apply_self]
  · rw [flip_apply_of_ne _ hr, flip_apply_of_ne _ hr]

theorem flip_injective (q : Fin n → Bool) : Function.Injective (flip q) := by
  intro i j h
  by_contra hij
  have := congrFun h i
  rw [flip_apply_self, flip_apply_of_ne q hij] at this
  cases q i <;> simp at this

theorem flip_left_injective (i : Fin n) : Function.Injective (fun q : Fin n → Bool => flip q i) := by
  intro q q' h
  have := congrArg (fun r => flip r i) h
  simpa [flip_flip] using this

/-- Two patterns with at least two inputs: some third pattern differs from both. -/
theorem exists_ne_ne (hn : 2 ≤ n) (q q' : Fin n → Bool) : ∃ x, x ≠ q ∧ x ≠ q' := by
  have h0 : (0 : Nat) < n := by omega
  have h1 : (1 : Nat) < n := by omega
  by_cases hc : flip q ⟨0, h0⟩ = q'
  · refine ⟨flip q ⟨1, h1⟩, flip_ne q _, ?_⟩
    rw [← hc]
    intro h'
    have := flip_injective q h'
    simp [Fin.ext_iff] at this
  · exact ⟨flip q ⟨0, h0⟩, flip_ne q _, hc⟩

/-- A minterm is never the complement of a minterm. -/
theorem minterm_ne_not (hn : 2 ≤ n) (q q' : Fin n → Bool) : minterm q ≠ fun x => !minterm q' x := by
  intro h
  obtain ⟨x, hxq, hxq'⟩ := exists_ne_ne hn q q'
  have := congrFun h x
  simp [minterm, hxq, hxq'] at this

end DecoderOptimality
