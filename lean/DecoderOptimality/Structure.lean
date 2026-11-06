import DecoderOptimality.Lemma1
import DecoderOptimality.Lemma2
import DecoderOptimality.Reduced

/-!
# From a network of at most `2 ^ n + 1` LUTs to the reduced object

Let `out q` be the first node computing the minterm of `q` (Lemma 1). The image of `out` has `2 ^ n`
elements, so at most one node index is not an output. By Lemma 2 every output node reads a node that is
not an output; hence that node `Y` exists, is unique, precedes every output, and reads inputs only. For
the output `q`, `R` is the set of inputs it reads, `P` the set of patterns whose outputs it reads, and
`F = Rᶜ`. One pin reads `Y`, so `|R| + |P| ≤ K - 1` and `|F| ≥ n - K + 1 + |P|`. A pattern `x ≠ q` that
agrees with `q` outside `F`, has `Y x = Y q` and is not in `P` presents the node with the pin values of
`q`, so it is in `P` after all, and its output was built before `q`.
-/

namespace DecoderOptimality

open Finset

variable {n K : Nat}

/-- The input a pin reads; a junk value for other pins. -/
def inputOf (h0 : 0 < n) (pin : Pin n) : Fin n :=
  match pin.sig with
  | .input i => i
  | _ => ⟨0, h0⟩

/-- The node a pin reads; a junk value for other pins. -/
def nodeOf (pin : Pin n) : Nat :=
  match pin.sig with
  | .node j => j
  | _ => 0

theorem inputOf_input (h0 : 0 < n) {pin : Pin n} {i : Fin n} (h : pin.sig = .input i) :
    inputOf h0 pin = i := by
  simp [inputOf, h]

theorem nodeOf_node {pin : Pin n} {j : Nat} (h : pin.sig = .node j) : nodeOf pin = j := by
  simp [nodeOf, h]

/-- Two patterns on which every pin of node `j` reads the same value give the same node value. -/
theorem Network.nodeFun_congr (net : Network n K) {j : Nat} (h : j < net.nodes.size)
    {x x' : Fin n → Bool}
    (hp : ∀ p : Fin K, net.pinVal x ((net.nodes[j]'h).pins p) = net.pinVal x' ((net.nodes[j]'h).pins p)) :
    net.nodeFun j x = net.nodeFun j x' := by
  rw [net.nodeFun_eq j h x, net.nodeFun_eq j h x']
  congr 1
  funext p
  exact hp p

theorem reduce (net : Network n K) (hK : 1 ≤ K) (hnK : K < n) (hdec : net.computesDecoder)
    (hsize : net.nodes.size ≤ 2 ^ n + 1) : Nonempty (Reduced n K) := by
  classical
  have hn : 2 ≤ n := by omega
  have h0 : 0 < n := by omega
  have oinj := out_injective net hdec hn
  have olt := out_lt net hdec
  have ospec := out_spec net hdec
  -- the set of output node indices
  obtain ⟨I, hI⟩ : ∃ I : Finset Nat, I = univ.image (out net hdec) := ⟨_, rfl⟩
  have memI : ∀ j, j ∈ I ↔ ∃ q, out net hdec q = j := by
    intro j; rw [hI, mem_image]; simp
  have hIcard : I.card = 2 ^ n := by
    rw [hI, card_image_of_injective _ oinj, card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin]
  have hIsub : I ⊆ range net.nodes.size := by
    intro j hj
    obtain ⟨q, rfl⟩ := (memI j).mp hj
    exact mem_range.mpr (olt q)
  have hextra : (range net.nodes.size \ I).card ≤ 1 := by
    rw [card_sdiff_of_subset hIsub, card_range, hIcard]
    generalize 2 ^ n = M at *
    omega
  -- Claim A: every output node reads a node that is not an output.
  have claimA : ∀ q : Fin n → Bool, ∃ p : Fin K, ∃ e,
      ((net.nodes[out net hdec q]'(olt q)).pins p).sig = Signal.node e ∧ e ∉ I := by
    intro q
    by_contra hcon
    push_neg at hcon
    have htr : ∀ p : Fin K, ∃ r : Read n q,
        ∀ x, net.pinVal x ((net.nodes[out net hdec q]'(olt q)).pins p) = r.eval x := by
      intro p
      rcases hs : ((net.nodes[out net hdec q]'(olt q)).pins p).sig with i | e | c
      · exact ⟨.input i ((net.nodes[out net hdec q]'(olt q)).pins p).neg,
          fun x => by simp [Network.pinVal, Network.sigVal, hs, Read.eval]⟩
      · have heI := hcon p e hs
        obtain ⟨p', hp'⟩ := (memI e).mp heI
        have hlt : e < out net hdec q := net.acyclic _ (olt q) p e hs
        have hne : p' ≠ q := by
          rintro rfl
          omega
        obtain ⟨b', hb'⟩ := ospec p'
        refine ⟨.other p' hne (Bool.xor ((net.nodes[out net hdec q]'(olt q)).pins p).neg b'),
          fun x => ?_⟩
        have hx := congrFun hb' x
        simp only [Network.signed] at hx
        rw [hp'] at hx
        simp only [Network.pinVal, Network.sigVal, hs, Read.eval]
        rw [← hx, Bool.xor_assoc, ← Bool.xor_assoc b' b', Bool.xor_self, Bool.false_xor]
      · exact ⟨.const (Bool.xor ((net.nodes[out net hdec q]'(olt q)).pins p).neg c),
          fun x => by simp [Network.pinVal, Network.sigVal, hs, Read.eval]⟩
    obtain ⟨b, hb⟩ := ospec q
    apply lemma2 hnK q (fun p => Classical.choose (htr p)) (net.nodes[out net hdec q]'(olt q)).table b
    rw [← hb]
    funext x
    simp only [Network.signed]
    rw [net.nodeFun_eq (out net hdec q) (olt q) x]
    have hp : (fun p => (Classical.choose (htr p)).eval x) =
        fun p => net.pinVal x ((net.nodes[out net hdec q]'(olt q)).pins p) :=
      funext fun p => (Classical.choose_spec (htr p) x).symm
    rw [hp]
  -- The non-output node Y.
  obtain ⟨p₀, Y, hp₀, hYI⟩ := claimA (fun _ => false)
  have hY : Y < net.nodes.size :=
    lt_trans (net.acyclic _ (olt _) p₀ Y hp₀) (olt _)
  have huniq : ∀ e, e < net.nodes.size → e ∉ I → e = Y := by
    intro e he heI
    have h1 : e ∈ range net.nodes.size \ I := mem_sdiff.mpr ⟨mem_range.mpr he, heI⟩
    have h2 : Y ∈ range net.nodes.size \ I := mem_sdiff.mpr ⟨mem_range.mpr hY, hYI⟩
    exact card_le_one.mp hextra e h1 Y h2
  -- Claim B: every output reads Y, so Y precedes every output.
  have claimB : ∀ q : Fin n → Bool, ∃ p : Fin K,
      ((net.nodes[out net hdec q]'(olt q)).pins p).sig = Signal.node Y := by
    intro q
    obtain ⟨p, e, hs, heI⟩ := claimA q
    have he : e < net.nodes.size := lt_trans (net.acyclic _ (olt q) p e hs) (olt q)
    rw [huniq e he heI] at hs
    exact ⟨p, hs⟩
  have hYlt : ∀ q : Fin n → Bool, Y < out net hdec q := by
    intro q
    obtain ⟨p, hs⟩ := claimB q
    exact net.acyclic _ (olt q) p Y hs
  -- Claim C: Y reads no node.
  have claimC : ∀ (p : Fin K) (e : Nat), ((net.nodes[Y]'hY).pins p).sig ≠ Signal.node e := by
    intro p e hs
    have hlt : e < Y := net.acyclic Y hY p e hs
    by_cases heI : e ∈ I
    · obtain ⟨q, rfl⟩ := (memI e).mp heI
      exact absurd (hYlt q) (by omega)
    · have := huniq e (lt_trans hlt hY) heI
      omega
  -- The inputs Y reads (with a junk input for constant pins, harmless as a superset).
  obtain ⟨V, hV⟩ : ∃ V : Finset (Fin n),
      V = univ.image fun p : Fin K => inputOf h0 ((net.nodes[Y]'hY).pins p) := ⟨_, rfl⟩
  have hVcard : V.card ≤ K := by
    rw [hV]
    exact card_image_le.trans (by simp)
  have hign : ∀ x x' : Fin n → Bool, (∀ i ∈ V, x i = x' i) → net.nodeFun Y x = net.nodeFun Y x' := by
    intro x x' hxx
    apply net.nodeFun_congr hY
    intro p
    rcases hs : ((net.nodes[Y]'hY).pins p).sig with i | e | c
    · have hi : i ∈ V := by
        rw [hV, mem_image]
        exact ⟨p, mem_univ _, inputOf_input h0 hs⟩
      simp [Network.pinVal, Network.sigVal, hs, hxx i hi]
    · exact absurd hs (claimC p e)
    · simp [Network.pinVal, Network.sigVal, hs]
  -- The admissible pair of each output.
  have hadm : ∀ q : Fin n → Bool, ∃ (F : Finset (Fin n)) (u : Nat),
      n - K + 1 + u ≤ F.card ∧ Admissible (net.nodeFun Y) (out net hdec) q F u := by
    intro q
    have hq := olt q
    -- pin classes of the node of q: input pins, other-output pins, Y pins
    obtain ⟨A, hA⟩ : ∃ A : Finset (Fin K), A = univ.filter fun p =>
        ∃ i, ((net.nodes[out net hdec q]'hq).pins p).sig = Signal.input i := ⟨_, rfl⟩
    obtain ⟨B, hB⟩ : ∃ B : Finset (Fin K), B = univ.filter fun p =>
        ∃ e, ((net.nodes[out net hdec q]'hq).pins p).sig = Signal.node e ∧ e ∈ I := ⟨_, rfl⟩
    obtain ⟨C, hC⟩ : ∃ C : Finset (Fin K), C = univ.filter fun p =>
        ((net.nodes[out net hdec q]'hq).pins p).sig = Signal.node Y := ⟨_, rfl⟩
    have hAB : Disjoint A B := by
      rw [hA, hB, disjoint_filter]
      rintro p - ⟨i, hi⟩ ⟨e, he, -⟩
      rw [hi] at he
      cases he
    have hAC : Disjoint A C := by
      rw [hA, hC, disjoint_filter]
      rintro p - ⟨i, hi⟩ he
      rw [hi] at he
      cases he
    have hBC : Disjoint B C := by
      rw [hB, hC, disjoint_filter]
      rintro p - ⟨e, he, heI⟩ hY'
      rw [hY'] at he
      cases he
      exact hYI heI
    have hsum : A.card + B.card + C.card ≤ K := by
      have h1 : (A ∪ B ∪ C).card ≤ K := (card_le_univ _).trans (by simp)
      rw [card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hAC, hBC⟩),
        card_union_of_disjoint hAB] at h1
      exact h1
    have hCpos : 0 < C.card := by
      obtain ⟨p, hp⟩ := claimB q
      exact card_pos.mpr ⟨p, by rw [hC, mem_filter]; exact ⟨mem_univ _, hp⟩⟩
    -- the inputs read
    obtain ⟨R, hR⟩ : ∃ R : Finset (Fin n),
        R = A.image fun p => inputOf h0 ((net.nodes[out net hdec q]'hq).pins p) := ⟨_, rfl⟩
    -- inverse of `out` on output indices
    let inv : Nat → (Fin n → Bool) := fun e =>
      if h : ∃ p', out net hdec p' = e then Classical.choose h else q
    have hinv : ∀ e, e ∈ I → out net hdec (inv e) = e := by
      intro e he
      have h := (memI e).mp he
      simp only [inv, dif_pos h]
      exact Classical.choose_spec h
    -- the outputs read
    obtain ⟨P, hP⟩ : ∃ P : Finset (Fin n → Bool),
        P = B.image fun p => inv (nodeOf ((net.nodes[out net hdec q]'hq).pins p)) := ⟨_, rfl⟩
    have hRcard : R.card ≤ A.card := by rw [hR]; exact card_image_le
    have hPcard : P.card ≤ B.card := by rw [hP]; exact card_image_le
    -- members of P were built before q
    have hPlt : ∀ x ∈ P, out net hdec x < out net hdec q := by
      intro x hx
      rw [hP, mem_image] at hx
      obtain ⟨p, hpB, rfl⟩ := hx
      rw [hB, mem_filter] at hpB
      obtain ⟨-, e, hs, heI⟩ := hpB
      rw [nodeOf_node hs, hinv e heI]
      exact net.acyclic _ hq p e hs
    -- every class member is a read output
    have hclsP : ∀ x ∈ cls (net.nodeFun Y) q Rᶜ, x ∈ P := by
      intro x hx
      rw [mem_cls] at hx
      obtain ⟨hxq, hxF, hxY⟩ := hx
      by_contra hxP
      apply hxq
      -- the node of q sees the same pin values at x and at q
      have hsame : net.nodeFun (out net hdec q) x = net.nodeFun (out net hdec q) q := by
        apply net.nodeFun_congr hq
        intro p
        rcases hs : ((net.nodes[out net hdec q]'hq).pins p).sig with i | e | c
        · have hiR : i ∈ R := by
            rw [hR, mem_image]
            refine ⟨p, ?_, inputOf_input h0 hs⟩
            rw [hA, mem_filter]
            exact ⟨mem_univ _, i, hs⟩
          have hiF : i ∉ Rᶜ := by simp [hiR]
          simp [Network.pinVal, Network.sigVal, hs, hxF i hiF]
        · by_cases heI : e ∈ I
          · -- another output: 0 at x and at q
            have hpB : p ∈ B := by
              rw [hB, mem_filter]; exact ⟨mem_univ _, e, hs, heI⟩
            have hmem : inv e ∈ P := by
              rw [hP, mem_image]
              exact ⟨p, hpB, by rw [nodeOf_node hs]⟩
            have hne_x : inv e ≠ x := fun h => hxP (h ▸ hmem)
            have hne_q : inv e ≠ q := by
              intro h
              have := hPlt _ hmem
              rw [h] at this
              exact lt_irrefl _ this
            obtain ⟨b', hb'⟩ := ospec (inv e)
            rw [hinv e heI] at hb'
            have e1 := congrFun hb' x
            have e2 := congrFun hb' q
            simp only [Network.signed, minterm_of_ne hne_x.symm, minterm_of_ne hne_q.symm] at e1 e2
            simp only [Network.pinVal, Network.sigVal, hs]
            rw [Bool.xor_right_inj.mp (e1.trans e2.symm)]
          · -- the node Y
            have heY : e = Y := huniq e (lt_trans (net.acyclic _ hq p e hs) hq) heI
            subst heY
            simp only [Network.pinVal, Network.sigVal, hs]
            rw [hxY]
        · simp [Network.pinVal, Network.sigVal, hs]
      obtain ⟨b, hb⟩ := ospec q
      have e1 := congrFun hb x
      have e2 := congrFun hb q
      simp only [Network.signed] at e1 e2
      rw [hsame] at e1
      rw [e2, minterm_self] at e1
      rw [minterm_of_ne hxq] at e1
      cases e1
    refine ⟨Rᶜ, P.card, ?_, card_le_card hclsP, fun x hx => hPlt x (hclsP x hx)⟩
    rw [card_compl, Fintype.card_fin]
    omega
  exact ⟨{ Y := net.nodeFun Y, V := V, card_V := hVcard, ignores := hign,
           out := out net hdec, out_injective := oinj, admissible := hadm }⟩

/-- Lemmas 1 and 2 alone: a decoder network over `n` inputs with `K`-pin nodes, `1 ≤ K < n`, has more than
`2 ^ n` nodes. With `2 ^ n` nodes every node is an output, so every pin of an output reads an input, another
output or a constant, and Lemma 2 says such a node is not a minterm. -/
theorem two_pow_lt_size (net : Network n K) (hK : 1 ≤ K) (hnK : K < n) (hdec : net.computesDecoder) :
    2 ^ n < net.nodes.size := by
  classical
  have hn : 2 ≤ n := by omega
  have oinj := out_injective net hdec hn
  have olt := out_lt net hdec
  have ospec := out_spec net hdec
  by_contra hlt
  have hle : net.nodes.size ≤ 2 ^ n := Nat.le_of_not_lt hlt
  -- every node index is an output
  have hall : ∀ e, e < net.nodes.size → ∃ q, out net hdec q = e := by
    intro e he
    by_contra hno
    have hsub : univ.image (out net hdec) ⊆ (range net.nodes.size).erase e := by
      intro j hj
      rw [mem_image] at hj
      obtain ⟨q, _, rfl⟩ := hj
      rw [mem_erase]
      exact ⟨fun h => hno ⟨q, h⟩, mem_range.mpr (olt q)⟩
    have h1 := card_le_card hsub
    rw [card_image_of_injective _ oinj, card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      card_erase_of_mem (mem_range.mpr he), card_range] at h1
    generalize 2 ^ n = M at *
    omega
  -- the output of any pattern reads inputs, other outputs and constants only
  obtain ⟨q⟩ : Nonempty (Fin n → Bool) := ⟨fun _ => false⟩
  have htr : ∀ p : Fin K, ∃ r : Read n q,
      ∀ x, net.pinVal x ((net.nodes[out net hdec q]'(olt q)).pins p) = r.eval x := by
    intro p
    rcases hs : ((net.nodes[out net hdec q]'(olt q)).pins p).sig with i | e | c
    · exact ⟨.input i ((net.nodes[out net hdec q]'(olt q)).pins p).neg,
        fun x => by simp [Network.pinVal, Network.sigVal, hs, Read.eval]⟩
    · have hlt : e < out net hdec q := net.acyclic _ (olt q) p e hs
      obtain ⟨p', hp'⟩ := hall e (lt_trans hlt (olt q))
      have hne : p' ≠ q := by
        rintro rfl
        omega
      obtain ⟨b', hb'⟩ := ospec p'
      refine ⟨.other p' hne (Bool.xor ((net.nodes[out net hdec q]'(olt q)).pins p).neg b'),
        fun x => ?_⟩
      have hx := congrFun hb' x
      simp only [Network.signed] at hx
      rw [hp'] at hx
      simp only [Network.pinVal, Network.sigVal, hs, Read.eval]
      rw [← hx, Bool.xor_assoc, ← Bool.xor_assoc b' b', Bool.xor_self, Bool.false_xor]
    · exact ⟨.const (Bool.xor ((net.nodes[out net hdec q]'(olt q)).pins p).neg c),
        fun x => by simp [Network.pinVal, Network.sigVal, hs, Read.eval]⟩
  obtain ⟨b, hb⟩ := ospec q
  apply lemma2 hnK q (fun p => Classical.choose (htr p)) (net.nodes[out net hdec q]'(olt q)).table b
  rw [← hb]
  funext x
  simp only [Network.signed]
  rw [net.nodeFun_eq (out net hdec q) (olt q) x]
  have hp : (fun p => (Classical.choose (htr p)).eval x) =
      fun p => net.pinVal x ((net.nodes[out net hdec q]'(olt q)).pins p) :=
    funext fun p => (Classical.choose_spec (htr p) x).symm
  rw [hp]

end DecoderOptimality
