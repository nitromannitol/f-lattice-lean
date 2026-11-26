import FLatticePaper.Plane.Induction.ChainWire
import FLatticePaper.Plane.Induction.StripColours

/-! # ALL_WHITE section C (internal canonical returns) as `ParentSquareOut` witnesses

A free white root `z` has a `ParentSquareOut` witness when its rejected input `q0` starts a three-edge retained route
`q0 → q1 → q2 → z` around a unit square, and `z` keeps its prescribed input `o`. Each case below is one such square, with the
corners given explicitly; the proof is the definition plus the parity of each corner.

The hypotheses are the companion inputs and nothing else:
* `LocalRetention` (black keeps both inputs, a white keeps at most one input, the packet's binary Laplacian): the quota and the
  selection of the canonical policy, and `Packet.binary`;
* `hpres`: the kept input of the free root is its prescribed direction (`CanonicalSignedPolicy.prescribed`, FreeClosure);
* `hR0`, `hR1`, `hR2`: the genuine arrows of the route (RegionalCompat), each stated as "black, or kept" at its white corner.
The parity and corner facts are proved here. -/

namespace FLatticePaper.InternalReturns

open FLatticePaper FLatticePaper.Induction FLatticePaper.W1NonfreeOut FLatticePaper.AndOrRank

/-- What a canonical policy supplies to a witness: black keeps both inputs, a white keeps at most one, and the Laplacian is binary. -/
structure LocalRetention (G : Field) (R : Site → Site → Prop) : Prop where
  black : ∀ c, laplacian G c = -1 → ∀ i, Edge i c → R c i
  white : ∀ c, laplacian G c = 0 → ∀ i j, R c i → R c j → i = j
  binary : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0

/-- The retention facts of a canonical signed policy (its quota and its white selection), with the binary Laplacian. -/
theorem LocalRetention.of_canonical {frame : ChildFrame} {G : Field} {η : ℤ} (C : CanonicalSignedPolicy frame G η)
    (hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0) : LocalRetention G C.policy where
  black := by
    intro c hc i hi
    rcases (show i = incomingNeg c ∨ i = incomingPos c from hi) with rfl | rfl
    · exact (C.quota.1 c hc).1
    · exact (C.quota.1 c hc).2
  white := fun c hc i j hi hj => by
    rw [C.white_policy c hc i] at hi
    rw [C.white_policy c hc j] at hj
    rw [hi, hj]
  binary := hbin

theorem incomingNeg_of_even {x : Site} (h : EvenSite x) : incomingNeg x = (x.1 - 1, x.2) := by
  unfold incomingNeg; rw [if_pos h]

theorem incomingPos_of_even {x : Site} (h : EvenSite x) : incomingPos x = (x.1 + 1, x.2) := by
  unfold incomingPos; rw [if_pos h]

theorem incomingNeg_of_odd {x : Site} (h : ¬ EvenSite x) : incomingNeg x = (x.1, x.2 - 1) := by
  unfold incomingNeg; rw [if_neg h]

theorem incomingPos_of_odd {x : Site} (h : ¬ EvenSite x) : incomingPos x = (x.1, x.2 + 1) := by
  unfold incomingPos; rw [if_neg h]


/-- An input of an odd site, by coordinates: a vertical neighbour `(a, b)` of `(y1, y2)`. -/
theorem edge_odd {y1 y2 a b : ℤ} (hy : ¬ EvenSite (y1, y2)) (h1 : a = y1) (h2 : b = y2 - 1 ∨ b = y2 + 1) :
    Edge (a, b) (y1, y2) := by
  show (a, b) = incomingNeg (y1, y2) ∨ (a, b) = incomingPos (y1, y2)
  rcases h2 with h2 | h2
  · left; rw [incomingNeg_of_odd hy]; exact Prod.ext h1 h2
  · right; rw [incomingPos_of_odd hy]; exact Prod.ext h1 h2

/-- An input of an even site, by coordinates: a horizontal neighbour `(a, b)` of `(y1, y2)`. -/
theorem edge_even {y1 y2 a b : ℤ} (hy : EvenSite (y1, y2)) (h1 : b = y2) (h2 : a = y1 - 1 ∨ a = y1 + 1) :
    Edge (a, b) (y1, y2) := by
  show (a, b) = incomingNeg (y1, y2) ∨ (a, b) = incomingPos (y1, y2)
  rcases h2 with h2 | h2
  · left; rw [incomingNeg_of_even hy]; exact Prod.ext h2 h1
  · right; rw [incomingPos_of_even hy]; exact Prod.ext h2 h1

/-- **A unit square witness.** Given the square's corners `z, q0, q1, q2` and the retained route `q0 → q1 → q2 → z` (each
edge genuine: black, or kept), with `z` keeping its other input `o`, the parent-square predicate holds at `z`. -/
theorem parentSquareOut_of_square {G : Field} {R : Site → Site → Prop} (hL : LocalRetention G R)
    {z q0 q1 q2 o : Site} {a b : ℤ}
    (hcorn : squareCorners a b = {z, q0, q1, q2})
    (hd : q0 ≠ q1 ∧ q1 ≠ q2 ∧ q0 ≠ q2)
    (hq0 : q0 = incomingNeg z ∨ q0 = incomingPos z) (hq0R : ¬ R z q0)
    (hq1 : Edge q1 q0) (hq2 : Edge q2 q1) (hz2 : Edge z q2)
    (hR0 : laplacian G q0 = -1 ∨ R q0 q1)
    (hR1 : laplacian G q1 = -1 ∨ R q1 q2)
    (hR2 : laplacian G q2 = -1 ∨ R q2 z)
    (ho : o = incomingNeg z ∨ o = incomingPos z) (hoC : o ∉ squareCorners a b)
    (hzo : R z o) (hzu : ∀ j, R z j → j = o) :
    ParentSquareOut G R z := by
  have hR0' : R q0 q1 := hR0.elim (fun h => hL.black q0 h q1 hq1) id
  have hR1' : R q1 q2 := hR1.elim (fun h => hL.black q1 h q2 hq2) id
  have hR2' : R q2 z := hR2.elim (fun h => hL.black q2 h z hz2) id
  have hmem : ∀ c, c ∈ squareCorners a b ↔ c = z ∨ c = q0 ∨ c = q1 ∨ c = q2 := by
    intro c; rw [hcorn]; simp
  refine ⟨q0, q1, q2, o, a, b, (hmem z).2 (Or.inl rfl), (hmem q0).2 (Or.inr (Or.inl rfl)),
    (hmem q1).2 (Or.inr (Or.inr (Or.inl rfl))), (hmem q2).2 (Or.inr (Or.inr (Or.inr rfl))), ?_,
    hd.1, hd.2.1, hd.2.2, hq0, hq0R, hq1, hq2, hz2, hR0', hR1', hR2', ho, hoC, hzo, hzu, ?_, ?_, ?_⟩
  · intro c' hc hne
    rcases (hmem c').1 hc with h | h | h | h
    · exact absurd h hne
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rcases hL.binary q0 with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, fun j hj => hL.white q0 h j q1 hj hR0'⟩
  · rcases hL.binary q1 with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, fun j hj => hL.white q1 h j q2 hj hR1'⟩
  · rcases hL.binary q2 with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, fun j hj => hL.white q2 h j z hj hR2'⟩

/-! ### Section C, horizontal arcs (`a = (1,0)`, `b = (0,1)`, `δ = 1`): type A is even, type B is odd.
The prescribed kept input of an internal free root is `z + a` (even) or `z + b` (odd). The three internal cases are the three
values of the preceding neighbour `c`: C.1 (`z` of type B, `c = z - a`), C.2 (`z` of type A, `c = z - a - b`), C.3 (`z` of type A,
`c = z - a`, type B). -/

/-- C.1: `z` of type B; the rejected input is `z - b`; the route is `z - b → z - a - b → c = z - a → z`. -/
theorem case1_H {G : Field} {R : Site → Site → Prop} (hL : LocalRetention G R) {z c : Site}
    (hzodd : ¬ EvenSite z) (hc : c = (z.1 - 1, z.2))
    (hpres : ∀ j, R z j ↔ j = (z.1, z.2 + 1))
    (hR0 : laplacian G (z.1, z.2 - 1) = -1 ∨ R (z.1, z.2 - 1) (z.1 - 1, z.2 - 1))
    (hR1 : laplacian G (z.1 - 1, z.2 - 1) = -1 ∨ R (z.1 - 1, z.2 - 1) c)
    (hR2 : laplacian G c = -1 ∨ R c z) :
    ParentSquareOut G R z := by
  subst hc
  have hq0e : EvenSite (z.1, z.2 - 1) := by unfold EvenSite at hzodd ⊢; simp only at hzodd ⊢; omega
  have hq1o : ¬ EvenSite (z.1 - 1, z.2 - 1) := by unfold EvenSite at hzodd ⊢; simp only at hzodd ⊢; omega
  have hq2e : EvenSite (z.1 - 1, z.2) := by unfold EvenSite at hzodd ⊢; simp only at hzodd ⊢; omega
  have hcorn : squareCorners (z.1 - 1) (z.2 - 1) = {z, (z.1, z.2 - 1), (z.1 - 1, z.2 - 1), (z.1 - 1, z.2)} := by
    ext c; simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]; constructor <;> intro h <;> omega
  have hd : (z.1, z.2 - 1) ≠ (z.1 - 1, z.2 - 1) ∧ (z.1 - 1, z.2 - 1) ≠ (z.1 - 1, z.2) ∧ (z.1, z.2 - 1) ≠ (z.1 - 1, z.2) := by
    refine ⟨?_, ?_, ?_⟩ <;> intro h <;> simp only [Prod.mk.injEq] at h <;> omega
  have hq0 : (z.1, z.2 - 1) = incomingNeg z ∨ (z.1, z.2 - 1) = incomingPos z := Or.inl (incomingNeg_of_odd hzodd).symm
  have hzo : R z (z.1, z.2 + 1) := (hpres _).2 rfl
  have hzu : ∀ j, R z j → j = (z.1, z.2 + 1) := fun j hj => (hpres j).1 hj
  have hq0R : ¬ R z (z.1, z.2 - 1) := by
    intro h; have := hzu _ h; simp only [Prod.mk.injEq] at this; omega
  have hq1 : Edge (z.1 - 1, z.2 - 1) (z.1, z.2 - 1) := Or.inl (by rw [incomingNeg_of_even hq0e])
  have hq2 : Edge (z.1 - 1, z.2) (z.1 - 1, z.2 - 1) :=
    Or.inr (by rw [incomingPos_of_odd hq1o]; exact Prod.ext rfl (by show z.2 = z.2 - 1 + 1; ring))
  have hz2 : Edge z (z.1 - 1, z.2) :=
    Or.inr (by rw [incomingPos_of_even hq2e]; exact Prod.ext (by show z.1 = z.1 - 1 + 1; ring) rfl)
  have ho : (z.1, z.2 + 1) = incomingNeg z ∨ (z.1, z.2 + 1) = incomingPos z := Or.inr (incomingPos_of_odd hzodd).symm
  have hoC : (z.1, z.2 + 1) ∉ squareCorners (z.1 - 1) (z.2 - 1) := by
    intro h; rw [hcorn] at h; simp only [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff] at h; omega
  exact parentSquareOut_of_square hL hcorn hd hq0 hq0R hq1 hq2 hz2 hR0 hR1 hR2 ho hoC hzo hzu

/-- C.2: `z` of type A, `c = z - a - b` of type A (diagonal); the route is `z - a → c → z - b → z`. -/
theorem case2_H {G : Field} {R : Site → Site → Prop} (hL : LocalRetention G R) {z c : Site}
    (hzeven : EvenSite z) (hc : c = (z.1 - 1, z.2 - 1))
    (hpres : ∀ j, R z j ↔ j = (z.1 + 1, z.2))
    (hR0 : laplacian G (z.1 - 1, z.2) = -1 ∨ R (z.1 - 1, z.2) c)
    (hR1 : laplacian G c = -1 ∨ R c (z.1, z.2 - 1))
    (hR2 : laplacian G (z.1, z.2 - 1) = -1 ∨ R (z.1, z.2 - 1) z) :
    ParentSquareOut G R z := by
  subst hc
  have hq0o : ¬ EvenSite (z.1 - 1, z.2) := by unfold EvenSite at hzeven ⊢; simp only at hzeven ⊢; omega
  have hq1e : EvenSite (z.1 - 1, z.2 - 1) := by unfold EvenSite at hzeven ⊢; simp only at hzeven ⊢; omega
  have hq2o : ¬ EvenSite (z.1, z.2 - 1) := by unfold EvenSite at hzeven ⊢; simp only at hzeven ⊢; omega
  have hcorn : squareCorners (z.1 - 1) (z.2 - 1) = {z, (z.1 - 1, z.2), (z.1 - 1, z.2 - 1), (z.1, z.2 - 1)} := by
    ext c; simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]; constructor <;> intro h <;> omega
  have hd : (z.1 - 1, z.2) ≠ (z.1 - 1, z.2 - 1) ∧ (z.1 - 1, z.2 - 1) ≠ (z.1, z.2 - 1) ∧ (z.1 - 1, z.2) ≠ (z.1, z.2 - 1) := by
    refine ⟨?_, ?_, ?_⟩ <;> intro h <;> simp only [Prod.mk.injEq] at h <;> omega
  have hq0 : (z.1 - 1, z.2) = incomingNeg z ∨ (z.1 - 1, z.2) = incomingPos z := Or.inl (incomingNeg_of_even hzeven).symm
  have hzo : R z (z.1 + 1, z.2) := (hpres _).2 rfl
  have hzu : ∀ j, R z j → j = (z.1 + 1, z.2) := fun j hj => (hpres j).1 hj
  have hq0R : ¬ R z (z.1 - 1, z.2) := by
    intro h; have := hzu _ h; simp only [Prod.mk.injEq] at this; omega
  have hq1 : Edge (z.1 - 1, z.2 - 1) (z.1 - 1, z.2) := Or.inl (by rw [incomingNeg_of_odd hq0o])
  have hq2 : Edge (z.1, z.2 - 1) (z.1 - 1, z.2 - 1) :=
    Or.inr (by rw [incomingPos_of_even hq1e]; exact Prod.ext (by show z.1 = z.1 - 1 + 1; ring) rfl)
  have hz2 : Edge z (z.1, z.2 - 1) := Or.inr (by rw [incomingPos_of_odd hq2o]; exact Prod.ext rfl (by show z.2 = z.2 - 1 + 1; ring))
  have ho : (z.1 + 1, z.2) = incomingNeg z ∨ (z.1 + 1, z.2) = incomingPos z := Or.inr (incomingPos_of_even hzeven).symm
  have hoC : (z.1 + 1, z.2) ∉ squareCorners (z.1 - 1) (z.2 - 1) := by
    intro h; rw [hcorn] at h; simp only [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff] at h; omega
  exact parentSquareOut_of_square hL hcorn hd hq0 hq0R hq1 hq2 hz2 hR0 hR1 hR2 ho hoC hzo hzu

/-- C.3: `z` of type A, `c = z - a` of type B; the rejected input is `c`; the route is `c → c + b → z + b → z`. -/
theorem case3_H {G : Field} {R : Site → Site → Prop} (hL : LocalRetention G R) {z c : Site}
    (hzeven : EvenSite z) (hc : c = (z.1 - 1, z.2))
    (hpres : ∀ j, R z j ↔ j = (z.1 + 1, z.2))
    (hR0 : laplacian G c = -1 ∨ R c (z.1 - 1, z.2 + 1))
    (hR1 : laplacian G (z.1 - 1, z.2 + 1) = -1 ∨ R (z.1 - 1, z.2 + 1) (z.1, z.2 + 1))
    (hR2 : laplacian G (z.1, z.2 + 1) = -1 ∨ R (z.1, z.2 + 1) z) :
    ParentSquareOut G R z := by
  subst hc
  have hq0o : ¬ EvenSite (z.1 - 1, z.2) := by unfold EvenSite at hzeven ⊢; simp only at hzeven ⊢; omega
  have hq1e : EvenSite (z.1 - 1, z.2 + 1) := by unfold EvenSite at hzeven ⊢; simp only at hzeven ⊢; omega
  have hq2o : ¬ EvenSite (z.1, z.2 + 1) := by unfold EvenSite at hzeven ⊢; simp only at hzeven ⊢; omega
  have hcorn : squareCorners (z.1 - 1) z.2 = {z, (z.1 - 1, z.2), (z.1 - 1, z.2 + 1), (z.1, z.2 + 1)} := by
    ext c; simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]; constructor <;> intro h <;> omega
  have hd : (z.1 - 1, z.2) ≠ (z.1 - 1, z.2 + 1) ∧ (z.1 - 1, z.2 + 1) ≠ (z.1, z.2 + 1) ∧ (z.1 - 1, z.2) ≠ (z.1, z.2 + 1) := by
    refine ⟨?_, ?_, ?_⟩ <;> intro h <;> simp only [Prod.mk.injEq] at h <;> omega
  have hq0 : (z.1 - 1, z.2) = incomingNeg z ∨ (z.1 - 1, z.2) = incomingPos z := Or.inl (incomingNeg_of_even hzeven).symm
  have hzo : R z (z.1 + 1, z.2) := (hpres _).2 rfl
  have hzu : ∀ j, R z j → j = (z.1 + 1, z.2) := fun j hj => (hpres j).1 hj
  have hq0R : ¬ R z (z.1 - 1, z.2) := by
    intro h; have := hzu _ h; simp only [Prod.mk.injEq] at this; omega
  have hq1 : Edge (z.1 - 1, z.2 + 1) (z.1 - 1, z.2) :=
    Or.inr (by rw [incomingPos_of_odd hq0o])
  have hq2 : Edge (z.1, z.2 + 1) (z.1 - 1, z.2 + 1) :=
    Or.inr (by rw [incomingPos_of_even hq1e]; exact Prod.ext (by show z.1 = z.1 - 1 + 1; ring) rfl)
  have hz2 : Edge z (z.1, z.2 + 1) := Or.inl (by rw [incomingNeg_of_odd hq2o]; exact Prod.ext rfl (by show z.2 = z.2 + 1 - 1; ring))
  have ho : (z.1 + 1, z.2) = incomingNeg z ∨ (z.1 + 1, z.2) = incomingPos z := Or.inr (incomingPos_of_even hzeven).symm
  have hoC : (z.1 + 1, z.2) ∉ squareCorners (z.1 - 1) z.2 := by
    intro h; rw [hcorn] at h; simp only [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff] at h; omega
  exact parentSquareOut_of_square hL hcorn hd hq0 hq0R hq1 hq2 hz2 hR0 hR1 hR2 ho hoC hzo hzu


/-! ### Section C, vertical arcs (`a = (0,δ)`, `b = (-δ,0)`, `δ = -η`): type A is odd, type B is even.
The prescribed kept input of an internal free root is `z + a` (odd) or `z + b` (even). The three cases are as for horizontal
arcs with `a`, `b` replaced by these vectors. -/

/-- C.1 (vertical): `z` of type B (even); the rejected input is `z - b`; the route is `z - b → z - a - b → c = z - a → z`. -/
theorem case1_V {G : Field} {R : Site → Site → Prop} (hL : LocalRetention G R) {z c : Site} {δ : ℤ}
    (hδ : δ = 1 ∨ δ = -1) (heven : EvenSite z) (hc : c = (z.1, z.2 - δ))
    (hpres : ∀ j, R z j ↔ j = (z.1 - δ, z.2))
    (hR0 : laplacian G (z.1 + δ, z.2) = -1 ∨ R (z.1 + δ, z.2) (z.1 + δ, z.2 - δ))
    (hR1 : laplacian G (z.1 + δ, z.2 - δ) = -1 ∨ R (z.1 + δ, z.2 - δ) c)
    (hR2 : laplacian G c = -1 ∨ R c z) :
    ParentSquareOut G R z := by
  subst hc
  have hq0o : ¬ EvenSite (z.1 + δ, z.2) := by unfold EvenSite at heven ⊢; simp only at heven ⊢; omega
  have hq1e : EvenSite (z.1 + δ, z.2 - δ) := by unfold EvenSite at heven ⊢; simp only at heven ⊢; omega
  have hq2o : ¬ EvenSite (z.1, z.2 - δ) := by unfold EvenSite at heven ⊢; simp only at heven ⊢; omega
  have hcorn : squareCorners (min z.1 (z.1 + δ)) (min z.2 (z.2 - δ)) =
      {z, (z.1 + δ, z.2), (z.1 + δ, z.2 - δ), (z.1, z.2 - δ)} := by
    ext c; simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
    constructor <;> intro h <;> omega
  have hd : (z.1 + δ, z.2) ≠ (z.1 + δ, z.2 - δ) ∧ (z.1 + δ, z.2 - δ) ≠ (z.1, z.2 - δ) ∧
      (z.1 + δ, z.2) ≠ (z.1, z.2 - δ) := by
    refine ⟨?_, ?_, ?_⟩ <;> intro h <;> simp only [Prod.mk.injEq] at h <;> omega
  have hq0 : (z.1 + δ, z.2) = incomingNeg z ∨ (z.1 + δ, z.2) = incomingPos z :=
    edge_even heven (by rfl) (by omega)
  have hzo : R z (z.1 - δ, z.2) := (hpres _).2 rfl
  have hzu : ∀ j, R z j → j = (z.1 - δ, z.2) := fun j hj => (hpres j).1 hj
  have hq0R : ¬ R z (z.1 + δ, z.2) := by
    intro h; have := hzu _ h; simp only [Prod.mk.injEq] at this; omega
  have hq1 : Edge (z.1 + δ, z.2 - δ) (z.1 + δ, z.2) := edge_odd hq0o rfl (by omega)
  have hq2 : Edge (z.1, z.2 - δ) (z.1 + δ, z.2 - δ) := edge_even hq1e rfl (by omega)
  have hz2 : Edge z (z.1, z.2 - δ) := edge_odd hq2o rfl (by omega)
  have ho : (z.1 - δ, z.2) = incomingNeg z ∨ (z.1 - δ, z.2) = incomingPos z :=
    edge_even heven (by rfl) (by omega)
  have hoC : (z.1 - δ, z.2) ∉ squareCorners (min z.1 (z.1 + δ)) (min z.2 (z.2 - δ)) := by
    intro h; rw [hcorn] at h; simp only [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff] at h; omega
  exact parentSquareOut_of_square hL hcorn hd hq0 hq0R hq1 hq2 hz2 hR0 hR1 hR2 ho hoC hzo hzu

/-- C.2 (vertical): `z` of type A (odd), `c = z - a - b` of type A (diagonal); the route is `z - a → c → z - b → z`. -/
theorem case2_V {G : Field} {R : Site → Site → Prop} (hL : LocalRetention G R) {z c : Site} {δ : ℤ}
    (hδ : δ = 1 ∨ δ = -1) (hzodd : ¬ EvenSite z) (hc : c = (z.1 + δ, z.2 - δ))
    (hpres : ∀ j, R z j ↔ j = (z.1, z.2 + δ))
    (hR0 : laplacian G (z.1, z.2 - δ) = -1 ∨ R (z.1, z.2 - δ) c)
    (hR1 : laplacian G c = -1 ∨ R c (z.1 + δ, z.2))
    (hR2 : laplacian G (z.1 + δ, z.2) = -1 ∨ R (z.1 + δ, z.2) z) :
    ParentSquareOut G R z := by
  subst hc
  have hq0e : EvenSite (z.1, z.2 - δ) := by unfold EvenSite at hzodd ⊢; simp only at hzodd ⊢; omega
  have hq1o : ¬ EvenSite (z.1 + δ, z.2 - δ) := by unfold EvenSite at hzodd ⊢; simp only at hzodd ⊢; omega
  have hq2e : EvenSite (z.1 + δ, z.2) := by unfold EvenSite at hzodd ⊢; simp only at hzodd ⊢; omega
  have hcorn : squareCorners (min z.1 (z.1 + δ)) (min (z.2 - δ) z.2) =
      {z, (z.1, z.2 - δ), (z.1 + δ, z.2 - δ), (z.1 + δ, z.2)} := by
    ext c; simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
    constructor <;> intro h <;> omega
  have hd : (z.1, z.2 - δ) ≠ (z.1 + δ, z.2 - δ) ∧ (z.1 + δ, z.2 - δ) ≠ (z.1 + δ, z.2) ∧
      (z.1, z.2 - δ) ≠ (z.1 + δ, z.2) := by
    refine ⟨?_, ?_, ?_⟩ <;> intro h <;> simp only [Prod.mk.injEq] at h <;> omega
  have hq0 : (z.1, z.2 - δ) = incomingNeg z ∨ (z.1, z.2 - δ) = incomingPos z :=
    edge_odd hzodd rfl (by omega)
  have hzo : R z (z.1, z.2 + δ) := (hpres _).2 rfl
  have hzu : ∀ j, R z j → j = (z.1, z.2 + δ) := fun j hj => (hpres j).1 hj
  have hq0R : ¬ R z (z.1, z.2 - δ) := by
    intro h; have := hzu _ h; simp only [Prod.mk.injEq] at this; omega
  have hq1 : Edge (z.1 + δ, z.2 - δ) (z.1, z.2 - δ) := edge_even hq0e rfl (by omega)
  have hq2 : Edge (z.1 + δ, z.2) (z.1 + δ, z.2 - δ) := edge_odd hq1o rfl (by omega)
  have hz2 : Edge z (z.1 + δ, z.2) := edge_even hq2e rfl (by omega)
  have ho : (z.1, z.2 + δ) = incomingNeg z ∨ (z.1, z.2 + δ) = incomingPos z :=
    edge_odd hzodd rfl (by omega)
  have hoC : (z.1, z.2 + δ) ∉ squareCorners (min z.1 (z.1 + δ)) (min (z.2 - δ) z.2) := by
    intro h; rw [hcorn] at h; simp only [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff] at h; omega
  exact parentSquareOut_of_square hL hcorn hd hq0 hq0R hq1 hq2 hz2 hR0 hR1 hR2 ho hoC hzo hzu

/-- C.3 (vertical): `z` of type A (odd), `c = z - a` of type B (even); the rejected input is `c`; the route is
`c → c - b → z + b → z`, with `c - b = z - a - b` (the common corner) and `z + b`. -/
theorem case3_V {G : Field} {R : Site → Site → Prop} (hL : LocalRetention G R) {z c : Site} {δ : ℤ}
    (hδ : δ = 1 ∨ δ = -1) (hzodd : ¬ EvenSite z) (hc : c = (z.1, z.2 - δ))
    (hpres : ∀ j, R z j ↔ j = (z.1, z.2 + δ))
    (hR0 : laplacian G c = -1 ∨ R c (z.1 - δ, z.2 - δ))
    (hR1 : laplacian G (z.1 - δ, z.2 - δ) = -1 ∨ R (z.1 - δ, z.2 - δ) (z.1 - δ, z.2))
    (hR2 : laplacian G (z.1 - δ, z.2) = -1 ∨ R (z.1 - δ, z.2) z) :
    ParentSquareOut G R z := by
  subst hc
  have hq0e : EvenSite (z.1, z.2 - δ) := by unfold EvenSite at hzodd ⊢; simp only at hzodd ⊢; omega
  have hq1o : ¬ EvenSite (z.1 - δ, z.2 - δ) := by unfold EvenSite at hzodd ⊢; simp only at hzodd ⊢; omega
  have hq2e : EvenSite (z.1 - δ, z.2) := by unfold EvenSite at hzodd ⊢; simp only at hzodd ⊢; omega
  have hcorn : squareCorners (min z.1 (z.1 - δ)) (min z.2 (z.2 - δ)) =
      {z, (z.1, z.2 - δ), (z.1 - δ, z.2 - δ), (z.1 - δ, z.2)} := by
    ext c; simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
    constructor <;> intro h <;> omega
  have hd : (z.1, z.2 - δ) ≠ (z.1 - δ, z.2 - δ) ∧ (z.1 - δ, z.2 - δ) ≠ (z.1 - δ, z.2) ∧
      (z.1, z.2 - δ) ≠ (z.1 - δ, z.2) := by
    refine ⟨?_, ?_, ?_⟩ <;> intro h <;> simp only [Prod.mk.injEq] at h <;> omega
  have hq0 : (z.1, z.2 - δ) = incomingNeg z ∨ (z.1, z.2 - δ) = incomingPos z :=
    edge_odd hzodd rfl (by omega)
  have hzo : R z (z.1, z.2 + δ) := (hpres _).2 rfl
  have hzu : ∀ j, R z j → j = (z.1, z.2 + δ) := fun j hj => (hpres j).1 hj
  have hq0R : ¬ R z (z.1, z.2 - δ) := by
    intro h; have := hzu _ h; simp only [Prod.mk.injEq] at this; omega
  have hq1 : Edge (z.1 - δ, z.2 - δ) (z.1, z.2 - δ) := edge_even hq0e rfl (by omega)
  have hq2 : Edge (z.1 - δ, z.2) (z.1 - δ, z.2 - δ) := edge_odd hq1o rfl (by omega)
  have hz2 : Edge z (z.1 - δ, z.2) := edge_even hq2e rfl (by omega)
  have ho : (z.1, z.2 + δ) = incomingNeg z ∨ (z.1, z.2 + δ) = incomingPos z :=
    edge_odd hzodd rfl (by omega)
  have hoC : (z.1, z.2 + δ) ∉ squareCorners (min z.1 (z.1 - δ)) (min z.2 (z.2 - δ)) := by
    intro h; rw [hcorn] at h; simp only [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff] at h; omega
  exact parentSquareOut_of_square hL hcorn hd hq0 hq0R hq1 hq2 hz2 hR0 hR1 hR2 ho hoC hzo hzu


/-! ### Section D, the endpoint rows, as witnesses. The root and route sites are the displayed representatives of the text.
The hypotheses are the genuine route arrows (`hR…`), the kept input of the root (`hpres`, the prescription), and, where a route
site is a strip seed, its Laplacian (from `hS`, the packet's strips, via `StripColours`). -/

section EndpointRows

variable {G : Field} {R : Site → Site → Prop}

/-- `η = +1`, root `H_0 = (1,0)`: `(1,1) → (0,1) → (0,0) → (1,0)`; the root keeps `(1,-1)`. -/
theorem row_eta_pos_H0 (hL : LocalRetention G R) (frame : ChildFrame) (hS : frame.HasStrips G)
    (hpres : ∀ j, R (1, 0) j ↔ j = (1, -1))
    (hR1 : laplacian G (0, 1) = -1 ∨ R (0, 1) (0, 0))
    (hR2 : laplacian G (0, 0) = -1 ∨ R (0, 0) (1, 0)) :
    ParentSquareOut G R (1, 0) := by
  have hzo : R (1, 0) (1, -1) := (hpres _).2 rfl
  have hzu : ∀ j, R (1, 0) j → j = (1, -1) := fun j hj => (hpres j).1 hj
  have hcorn : squareCorners 0 0 = {(1, 0), (1, 1), (0, 1), (0, 0)} := by decide
  exact parentSquareOut_of_square hL hcorn (by decide) (by decide) (fun h => by
      have := hzu _ h; exact absurd this (by decide)) (by unfold Edge; decide) (by unfold Edge; decide)
    (by unfold Edge; decide) (Or.inl (StripColours.lap_one_one frame hS)) hR1 hR2 (by decide) (by rw [hcorn]; decide)
    hzo hzu

/-- `η = -1`, root `H_0`: `(1,-1) → (0,-1) → (0,0) → (1,0)`; the root keeps `(1,1)`. -/
theorem row_eta_neg_H0 (hL : LocalRetention G R)
    (hpres : ∀ j, R (1, 0) j ↔ j = (1, 1))
    (hR0 : laplacian G (1, -1) = -1 ∨ R (1, -1) (0, -1))
    (hR1 : laplacian G (0, -1) = -1 ∨ R (0, -1) (0, 0))
    (hR2 : laplacian G (0, 0) = -1 ∨ R (0, 0) (1, 0)) :
    ParentSquareOut G R (1, 0) := by
  have hzo : R (1, 0) (1, 1) := (hpres _).2 rfl
  have hzu : ∀ j, R (1, 0) j → j = (1, 1) := fun j hj => (hpres j).1 hj
  have hcorn : squareCorners 0 (-1) = {(1, 0), (1, -1), (0, -1), (0, 0)} := by decide
  exact parentSquareOut_of_square hL hcorn (by decide) (by decide) (fun h => by
      have := hzu _ h; exact absurd this (by decide)) (by unfold Edge; decide) (by unfold Edge; decide)
    (by unfold Edge; decide) hR0 hR1 hR2 (by decide) (by rw [hcorn]; decide) hzo hzu

/-- `±`, root `H_last` (displayed `(0,-1)`): `(0,-2) → (-1,-2) → (-1,-1) → (0,-1)`; the root keeps `(0,0)`. The first corner is a
strip seed. -/
theorem row_Hlast (hL : LocalRetention G R) (frame : ChildFrame) (hS : frame.HasStrips G)
    (hpres : ∀ j, R (0, -1) j ↔ j = (0, 0))
    (hR1 : laplacian G (-1, -2) = -1 ∨ R (-1, -2) (-1, -1))
    (hR2 : laplacian G (-1, -1) = -1 ∨ R (-1, -1) (0, -1)) :
    ParentSquareOut G R (0, -1) := by
  have hzo : R (0, -1) (0, 0) := (hpres _).2 rfl
  have hzu : ∀ j, R (0, -1) j → j = (0, 0) := fun j hj => (hpres j).1 hj
  have hcorn : squareCorners (-1) (-2) = {(0, -1), (0, -2), (-1, -2), (-1, -1)} := by decide
  exact parentSquareOut_of_square hL hcorn (by decide) (by decide) (fun h => by
      have := hzu _ h; exact absurd this (by decide)) (by unfold Edge; decide) (by unfold Edge; decide)
    (by unfold Edge; decide) (Or.inl (StripColours.lap_zero_neg_two frame hS)) hR1 hR2 (by decide)
    (by rw [hcorn]; decide) hzo hzu

/-- `±`, root `V_0 = (0,0)`: `(-1,0) → (-1,-1) → (0,-1) → (0,0)`; the root keeps `(1,0)`. The first corner is a strip seed. -/
theorem row_V0 (hL : LocalRetention G R) (frame : ChildFrame) (hS : frame.HasStrips G)
    (hpres : ∀ j, R (0, 0) j ↔ j = (1, 0))
    (hR1 : laplacian G (-1, -1) = -1 ∨ R (-1, -1) (0, -1))
    (hR2 : laplacian G (0, -1) = -1 ∨ R (0, -1) (0, 0)) :
    ParentSquareOut G R (0, 0) := by
  have hzo : R (0, 0) (1, 0) := (hpres _).2 rfl
  have hzu : ∀ j, R (0, 0) j → j = (1, 0) := fun j hj => (hpres j).1 hj
  have hcorn : squareCorners (-1) (-1) = {(0, 0), (-1, 0), (-1, -1), (0, -1)} := by decide
  exact parentSquareOut_of_square hL hcorn (by decide) (by decide) (fun h => by
      have := hzu _ h; exact absurd this (by decide)) (by unfold Edge; decide) (by unfold Edge; decide)
    (by unfold Edge; decide) (Or.inl (StripColours.lap_neg_one_zero frame hS)) hR1 hR2 (by decide)
    (by rw [hcorn]; decide) hzo hzu

/-- `η = +1`, root `V_end` (displayed `(1,-1)`): `(0,-1) → (0,0) → (1,0) → (1,-1)`; the root keeps `(2,-1)`. -/
theorem row_eta_pos_Vend (hL : LocalRetention G R)
    (hpres : ∀ j, R (1, -1) j ↔ j = (2, -1))
    (hR0 : laplacian G (0, -1) = -1 ∨ R (0, -1) (0, 0))
    (hR1 : laplacian G (0, 0) = -1 ∨ R (0, 0) (1, 0))
    (hR2 : laplacian G (1, 0) = -1 ∨ R (1, 0) (1, -1)) :
    ParentSquareOut G R (1, -1) := by
  have hzo : R (1, -1) (2, -1) := (hpres _).2 rfl
  have hzu : ∀ j, R (1, -1) j → j = (2, -1) := fun j hj => (hpres j).1 hj
  have hcorn : squareCorners 0 (-1) = {(1, -1), (0, -1), (0, 0), (1, 0)} := by decide
  exact parentSquareOut_of_square hL hcorn (by decide) (by decide) (fun h => by
      have := hzu _ h; exact absurd this (by decide)) (by unfold Edge; decide) (by unfold Edge; decide)
    (by unfold Edge; decide) hR0 hR1 hR2 (by decide) (by rw [hcorn]; decide) hzo hzu

/-- `η = -1`, root `V_end`: `(2,-1) → (2,-2) → (1,-2) → (1,-1)`; the root keeps `(0,-1)`. The first corner is a strip seed. -/
theorem row_eta_neg_Vend (hL : LocalRetention G R) (frame : ChildFrame) (hS : frame.HasStrips G)
    (hpres : ∀ j, R (1, -1) j ↔ j = (0, -1))
    (hR1 : laplacian G (2, -2) = -1 ∨ R (2, -2) (1, -2))
    (hR2 : laplacian G (1, -2) = -1 ∨ R (1, -2) (1, -1)) :
    ParentSquareOut G R (1, -1) := by
  have hzo : R (1, -1) (0, -1) := (hpres _).2 rfl
  have hzu : ∀ j, R (1, -1) j → j = (0, -1) := fun j hj => (hpres j).1 hj
  have hcorn : squareCorners 1 (-2) = {(1, -1), (2, -1), (2, -2), (1, -2)} := by decide
  exact parentSquareOut_of_square hL hcorn (by decide) (by decide) (fun h => by
      have := hzu _ h; exact absurd this (by decide)) (by unfold Edge; decide) (by unfold Edge; decide)
    (by unfold Edge; decide) (Or.inl (StripColours.lap_two_neg_one frame hS)) hR1 hR2 (by decide)
    (by rw [hcorn]; decide) hzo hzu

end EndpointRows


/-! ### The remaining endpoint rows, as instances of the case lemmas -/

/-- `η = +1`, root `H_1 = (2,0)`: `(1,0) → (1,-1) → (2,-1) → (2,0)`, the case C.2 with `c = (1,-1)`. -/
theorem row_eta_pos_H1 (hL : LocalRetention G R) (frame : ChildFrame) (hS : frame.HasStrips G)
    (hpres : ∀ j, R (2, 0) j ↔ j = (3, 0))
    (hR0 : laplacian G (1, 0) = -1 ∨ R (1, 0) (1, -1))
    (hR1 : laplacian G (1, -1) = -1 ∨ R (1, -1) (2, -1)) :
    ParentSquareOut G R (2, 0) :=
  case2_H hL (c := (1, -1)) (by decide) rfl hpres hR0 hR1 (Or.inl (StripColours.lap_two_neg_one frame hS))

/-- `η = -1`, root `H_1 = (2,0)`: `(1,0) → (1,1) → (2,1) → (2,0)`, the case C.3 with `c = (1,0)`. -/
theorem row_eta_neg_H1 (hL : LocalRetention G R) (frame : ChildFrame) (hS : frame.HasStrips G)
    (hpres : ∀ j, R (2, 0) j ↔ j = (3, 0))
    (hR0 : laplacian G (1, 0) = -1 ∨ R (1, 0) (1, 1))
    (hR2 : laplacian G (2, 1) = -1 ∨ R (2, 1) (2, 0)) :
    ParentSquareOut G R (2, 0) :=
  case3_H hL (c := (1, 0)) (by decide) rfl hpres hR0 (Or.inl (StripColours.lap_one_one frame hS)) hR2

/-- `η = -1`, root `V_1 = (0,1)`: `(0,0) → (1,0) → (1,1) → (0,1)`, the case C.2 (vertical) with `δ = 1`, `c = (1,0)`. -/
theorem row_eta_neg_V1 (hL : LocalRetention G R) (frame : ChildFrame) (hS : frame.HasStrips G)
    (hpres : ∀ j, R (0, 1) j ↔ j = (0, 2))
    (hR0 : laplacian G (0, 0) = -1 ∨ R (0, 0) (1, 0))
    (hR1 : laplacian G (1, 0) = -1 ∨ R (1, 0) (1, 1)) :
    ParentSquareOut G R (0, 1) :=
  case2_V hL (δ := 1) (Or.inl rfl) (by decide) (c := (1, 0)) (by decide) hpres hR0 hR1
    (Or.inl (StripColours.lap_one_one frame hS))

/-- `η = +1`, root `V_prev = (1,-2)`: `(1,-1) → (2,-1) → (2,-2) → (1,-2)`, the case C.3 (vertical) with `δ = -1`, `c = (1,-1)`. -/
theorem row_eta_pos_Vprev (hL : LocalRetention G R) (frame : ChildFrame) (hS : frame.HasStrips G)
    (hpres : ∀ j, R (1, -2) j ↔ j = (1, -3))
    (hR0 : laplacian G (1, -1) = -1 ∨ R (1, -1) (2, -1))
    (hR2 : laplacian G (2, -2) = -1 ∨ R (2, -2) (1, -2)) :
    ParentSquareOut G R (1, -2) :=
  case3_V hL (δ := -1) (Or.inr rfl) (by decide) (c := (1, -1)) (by decide) hpres hR0
    (Or.inl (StripColours.lap_two_neg_one frame hS)) hR2

/-! ### The internal cases from the canonical policy

The kept input of a free root is its prescription (`CanonicalSignedPolicy.prescribed`), and the retention facts are those of the
canonical policy (`LocalRetention.of_canonical`). The three internal cases of section C, for the horizontal and the vertical
arcs, follow. The genuine arrows of the route are the named hypotheses `hR…`. -/

theorem prescribedH_even (frame : ChildFrame) (η : ℤ) {z : Site} (hz : EvenSite z) :
    frame.prescribedH η z = (1, 0) := by
  have h1 : z ≠ FLatticePaper.Induction.hFirst := by
    intro h; subst h; unfold EvenSite at hz; simp [FLatticePaper.Induction.hFirst] at hz
  have h2 : z ≠ frame.hLast := by
    intro h; subst h
    have hpar : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
    have hl : frame.hLast = (frame.child.den, frame.child.num - 1) := rfl
    have hz' : (frame.child.den + (frame.child.num - 1)) % 2 = 0 := by rw [hl] at hz; exact hz
    omega
  unfold ChildFrame.prescribedH; simp [h1, h2, hz]

theorem prescribedH_odd (frame : ChildFrame) (η : ℤ) {z : Site} (hz : ¬ EvenSite z)
    (h1 : z ≠ FLatticePaper.Induction.hFirst) (h2 : z ≠ frame.hLast) :
    frame.prescribedH η z = (0, 1) := by
  unfold ChildFrame.prescribedH; simp [h1, h2, hz]

theorem prescribedV_odd (frame : ChildFrame) (η : ℤ) {z : Site} (hz : ¬ EvenSite z) :
    frame.prescribedV η z = (0, -η) := by
  have h1 : z ≠ FLatticePaper.Induction.vFirst := by
    intro h; subst h; unfold EvenSite at hz; simp [FLatticePaper.Induction.vFirst] at hz
  have h2 : z ≠ frame.vLast := by
    intro h; subst h; have := frame.child_even; unfold EvenSite at hz; simp [ChildFrame.vLast] at hz this; omega
  unfold ChildFrame.prescribedV; simp [h1, h2, hz]

theorem prescribedV_even (frame : ChildFrame) (η : ℤ) {z : Site} (hz : EvenSite z)
    (h1 : z ≠ FLatticePaper.Induction.vFirst) : frame.prescribedV η z = (η, 0) := by
  unfold ChildFrame.prescribedV; simp [h1, hz]

/-- Section C, C.1 for the horizontal arc, from the canonical policy of the sign. -/
theorem internal_H_case1 {frame : ChildFrame} {G : Field} {η : ℤ} (C : CanonicalSignedPolicy frame G η)
    (hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0) {z c : Site}
    (hz : z ∈ frame.freeH) (hw : laplacian G z = 0) (hzodd : ¬ EvenSite z)
    (hz1 : z ≠ FLatticePaper.Induction.hFirst) (hz2 : z ≠ frame.hLast) (hc : c = (z.1 - 1, z.2))
    (hR0 : laplacian G (z.1, z.2 - 1) = -1 ∨ C.policy (z.1, z.2 - 1) (z.1 - 1, z.2 - 1))
    (hR1 : laplacian G (z.1 - 1, z.2 - 1) = -1 ∨ C.policy (z.1 - 1, z.2 - 1) c)
    (hR2 : laplacian G c = -1 ∨ C.policy c z) :
    ParentSquareOut G C.policy z := by
  have e : z + (0, 1) = (z.1, z.2 + 1) := Prod.ext (by simp) (by simp)
  have hpres : ∀ j, C.policy z j ↔ j = (z.1, z.2 + 1) := by
    intro j; rw [C.prescribed.1 z hz hw j, prescribedH_odd frame η hzodd hz1 hz2, e]
  exact case1_H (LocalRetention.of_canonical C hbin) hzodd hc hpres hR0 hR1 hR2

/-- Section C, C.2 for the horizontal arc. -/
theorem internal_H_case2 {frame : ChildFrame} {G : Field} {η : ℤ} (C : CanonicalSignedPolicy frame G η)
    (hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0) {z c : Site}
    (hz : z ∈ frame.freeH) (hw : laplacian G z = 0) (hzeven : EvenSite z) (hc : c = (z.1 - 1, z.2 - 1))
    (hR0 : laplacian G (z.1 - 1, z.2) = -1 ∨ C.policy (z.1 - 1, z.2) c)
    (hR1 : laplacian G c = -1 ∨ C.policy c (z.1, z.2 - 1))
    (hR2 : laplacian G (z.1, z.2 - 1) = -1 ∨ C.policy (z.1, z.2 - 1) z) :
    ParentSquareOut G C.policy z := by
  have e : z + (1, 0) = (z.1 + 1, z.2) := Prod.ext (by simp) (by simp)
  have hpres : ∀ j, C.policy z j ↔ j = (z.1 + 1, z.2) := by
    intro j; rw [C.prescribed.1 z hz hw j, prescribedH_even frame η hzeven, e]
  exact case2_H (LocalRetention.of_canonical C hbin) hzeven hc hpres hR0 hR1 hR2

/-- Section C, C.3 for the horizontal arc. -/
theorem internal_H_case3 {frame : ChildFrame} {G : Field} {η : ℤ} (C : CanonicalSignedPolicy frame G η)
    (hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0) {z c : Site}
    (hz : z ∈ frame.freeH) (hw : laplacian G z = 0) (hzeven : EvenSite z) (hc : c = (z.1 - 1, z.2))
    (hR0 : laplacian G c = -1 ∨ C.policy c (z.1 - 1, z.2 + 1))
    (hR1 : laplacian G (z.1 - 1, z.2 + 1) = -1 ∨ C.policy (z.1 - 1, z.2 + 1) (z.1, z.2 + 1))
    (hR2 : laplacian G (z.1, z.2 + 1) = -1 ∨ C.policy (z.1, z.2 + 1) z) :
    ParentSquareOut G C.policy z := by
  have e : z + (1, 0) = (z.1 + 1, z.2) := Prod.ext (by simp) (by simp)
  have hpres : ∀ j, C.policy z j ↔ j = (z.1 + 1, z.2) := by
    intro j; rw [C.prescribed.1 z hz hw j, prescribedH_even frame η hzeven, e]
  exact case3_H (LocalRetention.of_canonical C hbin) hzeven hc hpres hR0 hR1 hR2


/-- Section C, C.1 for the vertical arc, from the canonical policy of the sign (`δ = -η`; `z` of type B, even). -/
theorem internal_V_case1 {frame : ChildFrame} {G : Field} {η : ℤ} (C : CanonicalSignedPolicy frame G η)
    (hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0) {z c : Site} {δ : ℤ}
    (hδ : δ = -η) (hη : η = 1 ∨ η = -1)
    (hz : z ∈ frame.freeV) (hw : laplacian G z = 0) (heven : EvenSite z)
    (hz1 : z ≠ FLatticePaper.Induction.vFirst) (hc : c = (z.1, z.2 - δ))
    (hR0 : laplacian G (z.1 + δ, z.2) = -1 ∨ C.policy (z.1 + δ, z.2) (z.1 + δ, z.2 - δ))
    (hR1 : laplacian G (z.1 + δ, z.2 - δ) = -1 ∨ C.policy (z.1 + δ, z.2 - δ) c)
    (hR2 : laplacian G c = -1 ∨ C.policy c z) :
    ParentSquareOut G C.policy z := by
  have hδ1 : δ = 1 ∨ δ = -1 := by rcases hη with rfl | rfl <;> simp [hδ]
  have e : z + (η, 0) = (z.1 - δ, z.2) := Prod.ext (by simp [hδ]) (by simp)
  have hpres : ∀ j, C.policy z j ↔ j = (z.1 - δ, z.2) := by
    intro j; rw [C.prescribed.2 z hz hw j, prescribedV_even frame η heven hz1, e]
  exact case1_V (LocalRetention.of_canonical C hbin) hδ1 heven hc hpres hR0 hR1 hR2

/-- Section C, C.2 for the vertical arc (`z` of type A, odd; `c` of type A, diagonal). -/
theorem internal_V_case2 {frame : ChildFrame} {G : Field} {η : ℤ} (C : CanonicalSignedPolicy frame G η)
    (hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0) {z c : Site} {δ : ℤ}
    (hδ : δ = -η) (hη : η = 1 ∨ η = -1)
    (hz : z ∈ frame.freeV) (hw : laplacian G z = 0) (hzodd : ¬ EvenSite z) (hc : c = (z.1 + δ, z.2 - δ))
    (hR0 : laplacian G (z.1, z.2 - δ) = -1 ∨ C.policy (z.1, z.2 - δ) c)
    (hR1 : laplacian G c = -1 ∨ C.policy c (z.1 + δ, z.2))
    (hR2 : laplacian G (z.1 + δ, z.2) = -1 ∨ C.policy (z.1 + δ, z.2) z) :
    ParentSquareOut G C.policy z := by
  have hδ1 : δ = 1 ∨ δ = -1 := by rcases hη with rfl | rfl <;> simp [hδ]
  have e : z + (0, -η) = (z.1, z.2 + δ) := Prod.ext (by simp) (by simp [hδ])
  have hpres : ∀ j, C.policy z j ↔ j = (z.1, z.2 + δ) := by
    intro j; rw [C.prescribed.2 z hz hw j, prescribedV_odd frame η hzodd, e]
  exact case2_V (LocalRetention.of_canonical C hbin) hδ1 hzodd hc hpres hR0 hR1 hR2

/-- Section C, C.3 for the vertical arc (`z` of type A, odd; `c = z - a` of type B, even). -/
theorem internal_V_case3 {frame : ChildFrame} {G : Field} {η : ℤ} (C : CanonicalSignedPolicy frame G η)
    (hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0) {z c : Site} {δ : ℤ}
    (hδ : δ = -η) (hη : η = 1 ∨ η = -1)
    (hz : z ∈ frame.freeV) (hw : laplacian G z = 0) (hzodd : ¬ EvenSite z) (hc : c = (z.1, z.2 - δ))
    (hR0 : laplacian G c = -1 ∨ C.policy c (z.1 - δ, z.2 - δ))
    (hR1 : laplacian G (z.1 - δ, z.2 - δ) = -1 ∨ C.policy (z.1 - δ, z.2 - δ) (z.1 - δ, z.2))
    (hR2 : laplacian G (z.1 - δ, z.2) = -1 ∨ C.policy (z.1 - δ, z.2) z) :
    ParentSquareOut G C.policy z := by
  have hδ1 : δ = 1 ∨ δ = -1 := by rcases hη with rfl | rfl <;> simp [hδ]
  have e : z + (0, -η) = (z.1, z.2 + δ) := Prod.ext (by simp) (by simp [hδ])
  have hpres : ∀ j, C.policy z j ↔ j = (z.1, z.2 + δ) := by
    intro j; rw [C.prescribed.2 z hz hw j, prescribedV_odd frame η hzodd, e]
  exact case3_V (LocalRetention.of_canonical C hbin) hδ1 hzodd hc hpres hR0 hR1 hR2

end FLatticePaper.InternalReturns


