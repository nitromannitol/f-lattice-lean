import FLatticePaper.Tiles.ChildGlue

/-! # Condition (C): the reduction to agreement of pairs, and the potential of a closed path

Condition (C) of the existence step of `lemma:weak_standard_odometer_properties` (Step 1), in the form
`ChildGlue.ClosedPathOdd` / `ClosedPathEven`, asks for piece constants `κ` such that the placed subodometers `f0 i + κ i` agree
on the marks of every two copies of different parents, and on the whole overlap of the two copies of each doubled piece.

This module contains the two combinatorial steps of the proof, which do not depend on the tiles.

* `closedPathOdd_of_pairs`, `closedPathEven_of_pairs`: the index bookkeeping. The odd child has the copies `0, 1` of the odd
  register and `2, …, 5` of the even register, the doubled pairs being `(2, 3)` and `(4, 5)`; the even child has the copies
  `0, …, 3` of the odd register and `4, 5` of the even one, the doubled pairs being `(0, 1)` and `(2, 3)`. It is enough to give
  the agreement for each mixed pair in one order and for the two doubled pairs.
* `agree_of_witness`: two functions whose difference is constant on a set agree on it as soon as they agree at one point.
  This is how the text concludes, at every interface, from local compatibility and the value at one common point.
* `hexKappa`, `hexKappa_spec`: on a closed path of six pieces, with one chosen point on each of the six interfaces, the
  constants obtained by walking along the path make the pieces agree at the five chosen points of the path, and at the
  sixth one exactly when the six offsets sum to zero (the closed-path condition of `lemma:pairwise_compatibility`). -/

namespace FLatticePaper.Tiles.ClosedPathCycle

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.ChildGlue FLatticePaper.Tiles.SiteInduction
open FLatticePaper.Tiles.MixedPieces

/-! ### The number of copies of each parent -/

theorem oddP_length (w : Word) : (oddP w).length = 2 := by
  unfold oddP pOffsetsOdd
  split <;> rfl

theorem oddQ_length (w : Word) : (oddQ w).length = 4 := by
  unfold oddQ qOffsetsOdd
  split <;> rfl

theorem evenP_length (w : Word) : (evenP w).length = 4 := by
  unfold evenP pOffsetsEven
  split <;> rfl

theorem evenQ_length (w : Word) : (evenQ w).length = 2 := by
  unfold evenQ qOffsetsEven
  split <;> rfl

/-! ### Agreement from a constant difference and one common value -/

/-- Two functions whose difference is constant on `S` and which agree at one point of `S` agree on `S`. -/
theorem agree_of_witness (S : Set (ℤ × ℤ)) (g h : ℤ × ℤ → ℤ)
    (hc : ∃ c : ℤ, ∀ z ∈ S, g z - h z = c) (y : ℤ × ℤ) (hy : y ∈ S) (hyw : g y = h y) :
    ∀ z ∈ S, g z = h z := by
  obtain ⟨c, hc⟩ := hc
  intro z hz
  have h1 := hc z hz
  have h2 := hc y hy
  linarith

/-! ### The reduction of (C) to the agreement of pairs -/

/-- **Odd child.** Condition (C) follows from the agreement of the subodometers with constants `κ` for every mixed pair
`i < 2 ≤ j < 6` on the marks of both copies, and for the two doubled pairs `(2, 3)`, `(4, 5)` on their whole overlap. -/
theorem closedPathOdd_of_pairs (w u1 u2 : Word) (f0 : ℕ → ℤ × ℤ → ℤ) (κ : ℕ → ℤ)
    (hmix : ∀ i j, i < 2 → 2 ≤ j → j < 6 → ∀ z,
      z ∈ pieceSet (oddP w) (oddQ w) (marksOdd u1) (marksEven u2) i →
      z ∈ pieceSet (oddP w) (oddQ w) (marksOdd u1) (marksEven u2) j → f0 i z + κ i = f0 j z + κ j)
    (hd23 : ∀ z, z ∈ pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 2 →
      z ∈ pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 3 → f0 2 z + κ 2 = f0 3 z + κ 3)
    (hd45 : ∀ z, z ∈ pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 4 →
      z ∈ pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 5 → f0 4 z + κ 4 = f0 5 z + κ 5) :
    ClosedPathOdd w u1 u2 f0 := by
  have hP := oddP_length w
  have hQ := oddQ_length w
  refine ⟨κ, ?_, ?_⟩
  · intro i j hi hj hfl z hzi hzj
    rw [hP, hQ] at hi hj
    simp only [pieceFlag, hP, ne_eq, decide_eq_decide] at hfl
    by_cases hi2 : i < 2
    · have hj2 : 2 ≤ j := by omega
      exact hmix i j hi2 hj2 hj z hzi hzj
    · have hj2 : j < 2 := by omega
      exact (hmix j i hj2 (by omega) hi z hzj hzi).symm
  · intro i j _ _ _ _ hd z hzi hzj
    obtain ⟨rfl, hi⟩ := hd
    rw [hP] at hi
    rcases hi with rfl | rfl
    · exact hd23 z hzi hzj
    · exact hd45 z hzi hzj

/-- **Even child.** Condition (C) follows from the agreement for every mixed pair `i < 4 ≤ j < 6` on the marks of both
copies, and for the two doubled pairs `(0, 1)`, `(2, 3)` on their whole overlap. -/
theorem closedPathEven_of_pairs (w u1 u2 : Word) (f0 : ℕ → ℤ × ℤ → ℤ) (κ : ℕ → ℤ)
    (hmix : ∀ i j, i < 4 → 4 ≤ j → j < 6 → ∀ z,
      z ∈ pieceSet (evenP w) (evenQ w) (marksOdd u1) (marksEven u2) i →
      z ∈ pieceSet (evenP w) (evenQ w) (marksOdd u1) (marksEven u2) j → f0 i z + κ i = f0 j z + κ j)
    (hd01 : ∀ z, z ∈ pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) 0 →
      z ∈ pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) 1 → f0 0 z + κ 0 = f0 1 z + κ 1)
    (hd23 : ∀ z, z ∈ pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) 2 →
      z ∈ pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) 3 → f0 2 z + κ 2 = f0 3 z + κ 3) :
    ClosedPathEven w u1 u2 f0 := by
  have hP := evenP_length w
  have hQ := evenQ_length w
  refine ⟨κ, ?_, ?_⟩
  · intro i j hi hj hfl z hzi hzj
    rw [hP, hQ] at hi hj
    simp only [pieceFlag, hP, ne_eq, decide_eq_decide] at hfl
    by_cases hi4 : i < 4
    · have hj4 : 4 ≤ j := by omega
      exact hmix i j hi4 hj4 hj z hzi hzj
    · have hj4 : j < 4 := by omega
      exact (hmix j i hj4 (by omega) hi z hzj hzi).symm
  · intro i j _ _ _ _ hd z hzi hzj
    obtain ⟨rfl, hi⟩ := hd
    rcases hi with rfl | rfl
    · exact hd01 z hzi hzj
    · exact hd23 z hzi hzj

/-! ### The potential of a closed path of six pieces -/

/-- The constants of six pieces `i0, …, i5` in the order of a closed path, with the chosen point `z k` on the interface of
`i k` and `i (k+1)`: `κ i0 = 0`, and each next constant makes the next two pieces agree at the chosen point. Other indices get
`0`. -/
def hexKappa (f : ℕ → ℤ × ℤ → ℤ) (i0 i1 i2 i3 i4 i5 : ℕ) (z0 z1 z2 z3 z4 : ℤ × ℤ) : ℕ → ℤ := fun i =>
  let k1 := f i0 z0 - f i1 z0
  let k2 := k1 + f i1 z1 - f i2 z1
  let k3 := k2 + f i2 z2 - f i3 z2
  let k4 := k3 + f i3 z3 - f i4 z3
  let k5 := k4 + f i4 z4 - f i5 z4
  if i = i1 then k1 else if i = i2 then k2 else if i = i3 then k3 else if i = i4 then k4 else
    if i = i5 then k5 else 0

/-- The constants of `hexKappa` make consecutive pieces agree at the chosen points of the path; at the closing point `z5`
they agree exactly when the six offsets `f (i k) (z k) - f (i (k+1)) (z k)` sum to zero. -/
theorem hexKappa_spec (f : ℕ → ℤ × ℤ → ℤ) (i0 i1 i2 i3 i4 i5 : ℕ) (z0 z1 z2 z3 z4 z5 : ℤ × ℤ)
    (hd : [i0, i1, i2, i3, i4, i5].Nodup) :
    let κ := hexKappa f i0 i1 i2 i3 i4 i5 z0 z1 z2 z3 z4
    κ i0 = 0 ∧
    f i0 z0 + κ i0 = f i1 z0 + κ i1 ∧ f i1 z1 + κ i1 = f i2 z1 + κ i2 ∧ f i2 z2 + κ i2 = f i3 z2 + κ i3 ∧
    f i3 z3 + κ i3 = f i4 z3 + κ i4 ∧ f i4 z4 + κ i4 = f i5 z4 + κ i5 ∧
    ((f i5 z5 + κ i5 = f i0 z5 + κ i0) ↔
      (f i0 z0 - f i1 z0) + (f i1 z1 - f i2 z1) + (f i2 z2 - f i3 z2) + (f i3 z3 - f i4 z3) +
        (f i4 z4 - f i5 z4) + (f i5 z5 - f i0 z5) = 0) := by
  have h01 : i0 ≠ i1 := fun h => by subst h; simp at hd
  have h02 : i0 ≠ i2 := fun h => by subst h; simp at hd
  have h03 : i0 ≠ i3 := fun h => by subst h; simp at hd
  have h04 : i0 ≠ i4 := fun h => by subst h; simp at hd
  have h05 : i0 ≠ i5 := fun h => by subst h; simp at hd
  have h12 : i1 ≠ i2 := fun h => by subst h; simp at hd
  have h13 : i1 ≠ i3 := fun h => by subst h; simp at hd
  have h14 : i1 ≠ i4 := fun h => by subst h; simp at hd
  have h15 : i1 ≠ i5 := fun h => by subst h; simp at hd
  have h23 : i2 ≠ i3 := fun h => by subst h; simp at hd
  have h24 : i2 ≠ i4 := fun h => by subst h; simp at hd
  have h25 : i2 ≠ i5 := fun h => by subst h; simp at hd
  have h34 : i3 ≠ i4 := fun h => by subst h; simp at hd
  have h35 : i3 ≠ i5 := fun h => by subst h; simp at hd
  have h45 : i4 ≠ i5 := fun h => by subst h; simp at hd
  simp only [hexKappa, h01, h02, h03, h04, h05, h12, Ne.symm h12, h13, Ne.symm h13, h14, Ne.symm h14, h15,
    Ne.symm h15, h23, Ne.symm h23, h24, Ne.symm h24, h25, Ne.symm h25, h34, Ne.symm h34, h35, Ne.symm h35, h45,
    Ne.symm h45, if_true, if_false]
  refine ⟨trivial, by ring, by ring, by ring, by ring, by ring, ?_⟩
  constructor <;> intro h <;> linarith

end FLatticePaper.Tiles.ClosedPathCycle
