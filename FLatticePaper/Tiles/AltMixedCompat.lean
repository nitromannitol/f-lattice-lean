import FLatticePaper.Tiles.ClosedPathAlt

/-! The mixed standard subtiles of the alternate children. On each nonempty interface
the relative position and the difference of the two affine factors occur together in
the standard odd child. This transports the height difference as well as the marks. -/

namespace FLatticePaper.Tiles.AltMixedCompat

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open FLatticePaper.Tiles.SiteInduction FLatticePaper.Tiles.ChildGlue
open FLatticePaper.Tiles.ClosedPathAssembly FLatticePaper.Tiles.ClosedPathAlt
open FLatticePaper.Tiles.ClosedPathCycle FLatticePaper.Tiles.ClosedPathSum
open FLatticePaper.Tiles.StandardClause

private def relative (M N : Set Site) (P Q : Site → ℤ) (v s : Site) : Prop :=
  ∃ C : ℤ, ∀ x ∈ M, x + v ∈ N → P x - Q (x + v) + dot2 s x = C

private theorem relative_iff (M N : Set Site) (P Q : Site → ℤ) (a b s t : Site) (c d : ℤ) :
    relative M N P Q (a - b) (s - t) ↔
      ∃ C : ℤ, ∀ z ∈ shiftS M a, z ∈ shiftS N b →
        P (z - a) + dot2 s z + c - (Q (z - b) + dot2 t z + d) = C := by
  have affine (x : Site) : dot2 s (x + a) - dot2 t (x + a) = dot2 (s - t) x + dot2 (s - t) a := by
    simp only [dot2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
    ring
  constructor
  · rintro ⟨C, h⟩
    refine ⟨C + dot2 (s - t) a + c - d, ?_⟩
    rintro _ ⟨x, hx, rfl⟩ hz
    have he : x + (a - b) = x + a - b := (add_sub_assoc ..).symm
    have hh := h x hx (he ▸ sub_mem_of_shift N b _ hz)
    rw [he] at hh
    rw [add_sub_cancel_right]
    linarith only [hh, affine x]
  · rintro ⟨C, h⟩
    refine ⟨C - dot2 (s - t) a - c + d, fun x hx hy => ?_⟩
    have he : x + (a - b) = x + a - b := (add_sub_assoc ..).symm
    have hh := h (x + a) ⟨x, hx, rfl⟩ ⟨x + (a - b), hy, by simpa only [he] using sub_add_cancel (x + a) b⟩
    rw [add_sub_cancel_right, ← he] at hh
    linarith only [hh, affine x]

private abbrev own (w : Word) := affOdd (parentsAt w).odd (parentsAt w).even

private theorem standard_relative (w u v : Word) (P Q : Site → ℤ)
    (h : MixedCompatOdd w u v (placedOdd w P Q 0)) (i j : ℕ) (hi : i < 2) (hj : 2 ≤ j) (hj' : j < 6) :
    relative (marksOdd u) (marksEven v) P Q
      ((oddP w).getD i 0 - (oddQ w).getD (j - 2) 0) (own w i - own w j) := by
  apply (relative_iff _ _ _ _ _ _ _ _ 0 0).2
  simpa only [mOdd, pieceSet, oddP_length, placedOdd, if_pos hi, if_neg (Nat.not_lt_of_ge hj),
    Pi.zero_apply] using h i j hi hj hj'

private theorem piece_mono (A B : List Site) {M M' N N' : Set Site} (hm : M ⊆ M') (hn : N ⊆ N') (i : ℕ) :
    pieceSet A B M N i ⊆ pieceSet A B M' N' i := by
  unfold pieceSet
  split
  · exact Set.image_mono hm
  · exact Set.image_mono hn

private theorem eight {R : ℕ → ℕ → Prop}
    (hits : ∀ i : Fin 4, R i (i.val % 2 + 4))
    (miss : R 0 5 ∧ R 1 4 ∧ R 2 5 ∧ R 3 4) :
    ∀ i j, i < 4 → 4 ≤ j → j < 6 → R i j := by
  intro i j hi hj hk
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
    rcases (by omega : j = 4 ∨ j = 5) with rfl | rfl
  · exact hits 0
  · exact miss.1
  · exact miss.2.1
  · exact hits 1
  · exact hits 2
  · exact miss.2.2.1
  · exact miss.2.2.2
  · exact hits 3

private abbrev lastIdx (i : Fin 4) : ℕ := i.val % 2 + 4

private theorem odd_match (w : Word) (i : Fin 4) :
    ∃ k l : ℕ, k < 2 ∧ 2 ≤ l ∧ l < 6 ∧
      (altOddD w).getD i 0 - (altOddR w).getD (lastIdx i - 4) 0 =
        (oddP w).getD k 0 - (oddQ w).getD (l - 2) 0 ∧
      (altOddAff w).getD i 0 - (altOddAff w).getD (lastIdx i) 0 = own w k - own w l := by
  by_cases h : phase w = 1
  · obtain ⟨hD, hR, hA, hS⟩ := altOdd_of w h
    refine ⟨i.val / 2, ([2, 4, 3, 5] : List ℕ).getD i 0, ?_, ?_, ?_, ?_, ?_⟩
    all_goals fin_cases i <;> first | decide |
      simp [hD, hR, hA, hS, oddP_of w h, oddQ_of w h, lastIdx, own, affOdd] <;> abel
  · obtain ⟨hD, hR, hA, hS⟩ := altOdd_ef w h
    refine ⟨i.val / 2, ([3, 5, 2, 4] : List ℕ).getD i 0, ?_, ?_, ?_, ?_, ?_⟩
    all_goals fin_cases i <;> first | decide |
      simp [hD, hR, hA, hS, oddP_ef w h, oddQ_ef w h, lastIdx, own, affOdd] <;> abel

private theorem even_match (w : Word) (i : Fin 4) :
    ∃ k l : ℕ, k < 2 ∧ 2 ≤ l ∧ l < 6 ∧
      (altEvenR w).getD (lastIdx i - 4) 0 - (altEvenD w).getD i 0 =
        (oddP w).getD k 0 - (oddQ w).getD (l - 2) 0 ∧
      (altEvenAff w).getD (lastIdx i) 0 - (altEvenAff w).getD i 0 = own w k - own w l := by
  by_cases h : phase w = 1
  · obtain ⟨hD, hR, hA, hS⟩ := altEven_of w h
    refine ⟨i.val % 2, ([2, 3, 4, 5] : List ℕ).getD i 0, ?_, ?_, ?_, ?_, ?_⟩
    all_goals fin_cases i <;> first | decide |
      simp [hD, hR, hA, hS, oddP_of w h, oddQ_of w h, lastIdx, own, affOdd] <;> abel
  · obtain ⟨hD, hR, hA, hS⟩ := altEven_ef w h
    refine ⟨i.val % 2, ([3, 2, 5, 4] : List ℕ).getD i 0, ?_, ?_, ?_, ?_, ?_⟩
    all_goals fin_cases i <;> first | decide |
      simp [hD, hR, hA, hS, oddP_ef w h, oddQ_ef w h, lastIdx, own, affOdd] <;> abel

/-- The four mixed interfaces among the standard subtiles of the odd alternate child inherit
the local differences of the odd standard child. -/
theorem odd_of_standard (w u v : Word) (hp : (parentsAt w).odd = fracOdd u)
    (hq : (parentsAt w).even = fracEven v) (P Q : Site → ℤ) (c : ℕ → ℤ)
    (h : MixedCompatOdd w u v (placedOdd w P Q 0)) : AltMixedCompatOdd w u v (placedAltOdd w P Q c) := by
  apply eight
  · intro i
    obtain ⟨k, l, hk, hl, hl', hv, hs⟩ := odd_match w i
    have hc := standard_relative w u v P Q h k l hk hl hl'
    rw [← hv, ← hs] at hc
    have hab := (relative_iff _ _ _ _ _ _ _ _ (c i) (c (lastIdx i))).1 hc
    have hj : ¬ lastIdx i < 4 := by unfold lastIdx; omega
    have hlen : (altOddD w).length = 4 := rfl
    simpa only [mAO, pieceSet, hlen, if_pos i.isLt, if_neg hj, placedAltOdd] using hab
  · have hEx := if hph : phase w = 1 then altExclOdd_of w u v hph hp hq else altExclOdd_ef w u v hph hp hq
    have lift (i : ℕ) : mAO w u v i ⊆ dAO w u v i :=
      piece_mono _ _ (MarksIn.marksOdd_sub u) (MarksIn.marksEven_sub v) i
    have miss (i j : ℕ) (he : ∀ z, z ∈ dAO w u v i → z ∈ dAO w u v j → False) :
        ∃ C : ℤ, ∀ z ∈ mAO w u v i, z ∈ mAO w u v j →
          placedAltOdd w P Q c i z - placedAltOdd w P Q c j z = C :=
      ⟨0, fun z hi hj => (he z (lift i hi) (lift j hj)).elim⟩
    exact ⟨miss _ _ hEx.1, miss _ _ hEx.2.1, miss _ _ hEx.2.2.1, miss _ _ hEx.2.2.2⟩

/-- The four mixed interfaces among the standard subtiles of the even alternate child,
with the doubled even parent indexed first. -/
theorem even_of_standard (w u v : Word) (hp : (parentsAt w).odd = fracOdd u)
    (hq : (parentsAt w).even = fracEven v) (P Q : Site → ℤ) (c : ℕ → ℤ)
    (h : MixedCompatOdd w u v (placedOdd w P Q 0)) : AltMixedCompatEven w u v (placedAltEven w P Q c) := by
  apply eight
  · intro i
    obtain ⟨k, l, hk, hl, hl', hv, hs⟩ := even_match w i
    have hc := standard_relative w u v P Q h k l hk hl hl'
    rw [← hv, ← hs] at hc
    obtain ⟨K, hK⟩ := (relative_iff _ _ _ _ _ _ _ _ (c (lastIdx i)) (c i)).1 hc
    refine ⟨-K, fun z hx hy => ?_⟩
    have hj : ¬ lastIdx i < 4 := by unfold lastIdx; omega
    have hlen : (altEvenD w).length = 4 := rfl
    change z ∈ mAE w u v (lastIdx i) at hy
    simp only [mAE, pieceSet, hlen, if_pos i.isLt, if_neg hj] at hx hy
    have hval := hK z hy hx
    change placedAltEven w P Q c i z - placedAltEven w P Q c (lastIdx i) z = -K
    simp only [placedAltEven, if_pos i.isLt, if_neg hj]
    omega
  · have hEx := if hph : phase w = 1 then altExclEven_of w u v hph hp hq else altExclEven_ef w u v hph hp hq
    have lift (i : ℕ) : mAE w u v i ⊆ dAE w u v i :=
      piece_mono _ _ (MarksIn.marksEven_sub v) (MarksIn.marksOdd_sub u) i
    have miss (i j : ℕ) (he : ∀ z, z ∈ dAE w u v i → z ∈ dAE w u v j → False) :
        ∃ C : ℤ, ∀ z ∈ mAE w u v i, z ∈ mAE w u v j →
          placedAltEven w P Q c i z - placedAltEven w P Q c j z = C :=
      ⟨0, fun z hi hj => (he z (lift i hi) (lift j hj)).elim⟩
    exact ⟨miss _ _ hEx.1, miss _ _ hEx.2.1, miss _ _ hEx.2.2.1, miss _ _ hEx.2.2.2⟩

end FLatticePaper.Tiles.AltMixedCompat
