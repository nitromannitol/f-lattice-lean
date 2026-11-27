import FLatticePaper.Tiles.ClosedPathAssembly
import FLatticePaper.Tiles.ClosedPathCorners
import FLatticePaper.Tiles.SurgicalWeakOdometers

/-! # Condition (C) for both standard children, with the parents' respects as the input on the parents

`closedPathOdd_standard` and `closedPathEven_standard` state condition (C) (`ChildGlue.ClosedPathOdd`, `ClosedPathEven`) for the
placed subodometers of the standard step of any word `w`, in either orientation, with parents `oP`, `oQ` that respect their
strings (`RespectsAnchored`, as the joint induction provides for the tile odometers of the registers). The corner differences of
the closed path come from the respects (`cornerDiffs_odd`, `cornerDiffs_even`, through (b) in affine factors,
`corner_affine_12` and `corner_third`). The remaining inputs are those of `ClosedPathAssembly`, the excluded pairs and the
triangle identities being packaged by orientation (`ExclOdd`, `TriOdd`, `ExclEven`, `TriEven`). -/

namespace FLatticePaper.Tiles.ClosedPathStandard

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.SiteInduction
open FLatticePaper.Tiles.SiteStrings FLatticePaper.Tiles.ChildGlue FLatticePaper.Tiles.MixedPieces
open FLatticePaper.Tiles.ClosedPathSum FLatticePaper.Tiles.ClosedPathAssembly FLatticePaper.Tiles.ClosedPathCorners
open FLatticePaper.Tiles.StandardClause FLatticePaper.Tiles.SurgicalWeak

/-! ### The corner differences from the respects -/

/-- The corner differences of an odometer respecting `(w_h, w_v)` (`RespectsAnchored`), for a horizontal word from `q` to `p`
whose forward string ends at `X - 1 - i`, and a vertical word from `p` to `q` with `#p = d - n` and `#q = n`; the second vector is
`Y = (n - d, n + d)`. -/
theorem cornerDiffs_of_respects (wh wv : BinaryWord) (T : Finset Site) (S : GInt → ℤ) (n d : ℤ) (X : GInt)
    (hh : wh.head? = some .q) (hl : wh.getLast? = some .p) (hvh : wv.head? = some .p) (hvl : wv.getLast? = some .q)
    (hcp : (wv.count .p : ℤ) = d - n) (hcq : (wv.count .q : ℤ) = n)
    (hX : lastPosOf (hStringAt wh 0) = X - (1, 1)) (h : RespectsAnchored T wh wv S) :
    CornerDiffs S X (n - d, n + d) n d := by
  obtain ⟨-, hA, hC, hV, -⟩ := h
  have hlen : (wv.length : ℤ) = d := by
    have := length_eq_counts wv
    have h' : (wv.length : ℤ) = (wv.count .p : ℤ) + (wv.count .q : ℤ) := by exact_mod_cast this
    rw [h', hcp, hcq]
    ring
  have hne : wv ≠ [] := by
    rintro rfl
    simp at hvh
  obtain ⟨k, hk⟩ : ∃ k, wv.length = k + 1 :=
    ⟨wv.length - 1, by have := List.length_pos_of_ne_nil hne; omega⟩
  have h3 := corner_third wh wv k S hh hl hvh hvl hk hA hC hV
  obtain ⟨b1, b2⟩ := corner_affine_12 wh wv S hh hl hA hC
  have hb : CornerAffineStatement wh wv n d S := by
    refine ⟨b1, b2, ?_⟩
    rw [h3]
    have hq : ((wv.count .q : ℕ) : ℚ) = (n : ℚ) := by exact_mod_cast hcq
    have hk' : ((k : ℕ) : ℚ) = (d : ℚ) - 1 := by
      have : ((k : ℤ) : ℚ) + 1 = (d : ℚ) := by
        rw [← hlen, hk]
        push_cast
        ring
      push_cast at this ⊢
      linarith
    rw [hq, hk']
    ext <;> simp
  have hY : lastPosOf (vRevStringAt wv.reverse 0) = (n - d, n + d) + (1, -2) := by
    rw [vRev_last_top wv hvh hvl, hcq, hlen]
    ext <;> simp <;> ring
  obtain ⟨d1, d2⟩ := corner_diffs wh wv S n d X (n - d, n + d) hh hl hA hC hb hX hY
  refine ⟨?_, ?_⟩
  · have p1 : X + (n - d, n + d) + e₁ - e₂ = X + (n - d, n + d) + (1, -1) := by
      ext <;> (simp; try ring)
    have p2 : X + (n - d, n + d) - e₂ = X + (n - d, n + d) + (0, -1) := by
      ext <;> (simp; try ring)
    rw [p1, p2]
    exact d1
  · have p3 : (n - d, n + d) + e₁ - e₂ = (n - d, n + d) + (1, -1) := by
      ext <;> (simp; try ring)
    rw [p3]
    exact d2

/-- **The corner differences of a parent on the odd register**: an odometer respecting the strings of the odd standard tile of
`u`. -/
theorem cornerDiffs_odd (u : Word) (T : Finset Site) (S : GInt → ℤ)
    (h : RespectsAnchored T (hWordOf u false) (vWordOf u false) S) :
    CornerDiffs S (texV1Odd (fracOdd u)) (texV2 (fracOdd u)) (fracOdd u).num (fracOdd u).den :=
  cornerDiffs_of_respects (hWordOf u false) (vWordOf u false) T S _ _ _ (hWordOf_head_last u false).1
    (hWordOf_head_last u false).2 (StringCorners.vertWord_head_last u).1 (StringCorners.vertWord_head_last u).2
    (vertWord_counts u).1 (vertWord_counts u).2 (TexVPositions.lastPos_hWordOf_false_tex u) h

/-- **The corner differences of a parent on the even register**: an odometer respecting the strings of the even standard tile
of `u`. -/
theorem cornerDiffs_even (u : Word) (T : Finset Site) (S : GInt → ℤ)
    (h : RespectsAnchored T (hWordOf u true) (vWordOf u true) S) :
    CornerDiffs S (texV1Even (fracEven u)) (texV2 (fracEven u)) (fracEven u).num (fracEven u).den :=
  cornerDiffs_of_respects (hWordOf u true) (vWordOf u true) T S _ _ _ (hWordOf_head_last u true).1
    (hWordOf_head_last u true).2 (StringCorners.vWord_even_head_last u).1 (StringCorners.vWord_even_head_last u).2
    (StringCorners.vWord_even_counts u).1 (StringCorners.vWord_even_counts u).2
    (TexVPositions.lastPos_hWordOf_true_tex u) h

/-! ### The inputs at the excluded pairs and the optional interfaces, by orientation -/

/-- The two mixed pairs of copies of the odd child that never meet: `(P^+, Q^{+,2})`, `(P^-, Q^{-,1})` for `W_1` odd and
`(P^+, Q^{+,1})`, `(P^-, Q^{-,2})` for `W_1` even. -/
def ExclOdd (w u1 u2 : Word) : Prop :=
  if phase w = 1 then
    (∀ z, z ∈ dOdd w u1 u2 0 → z ∈ dOdd w u1 u2 3 → False) ∧ (∀ z, z ∈ dOdd w u1 u2 1 → z ∈ dOdd w u1 u2 4 → False)
  else
    (∀ z, z ∈ dOdd w u1 u2 0 → z ∈ dOdd w u1 u2 2 → False) ∧ (∀ z, z ∈ dOdd w u1 u2 1 → z ∈ dOdd w u1 u2 5 → False)

/-- The two mixed pairs of copies of the even child that never meet: `(P^{+,1}, Q^-)` and `(P^{-,2}, Q^+)`. -/
def ExclEven (w u1 u2 : Word) : Prop :=
  (∀ z, z ∈ dEven w u1 u2 0 → z ∈ dEven w u1 u2 5 → False) ∧ (∀ z, z ∈ dEven w u1 u2 3 → z ∈ dEven w u1 u2 4 → False)

/-- The triangle identities of the odd child at its two optional interfaces (the text's `z*`): if the copy of the plain parent
meets the farther copy of a doubled piece, then at one common point of their marks the offset is the offset through the
nearer copy plus the doubled offset. -/
def TriOdd (w u1 u2 : Word) (oP oQ : ℤ × ℤ → ℤ) (c : ℕ → ℤ) : Prop :=
  let f := placedOdd w oP oQ c
  let A := texV1Odd (parentsAt w).odd
  let B := texV2 (parentsAt w).odd
  let U := texV1Even (parentsAt w).even
  let V := texV2 (parentsAt w).even
  if phase w = 1 then
    ((∃ z, z ∈ mOdd w u1 u2 1 ∧ z ∈ mOdd w u1 u2 2) → ∃ z, z ∈ mOdd w u1 u2 1 ∧ z ∈ mOdd w u1 u2 2 ∧
        f 1 z - f 2 z = (f 1 (U + U + V + (A - e₂)) - f 3 (U + U + V + (A - e₂))) + (f 3 (A + U) - f 2 (A + U))) ∧
      ((∃ z, z ∈ mOdd w u1 u2 0 ∧ z ∈ mOdd w u1 u2 5) → ∃ z, z ∈ mOdd w u1 u2 0 ∧ z ∈ mOdd w u1 u2 5 ∧
        f 0 z - f 5 z = (f 0 (B + e₁) - f 4 (B + e₁)) + (f 4 (B + U) - f 5 (B + U)))
  else
    ((∃ z, z ∈ mOdd w u1 u2 1 ∧ z ∈ mOdd w u1 u2 3) → ∃ z, z ∈ mOdd w u1 u2 1 ∧ z ∈ mOdd w u1 u2 3 ∧
        f 1 z - f 3 z = (f 1 (V + e₁) - f 2 (V + e₁)) + (f 2 U - f 3 U)) ∧
      ((∃ z, z ∈ mOdd w u1 u2 0 ∧ z ∈ mOdd w u1 u2 4) → ∃ z, z ∈ mOdd w u1 u2 0 ∧ z ∈ mOdd w u1 u2 4 ∧
        f 0 z - f 4 z = (f 0 (U + U + (A + B - e₂)) - f 5 (U + U + (A + B - e₂))) +
          (f 5 (A + B + U) - f 4 (A + B + U)))

/-- The triangle identities of the even child at its two optional interfaces `(P^{+,2}, Q^+)` and `(P^{-,1}, Q^-)`. -/
def TriEven (w u1 u2 : Word) (oP oQ : ℤ × ℤ → ℤ) (c : ℕ → ℤ) : Prop :=
  let f := placedEven w oP oQ c
  let A := texV1Odd (parentsAt w).odd
  let B := texV2 (parentsAt w).odd
  let U := texV1Even (parentsAt w).even
  let V := texV2 (parentsAt w).even
  if phase w = 1 then
    ((∃ z, z ∈ mEven w u1 u2 1 ∧ z ∈ mEven w u1 u2 4) → ∃ z, z ∈ mEven w u1 u2 1 ∧ z ∈ mEven w u1 u2 4 ∧
        f 1 z - f 4 z = (f 1 (B + e₁) - f 0 (B + e₁)) + (f 0 A - f 4 A)) ∧
      ((∃ z, z ∈ mEven w u1 u2 2 ∧ z ∈ mEven w u1 u2 5) → ∃ z, z ∈ mEven w u1 u2 2 ∧ z ∈ mEven w u1 u2 5 ∧
        f 2 z - f 5 z = (f 2 (U + V + B + e₁) - f 3 (U + V + B + e₁)) +
          (f 3 (B + B + (U + V + e₁ - e₂)) - f 5 (B + B + (U + V + e₁ - e₂))))
  else
    ((∃ z, z ∈ mEven w u1 u2 1 ∧ z ∈ mEven w u1 u2 4) → ∃ z, z ∈ mEven w u1 u2 1 ∧ z ∈ mEven w u1 u2 4 ∧
        f 1 z - f 4 z = (f 1 (U + (B + e₁)) - f 0 (U + (B + e₁))) + (f 0 U - f 4 U)) ∧
      ((∃ z, z ∈ mEven w u1 u2 2 ∧ z ∈ mEven w u1 u2 5) → ∃ z, z ∈ mEven w u1 u2 2 ∧ z ∈ mEven w u1 u2 5 ∧
        f 2 z - f 5 z = (f 2 (V + B + e₁) - f 3 (V + B + e₁)) +
          (f 3 (A + B + B + (V + e₁ - e₂)) - f 5 (A + B + B + (V + e₁ - e₂))))

/-! ### Condition (C) for the standard children -/

/-- **Condition (C), odd standard child** (`ChildGlue.ClosedPathOdd`), in both orientations. The parents `oP`, `oQ` respect the
strings of the standard tiles of the register words `u1`, `u2` (whose fractions are the parents of `w`); `hdbl` is (c) of the
even parent at its first vector; `hcompat` is local compatibility of the mixed copies on their marks; `hexcl` and `htri` are the
excluded pairs and the triangle identities. -/
theorem closedPathOdd_standard (w u1 u2 : Word)
    (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2)
    (oP oQ : ℤ × ℤ → ℤ) (TP TQ : Finset Site) (c : ℕ → ℤ)
    (hRP : RespectsAnchored TP (hWordOf u1 false) (vWordOf u1 false) oP)
    (hRQ : RespectsAnchored TQ (hWordOf u2 true) (vWordOf u2 true) oQ)
    (hdbl : ∃ k : ℤ, ∀ x, x ∈ tEvenSet u2 → x + texV1Even (parentsAt w).even ∈ tEvenSet u2 →
      oQ (x + texV1Even (parentsAt w).even) - oQ x = k)
    (hcompat : MixedCompatOdd w u1 u2 (placedOdd w oP oQ c))
    (hexcl : ExclOdd w u1 u2) (htri : TriOdd w u1 u2 oP oQ c) :
    ClosedPathOdd w u1 u2 (placedOdd w oP oQ c) := by
  have hcP := cornerDiffs_odd u1 TP oP hRP
  have hcQ := cornerDiffs_even u2 TQ oQ hRQ
  rw [← hp] at hcP
  rw [← hq] at hcQ
  by_cases hph : phase w = 1
  · rw [ExclOdd, if_pos hph] at hexcl
    rw [TriOdd] at htri
    simp only [if_pos hph] at htri
    exact closedPathOdd_oddFirst w u1 u2 hph hp hq oP oQ c hcP hcQ hdbl hcompat hexcl htri
  · rw [ExclOdd, if_neg hph] at hexcl
    rw [TriOdd] at htri
    simp only [if_neg hph] at htri
    exact closedPathOdd_evenFirst w u1 u2 hph hp hq oP oQ c hcP hcQ hdbl hcompat hexcl htri

/-- **Condition (C), even standard child** (`ChildGlue.ClosedPathEven`), in both orientations; `hdbl` is (c) of the odd parent
at its second vector, with the affine factor `a_{p,2}`. -/
theorem closedPathEven_standard (w u1 u2 : Word)
    (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2)
    (oP oQ : ℤ × ℤ → ℤ) (TP TQ : Finset Site) (c : ℕ → ℤ)
    (hRP : RespectsAnchored TP (hWordOf u1 false) (vWordOf u1 false) oP)
    (hRQ : RespectsAnchored TQ (hWordOf u2 true) (vWordOf u2 true) oQ)
    (hdbl : ∃ k : ℤ, ∀ x, x ∈ tOddSet u1 → x + texV2 (parentsAt w).odd ∈ tOddSet u1 →
      oP (x + texV2 (parentsAt w).odd) - oP x - dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) x = k)
    (hcompat : MixedCompatEven w u1 u2 (placedEven w oP oQ c))
    (hexcl : ExclEven w u1 u2) (htri : TriEven w u1 u2 oP oQ c) :
    ClosedPathEven w u1 u2 (placedEven w oP oQ c) := by
  have hcP := cornerDiffs_odd u1 TP oP hRP
  have hcQ := cornerDiffs_even u2 TQ oQ hRQ
  rw [← hp] at hcP
  rw [← hq] at hcQ
  by_cases hph : phase w = 1
  · rw [TriEven] at htri
    simp only [if_pos hph] at htri
    exact closedPathEven_oddFirst w u1 u2 hph hp hq oP oQ c hcP hcQ hdbl hcompat hexcl htri
  · rw [TriEven] at htri
    simp only [if_neg hph] at htri
    exact closedPathEven_evenFirst w u1 u2 hph hp hq oP oQ c hcP hcQ hdbl hcompat hexcl htri

end FLatticePaper.Tiles.ClosedPathStandard
