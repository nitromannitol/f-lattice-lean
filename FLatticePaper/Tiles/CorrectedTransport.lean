import FLatticePaper.Tiles.CorrectedWalkZero
import FLatticePaper.Tiles.TileCompatRotation
import FLatticePaper.Tiles.StdPairCompatPaper

/-! # Condition (C) at the corrected decompositions: transport by the rotation, and the assembly

The rotation of the children carries the corrected decompositions after a `3` to those after a `2` at the swapped word
(`TileCompatRotation.standard_rows`, `alternate_rows`: every piece of the rotated decomposition is a rotated piece of the original
one). Agreement of the pieces with constants transports along such rows (`piecesAgree_of_rows`), which gives
`tEP_agree_of_tOP` and `aOP_agree_of_aEP`.

`tileWalkZero_of_edges`: condition (C) for the four corrected decompositions (`TileStepAssembly.TileWalkZeroInput`) from the two
local compatibility inputs of the tile step and the edge constants of the two decompositions after a `3` (`CorrectedEdgeInput`):
local compatibility and the edge constants give agreement (`CorrectedWalkZero.piecesAgree_of_edges`), agreement gives (C)
(`walkZero_of_agree`), and the decompositions after a `2` are reached by the rotation. -/

namespace FLatticePaper.Tiles.CorrectedTransport

open FLatticePaper FLatticePaper.Tiles FLatticePaper.Tiles.JointFamily FLatticePaper.Tiles.JointGlue
open FLatticePaper.Tiles.TileCompatRotation FLatticePaper.Farey
open FLatticePaper.Tiles.JointInduction (GoodBelow)
open FLatticePaper.Tiles.TileStepAssembly
open FLatticePaper.Tiles.TileCompatInputs (PairCompat oddLIdx evenLIdx altOddLIdx altEvenLIdx CorrectedCompatInput)

/-- **Agreement transports along rows**: if every piece of `qs` is a rotated piece of `ps` (`Row`), constants with which the
pieces of `ps` agree give constants with which those of `qs` agree. -/

theorem piecesAgree_of_rows {ps qs : List Piece} (σ : ℕ → ℕ) {c γ : Site} (n : ℕ) (hlen : qs.length ≤ n)
    (hrow : ∀ i < n, Row ps qs i (σ i) c γ) {κ : ℕ → ℤ} (h : PiecesAgree ps κ) : ∃ κ' : ℕ → ℤ, PiecesAgree qs κ' := by
  have key : ∀ i, ∃ b : ℤ, ∀ q, qs[i]? = some q → ∃ p, ps[σ i]? = some p ∧ ∀ x ∈ q.placed, x ∉ q.exc →
      mulI x + c ∈ p.placed ∧ mulI x + c ∉ p.exc ∧
        pieceVal q x = pieceVal p (mulI x + c) - h0 x + dotS γ x + b := by
    intro i
    by_cases hi : i < qs.length
    · obtain ⟨p, hp, b, hb⟩ := hrow i (by omega) (qs[i]'hi) (by simp)
      refine ⟨b, fun q hq => ?_⟩
      rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hq
      subst hq
      exact ⟨p, hp, hb⟩
    · refine ⟨0, fun q hq => ?_⟩
      rw [List.getElem?_eq_none (by omega)] at hq
      cases hq
  choose b hb using key
  refine ⟨fun i => κ (σ i) - b i, ?_⟩
  intro i j q q' hq hq' x hx hx' he he'
  obtain ⟨p, hp, hpx⟩ := hb i q hq
  obtain ⟨p', hp', hpx'⟩ := hb j q' hq'
  obtain ⟨m1, e1, v1⟩ := hpx x hx he
  obtain ⟨m2, e2, v2⟩ := hpx' x hx' he'
  have := h (σ i) (σ j) p p' hp hp' _ m1 m2 e1 e2
  rw [v1, v2]
  linarith


/-- The even standard decomposition after a `2`, from the odd one after a `3` at the swapped word. -/
theorem tEP_agree_of_tOP (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (f : Word → JSlice) (w : Word) (hg : GoodBelow D f w.length) (hw : CorrectedAfterThree w) {κ : ℕ → ℤ}
    (h : PiecesAgree (tOP D f w) κ) : ∃ κ' : ℕ → ℤ, PiecesAgree (tEP D f (Standard.swapW w)) κ' := by
  obtain ⟨hP, hQ⟩ := parent_rotations D hS hA f w hg hw.1
  have hL (elong : Bool) (hl : w.getLast? = some Digit.three) (plus : Bool) :
      JointRot.RawRot (TileCompatRotation.LE f w w.dropLast plus elong) (TileCompatRotation.LO f w (Standard.swapW w.dropLast) (plus != W1Odd w) elong)
        (vQ1 w - ((0 : ℤ),(1 : ℤ))) 0 := by
    have lt := JointRot.dropLast_length_lt hl
    simp only [TileCompatRotation.LE, TileCompatRotation.LO, JointRot.below_of_lt f w w.dropLast lt,
      JointRot.below_of_lt f w _ (by rwa [JointRot.length_swapW] : (Standard.swapW w.dropLast).length < w.length)]
    exact JointRot.lrot_three f w hw.1 hl (hg _ lt).2.2.2.2.1 elong plus
  have r := standard_rows D.S (O f w) (E f w) (LE f w) (LO f w) w hw.2 hP hQ hL
  have e : tEP D f (Standard.swapW w) = tileEvenPieces D.S (O f w) (E f w) (LO f w) (Standard.swapW w) := by
    unfold tEP O E LO; rw [JointRot.below_swapW]
  rw [e]
  exact piecesAgree_of_rows (stdIndex (W1Odd w)) 6 (by simp [tileEvenPieces]) r h

/-- The odd alternate decomposition after a `2`, from the even one after a `3` at the swapped word. -/
theorem aOP_agree_of_aEP (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (f : Word → JSlice) (w : Word) (hg : GoodBelow D f w.length) (hw : CorrectedAfterThree w) {κ : ℕ → ℤ}
    (h : PiecesAgree (aEP D f w) κ) : ∃ κ' : ℕ → ℤ, PiecesAgree (aOP D f (Standard.swapW w)) κ' := by
  obtain ⟨hP, hQ⟩ := parent_rotations D hS hA f w hg hw.1
  have hL (elong : Bool) (hl : w.getLast? = some Digit.three) (plus : Bool) :
      JointRot.RawRot (TileCompatRotation.LE f w w.dropLast plus elong) (TileCompatRotation.LO f w (Standard.swapW w.dropLast) (plus != W1Odd w) elong)
        (vQ1 w - ((0 : ℤ),(1 : ℤ))) 0 := by
    have lt := JointRot.dropLast_length_lt hl
    simp only [TileCompatRotation.LE, TileCompatRotation.LO, JointRot.below_of_lt f w w.dropLast lt,
      JointRot.below_of_lt f w _ (by rwa [JointRot.length_swapW] : (Standard.swapW w.dropLast).length < w.length)]
    exact JointRot.lrot_three f w hw.1 hl (hg _ lt).2.2.2.2.1 elong plus
  have r := alternate_rows D.S (O f w) (E f w) (AO f w) (AE f w) (LE f w) (LO f w) w hw.2 hP hQ hL
  have e : aOP D f (Standard.swapW w) =
      tileAltOddPieces D.S (O f w) (E f w) (AO f w) (AE f w) (LO f w) (Standard.swapW w) := by
    unfold aOP O E AO AE LO; rw [JointRot.below_swapW]
  rw [e]
  have hl2 : (Standard.swapW w).getLast? = some Digit.two := by
    rw [JointRot.getLast_swapW, hw.2]; rfl
  exact piecesAgree_of_rows (altIndex (W1Odd w)) 6
    (by simp [tileAltOddPieces, hl2, SurgicalAlt.altTypeOf, SurgicalAlt.altQ1Coeff]) r h

/-- The edge constants of the two corrected decompositions after a `3`: the input of condition (C) at the corrected words. -/
def CorrectedEdgeInput (D : JointData) : Prop :=
  ∀ (f : Word → JSlice) (w : Word), GoodBelow D f w.length → CorrectedAfterThree w →
    (∃ κ : ℕ → ℤ, CorrectedWalkZero.EdgeConst (tOP D f w) κ) ∧ (∃ κ : ℕ → ℤ, CorrectedWalkZero.EdgeConst (aEP D f w) κ)

/-- Local compatibility of every pair of a six-piece decomposition, from the pairs with an L-entry and the pairs without. -/
theorem compat_all (ps : List Piece) (hlen : ps.length = 6) (L : List ℕ)
    (hL : ∀ i ∈ L, ∀ j < 6, j ≠ i → PairCompat ps i j) (hN : ∀ i j, i ∉ L → j ∉ L → PairCompat ps i j) :
    ∀ i j, i < ps.length → j < ps.length → PairCompat ps i j := by
  intro i j hi hj
  by_cases hij : i = j
  · subst hij; exact pairCompat_refl ps i
  by_cases h1 : i ∈ L
  · exact hL i h1 j (by omega) (Ne.symm hij)
  by_cases h2 : j ∈ L
  · exact pairCompat_symm (hL j h2 i (by omega) hij)
  exact hN i j h1 h2

/-- Agreement of the two corrected decompositions after a `3`. -/
theorem agree_three (D : JointData) (hcc : CorrectedCompatInput D) (hsp : StdPairCompatInput D)
    (hE : CorrectedEdgeInput D) (f : Word → JSlice) (w : Word) (hg : GoodBelow D f w.length) (h3 : CorrectedAfterThree w) :
    (∃ κ : ℕ → ℤ, PiecesAgree (tOP D f w) κ) ∧ (∃ κ : ℕ → ℤ, PiecesAgree (aEP D f w) κ) := by
  obtain ⟨⟨κ, hκ⟩, ⟨κ', hκ'⟩⟩ := hE f w hg h3
  have hc := hcc f w hg h3.1
  have hs := (hsp f w hg h3.1).1 h3
  have hlA : (aEP D f w).length = 6 := by
    simp [aEP, tileAltEvenPieces, h3.2, SurgicalAlt.altTypeOf, SurgicalAlt.altP1Coeff]
  refine ⟨⟨κ, CorrectedWalkZero.piecesAgree_of_edges _ κ
      (compat_all _ (StdPairCompatPaper.tOP_length D f w) (oddLIdx w) (hc.1 h3) hs.1) hκ⟩,
    ⟨κ', CorrectedWalkZero.piecesAgree_of_edges _ κ' (compat_all _ hlA altEvenLIdx (hc.2.2.2 h3) hs.2) hκ'⟩⟩

/-- **Condition (C) at the four corrected decompositions** (`TileWalkZeroInput`) from the local compatibility inputs of the tile
step and the edge constants after a `3`. -/
theorem tileWalkZero_of_edges (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (hcc : CorrectedCompatInput D) (hsp : StdPairCompatInput D) (hE : CorrectedEdgeInput D) : TileWalkZeroInput D := by
  intro f w hg hb
  refine ⟨fun h3 => ?_, fun h2 => ?_⟩
  · obtain ⟨⟨κ, hκ⟩, ⟨κ', hκ'⟩⟩ := agree_three D hcc hsp hE f w hg h3
    exact ⟨CorrectedWalkZero.walkZero_of_agree _ κ hκ, CorrectedWalkZero.walkZero_of_agree _ κ' hκ'⟩
  · have h3 : CorrectedAfterThree (Standard.swapW w) :=
      ⟨Standard.nonbase_swap hb, by rw [JointRot.getLast_swapW, h2.2]; rfl⟩
    have hg' : GoodBelow D f (Standard.swapW w).length := by rwa [JointRot.length_swapW]
    obtain ⟨⟨κ, hκ⟩, ⟨κ', hκ'⟩⟩ := agree_three D hcc hsp hE f _ hg' h3
    obtain ⟨μ, hμ⟩ := tEP_agree_of_tOP D hS hA f _ hg' h3 hκ
    obtain ⟨μ', hμ'⟩ := aOP_agree_of_aEP D hS hA f _ hg' h3 hκ'
    rw [JointRot.swapW_swapW'] at hμ hμ'
    exact ⟨CorrectedWalkZero.walkZero_of_agree _ μ hμ, CorrectedWalkZero.walkZero_of_agree _ μ' hμ'⟩

end FLatticePaper.Tiles.CorrectedTransport
