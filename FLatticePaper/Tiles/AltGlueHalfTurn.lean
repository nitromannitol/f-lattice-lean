import FLatticePaper.Tiles.AltLatticeCore
import FLatticePaper.Tiles.JointGlue

/-! # Item (b) of `lemma:weak_alternate_odometer_properties`: the half-turn of the glued weak alternate odometer

A piece `T + off` of the alternate decomposition, with a parent `T` that has the normalised half-turn identity
`2(T(C - z) - T(z)) = aᵀC - 2aᵀz` of (b) of `lemma:tile-odometer-existence` (with `α = 0`, `JointRot.family_slopes`), is
mapped by `y ↦ D - y` onto the piece `T + off'` with `off' = D - C - off`; if the affine factors satisfy
`aff + aff' = E - a`, the values satisfy `2(val'(D - y) - val(y)) = -2Eᵀy + const` (`piece_halfTurn`). An odometer that
respects all the pieces then has the half-turn identity with the slope `-2E`, once the constants of the pieces agree along a
spanning tree of the overlap graph (`halfTurn_of_pieces`). -/

namespace FLatticePaper.Tiles.AltGlueHalfTurn

open FLatticePaper FLatticePaper.Farey FLatticePaper.Tiles
open FLatticePaper.Tiles.JointFamily (Piece stdPiece RespectsPieces)
open FLatticePaper.Tiles.JointGlue (pieceVal)
open FLatticePaper.Tiles.AltLatticeCore (HalfTurnId dotS_add dotS_sub)

theorem mem_placed_iff (p : Piece) (y : Site) : y ∈ p.placed ↔ y - p.off ∈ p.odo.dom := by
  unfold Piece.placed
  rw [Finset.mem_image]
  constructor
  · rintro ⟨z, hz, rfl⟩; rwa [add_sub_cancel_right]
  · intro h; exact ⟨y - p.off, h, sub_add_cancel y p.off⟩

/-- **The half-turn of one piece.** -/
theorem piece_halfTurn (T : PartialOdometer) (C a : Site)
    (HT : ∀ z ∈ T.dom, C - z ∈ T.dom ∧ 2 * (T.val (C - z) - T.val z) = dotS a C - 2 * dotS a z)
    (D off off' aff aff' E : Site) (hoff : off' = D - C - off) (haff : aff + aff' = E - a) (y : Site)
    (hy : y ∈ (stdPiece T off aff).placed) :
    D - y ∈ (stdPiece T off' aff').placed ∧
      2 * (pieceVal (stdPiece T off' aff') (D - y) - pieceVal (stdPiece T off aff) y) =
        dotS (-(2 : ℤ) • E) y + (dotS a C + 2 * dotS a off + 2 * dotS aff' D) := by
  rw [mem_placed_iff] at hy
  simp only [stdPiece] at hy
  obtain ⟨h1, h2⟩ := HT _ hy
  have e : D - y - off' = C - (y - off) := by rw [hoff]; abel
  refine ⟨?_, ?_⟩
  · rw [mem_placed_iff]; simp only [stdPiece]; rw [e]; exact h1
  · simp only [pieceVal, stdPiece]
    rw [e]
    have ha1 := congrArg Prod.fst haff
    have ha2 := congrArg Prod.snd haff
    simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at ha1 ha2
    simp only [dotS, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h2 ⊢
    linear_combination h2 - 2 * (y.1 * ha1 + y.2 * ha2)

end FLatticePaper.Tiles.AltGlueHalfTurn
