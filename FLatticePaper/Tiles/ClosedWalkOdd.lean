import FLatticePaper.Tiles.ClosedWalkVertical
import FLatticePaper.Tiles.ClosedWalkHorizontal
import FLatticePaper.Tiles.CommonExtensionFamily
import FLatticePaper.Tiles.CommonExtensionStandard
import FLatticePaper.Tiles.CommonExtensionWitness
import FLatticePaper.Tiles.PointNonNeighbour

/-! The closed-walk theorem for the odd standard tile: the constancy `κ` at every lattice step is assembled from the
vertical constancy (at `(1,0)`), the horizontal constancy (at `(0,-1)`), the algebraic relations of the two opposite steps,
and the vacuity of the non-unit steps (`unit_of_contact`). The covering hypotheses are the open H2 input. -/

namespace FLatticePaper.Tiles

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles.StandardClause
  FLatticePaper.Tiles.StandardBoundary FLatticePaper.Tiles.SiteStrings FLatticePaper.Tiles.CommonExtFamily
  FLatticePaper.Tiles.CommonExtStandard FLatticePaper.Tiles.PointNonNeighbour FLatticePaper.Tiles.Standard
  FLatticePaper.Tiles.CommonExtWitness FLatticePaper.Tiles.CellDerivation

/-- The constants of the odd tile on the lattice steps: `κ(1,0) = κv`, `κ(-1,0) = -κv`, `κ(0,1) = -κh - a2·v2`,
`κ(0,-1) = κh`, and `0` otherwise (the zero step and the non-unit steps). -/
def oddKappa (κv κh num den : ℤ) : ℤ × ℤ → ℤ := fun d =>
  if d = (1, 0) then κv else if d = (-1, 0) then -κv else
    if d = (0, 1) then -κh - (num * (num - den) - den * (num + den)) else
      if d = (0, -1) then κh else 0

theorem closed_walks_odd (S : FLatticePaper.Tiles.SurgicalWeak.WeakData)
    (oddO evenO : FLatticePaper.Farey.Word → PartialOdometer)
    (h : FLatticePaper.Tiles.SurgicalWeak.IsWeakStdFamily S oddO evenO) (w : FLatticePaper.Farey.Word)
    (H2X_v : ∀ z, BoundaryVertex (↑(cellTileOf (oddTile w)) : Set GInt) z →
      tileCovers (vStringAt (vWordOf w false) (lastPosOf (hStringAt (hWordOf w false) 0))) z)
    (H2Y_v : ∀ z, BoundaryVertex ({t : GInt | t - texV1Odd (fracOdd w) ∈ cellTileOf (oddTile w)} : Set GInt) z →
      tileCovers (vRevStringAt (vWordOf w false).reverse (texV1Odd (fracOdd w))) z)
    (H2X_h : ∀ z, BoundaryVertex (↑(cellTileOf (oddTile w)) : Set GInt) z →
      tileCovers (hStringAt (hWordOf w false) 0) z)
    (H2Y_h : ∀ z, BoundaryVertex ({t : GInt | t - (-texV2 (fracOdd w)) ∈ cellTileOf (oddTile w)} : Set GInt) z →
      tileCovers (hRevStringAt (hWordOf w false).reverse (1, -2)) z) :
    ∃ κ : ℤ × ℤ → ℤ, ∀ (u : ℤ × ℤ)
      (wk : (overlapGraph (dom (↑(oddTile w) : Set (ℤ × ℤ)) (texV1Odd (fracOdd w)) (texV2 (fracOdd w)))).Walk u u),
      walkSum (offFam κ (texV1Odd (fracOdd w)) (texV2 (fracOdd w)) (0, 0)
        ((fracOdd w).num, -(fracOdd w).den)) wk = 0 := by
  obtain ⟨κv, hv⟩ := vertical_kappa S oddO evenO h w H2X_v H2Y_v
  obtain ⟨κh, hh⟩ := horizontal_kappa S oddO evenO h w H2X_h H2Y_h
  have hκ : ∀ (d' : ℤ × ℤ) (y : ℤ × ℤ), y ∈ (↑(oddTile w) : Set (ℤ × ℤ)) →
      y - vP (texV1Odd (fracOdd w)) (texV2 (fracOdd w)) d' ∈ (↑(oddTile w) : Set (ℤ × ℤ)) →
      (oddO w).val y - ((oddO w).val (y - vP (texV1Odd (fracOdd w)) (texV2 (fracOdd w)) d') +
        dotZ (aP (0, 0) ((fracOdd w).num, -(fracOdd w).den) d') y) =
        oddKappa κv κh (fracOdd w).num (fracOdd w).den d' := by
    intro d' y hy hyd
    rcases d' with ⟨d1, d2⟩
    by_cases h0 : (d1, d2) = (0, 0)
    · simp only [Prod.mk.injEq] at h0
      obtain ⟨rfl, rfl⟩ := h0
      have h00 : y - ((0 : ℤ), (0 : ℤ)) = y := by ext <;> simp
      simp [vP, aP, dotZ, oddKappa, h00]
    · obtain ⟨hd1, hd2, hd3, hd4⟩ := oddTile_diagonal_disjoint w
      have hc := unit_of_contact (P := oddTile w) (v1 := texV1Odd (fracOdd w)) (v2 := texV2 (fracOdd w))
        (fun k k' hns z hz => oddTile_nonneighbour w k k' hns z hz)
        (fun z hz => ⟨hd1 z hz, hd2 z hz, hd3 z hz, hd4 z hz⟩) h0 (Finset.mem_coe.1 hy)
        (Finset.mem_coe.1 hyd)
      rcases hc with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩
      · simp only at e1 e2
        obtain ⟨rfl, rfl⟩ : d1 = 1 ∧ d2 = 0 := ⟨e1, e2⟩
        have e := hv y hy (by simpa [vP] using hyd)
        simp only [vP, aP, dotZ, oddKappa]
        simp
        linarith
      · simp only at e1 e2
        obtain ⟨rfl, rfl⟩ : d1 = -1 ∧ d2 = 0 := ⟨e1, e2⟩
        have hvn : vP (texV1Odd (fracOdd w)) (texV2 (fracOdd w)) (-1, 0) = -texV1Odd (fracOdd w) := by
          ext <;> simp [vP]
        have haP : aP (0, 0) ((fracOdd w).num, -(fracOdd w).den) (-1, 0) = (0, 0) := by
          ext <;> simp [aP]
        rw [hvn] at hyd ⊢
        rw [haP]
        have e := hv (y - -texV1Odd (fracOdd w)) hyd
          (by rw [sub_neg_eq_add, add_sub_cancel_right]; exact hy)
        rw [sub_neg_eq_add, add_sub_cancel_right] at e
        have hk : oddKappa κv κh (fracOdd w).num (fracOdd w).den (-1, 0) = -κv := by
          simp [oddKappa]
        rw [hk]
        simp only [dotZ, zero_mul, add_zero, sub_neg_eq_add]
        linarith
      · simp only at e1 e2
        obtain ⟨rfl, rfl⟩ : d1 = 0 ∧ d2 = 1 := ⟨e1, e2⟩
        have hvP : vP (texV1Odd (fracOdd w)) (texV2 (fracOdd w)) (0, 1) = texV2 (fracOdd w) := by
          ext <;> simp [vP]
        rw [hvP] at hyd
        have hzy : y - texV2 (fracOdd w) - -texV2 (fracOdd w) = y := by
          simp
        have e := hh (y - texV2 (fracOdd w)) (by simpa using hyd) (by rw [hzy]; exact hy)
        rw [hzy] at e
        simp only [vP, aP, dotZ, oddKappa, texV2, Prod.fst_sub, Prod.snd_sub] at e ⊢
        simp
        linear_combination (-1 : ℤ) * e
      · simp only at e1 e2
        obtain ⟨rfl, rfl⟩ : d1 = 0 ∧ d2 = -1 := ⟨e1, e2⟩
        have hvP : vP (texV1Odd (fracOdd w)) (texV2 (fracOdd w)) (0, -1) = -texV2 (fracOdd w) := by
          ext <;> simp [vP]
        have haP : aP (0, 0) ((fracOdd w).num, -(fracOdd w).den) (0, -1) =
            (-(fracOdd w).num, (fracOdd w).den) := by
          ext <;> simp [aP]
        rw [hvP] at hyd ⊢
        rw [haP]
        have hk : oddKappa κv κh (fracOdd w).num (fracOdd w).den (0, -1) = κh := by
          simp [oddKappa]
        rw [hk]
        have e := hh y hy hyd
        simp only [dotZ]
        linear_combination e
  refine ⟨oddKappa κv κh (fracOdd w).num (fracOdd w).den, fun u wk => ?_⟩
  refine family_closed_walks_zero_paper (↑(oddTile w) : Set (ℤ × ℤ)) (oddO w).val (fracOdd w).num
    (fracOdd w).den (texV1Odd (fracOdd w)) (texV2 (fracOdd w)) (0, 0) ((fracOdd w).num, -(fracOdd w).den)
    (oddKappa κv κh (fracOdd w).num (fracOdd w).den) hκ (oddTile_hA1h w) (oddTile_hA1v w) (oddTile_hA2 w)
    rfl rfl (Or.inr rfl) u wk

end FLatticePaper.Tiles
