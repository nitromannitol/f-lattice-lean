import FLatticePaper.Tiles.BaseVertOdo
import FLatticePaper.Tiles.BaseVertPilot
import FLatticePaper.Tiles.BaseVertPiece
import FLatticePaper.Tiles.FirstSentenceSurgical
import FLatticePaper.Tiles.VerticalIdentities
import FLatticePaper.Tiles.VLinVertical
import FLatticePaper.Tiles.PseudoSquareSites

/-! # The reversed vertical base piece of the odd `3^k` word respects its string

For `k ≥ 1` the reversed vertical string of the odd child of `3^k`, anchored at `(0,0)`, is covered by the translated
reversed vertical family `piece w` of `w = p^(2k+1) q` (`BaseVertPiece.vWordOf_three_false`). Its tiles are the `one` tile at
`(0,0)` and the `zero` tiles at `(-(j-1), j)`, `1 ≤ j ≤ 2k+1`, and its odometers agree with the paper ladder value on each
domain by the per-tile identities `BaseVertPilot.ladder_one_point`, `BaseVertPilot.ladder_zero_point`. -/

namespace FLatticePaper.Tiles.BaseVertOdoFamily

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.BaseVertOdo
open FLatticePaper.Tiles.SiteStrings

/-- The reversed vertical family of `w`, translated by the stacking shift: its tiles are those of `vRevStringAt w.reverse (0,0)`. -/
def piece (w : BinaryWord) : PTFamily := (vtM w).translate verticalStackShift

theorem piece_ts_range (w : BinaryWord) :
    (piece w).ts = (List.range w.length).map
      (fun k => (letterZTile (lettersOf w true k), posF .vertical true (lettersOf w true) k)) := by
  simp only [piece, PTFamily.translate, vtM, zoReversedStackedV, List.map_map, Function.comp_def, sub_add_cancel]

theorem piece_ts (w : BinaryWord) : (piece w).ts = vRevStringAt w.reverse (0, 0) := by
  have h := zoReversedStackedV_eq w
  have e : ((1 : ℤ), (1 : ℤ)) + verticalStackShift = (0, 0) := by
    simp [verticalStackShift]
  simp only [piece, PTFamily.translate, vtM]
  rw [h, ← e, vRevStringAt_add]

theorem piece_n (w : BinaryWord) : (piece w).n = w.length := by
  simp [PTFamily.n, piece_ts_range]

theorem piece_tile (w : BinaryWord) (J : ℕ) (hJ : J < w.length) :
    (piece w).tile J = (letterZTile (lettersOf w true J), posF .vertical true (lettersOf w true) J) := by
  unfold PTFamily.tile
  rw [piece_ts_range]
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hJ]

theorem piece_a (w : BinaryWord) (J : ℕ) : (piece w).a J = vtAff (lettersOf w true) J := rfl

theorem piece_b (w : BinaryWord) (J : ℕ) :
    (piece w).b J = vtCM (lettersOf w true) J
      - ptDot (vtAff (lettersOf w true) J) (posF .vertical true (lettersOf w true) J) := by
  simp only [piece, PTFamily.translate, vtM, ptDot, verticalStackShift, Prod.fst_sub, Prod.snd_sub]
  ring

theorem piece_odo (w : BinaryWord) (J : ℕ) (hJ : J < w.length) (x : GInt) :
    (piece w).odo J x = zTileOdo (letterZTile (lettersOf w true J)) (x - posF .vertical true (lettersOf w true) J)
      + (vtAff (lettersOf w true) J).1 * x.1 + (vtAff (lettersOf w true) J).2 * x.2
      + (vtCM (lettersOf w true) J
        - ptDot (vtAff (lettersOf w true) J) (posF .vertical true (lettersOf w true) J)) := by
  unfold PTFamily.odo
  rw [piece_tile w J hJ, piece_a, piece_b]

/-- The `one` tile at `(0,0)`: the odometer of the family is `oneOdometer`. -/
theorem piece_odo_zero (m : ℕ) (x : GInt) :
    (piece (List.replicate m Letter.p ++ [Letter.q])).odo 0 x = oneOdometer x := by
  obtain ⟨h0, -⟩ := lettersOf_rev_lv m
  rw [piece_odo _ 0 (by simp) x, h0]
  simp [letterZTile, zTileOdo, vtAff, vtCnt, vtCM, posF, ptDot]

/-- The `zero` tile at `(-j, j+1)`, index `j+1`: the odometer is the zero odometer, plus the slope and the constant. -/
theorem piece_odo_succ (m j : ℕ) (hj : j + 1 < m + 1) (x : GInt) :
    (piece (List.replicate m Letter.p ++ [Letter.q])).odo (j + 1) x =
      zeroOdometer (x - (-(j : ℤ), (j : ℤ) + 1)) + (x.1 - ((j : ℤ) + 1) * x.2) +
        (vtCM (lettersOf (List.replicate m Letter.p ++ [Letter.q]) true) (j + 1) + (j : ℤ)
          + ((j : ℤ) + 1) * ((j : ℤ) + 1)) := by
  obtain ⟨h0, hs⟩ := lettersOf_rev_lv m
  have hlen : j + 1 < (List.replicate m Letter.p ++ [Letter.q]).length := by simp; omega
  rw [piece_odo _ (j + 1) hlen x]
  have hl : lettersOf (List.replicate m Letter.p ++ [Letter.q]) true (j + 1) = Letter.p := hs j
  have hc := vtCnt_succ_one _ h0 hs j
  have hA : vtAff (lettersOf (List.replicate m Letter.p ++ [Letter.q]) true) (j + 1)
      = (1, -((j : ℤ) + 1)) := by
    simp [vtAff, hc]
  rw [hl, hA, posF_vert_succ _ h0 hs j]
  simp only [letterZTile, zTileOdo, ptDot]
  ring

/-- The constant of the `zero` tile of index `j+1` of the odd `3^k` reversed piece. -/
theorem const_succ (k j : ℕ) :
    vtCM (lettersOf (List.replicate (2 * k + 1) Letter.p ++ [Letter.q]) true) (j + 1) + (j : ℤ)
        + ((j : ℤ) + 1) * ((j : ℤ) + 1)
      = ((j : ℤ) + 1) * ((j : ℤ) + 1 + 1) / 2 - 1 := by
  obtain ⟨h0, hs⟩ := lettersOf_rev_lv (2 * k + 1)
  have hV := vtCM_closed _ h0 hs j
  have hT := Int.two_mul_ediv_two_of_even (Int.even_mul_succ_self ((j : ℤ) + 1))
  linarith

/-- The `one` tile point identity. -/
theorem odo_one_pt (k : ℕ) (hk : 1 ≤ k) (y : GInt) (hy : y ∈ tileShape ZTile.one) :
    paperLadderValue (2 * (k : ℤ) + 2) y =
      (piece (List.replicate (2 * k + 1) Letter.p ++ [Letter.q])).odo 0 y := by
  have hk' : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  obtain ⟨a, b⟩ := y
  have hab : (a, b) = (0, 0) ∨ (a, b) = (0, 1) ∨ (a, b) = (1, 0) ∨ (a, b) = (1, 1) := by
    simpa [tileShape] using hy
  rw [piece_odo_zero]
  exact BaseVertPilot.ladder_one_point (k : ℤ) hk' a b hab

/-- The `zero` tile point identity of index `j+1`. -/
theorem odo_zero_pt (k : ℕ) (hk : 1 ≤ k) (j : ℕ) (hj : j + 1 < 2 * k + 2) (y : GInt)
    (hy : y ∈ tileShape ZTile.zero) :
    paperLadderValue (2 * (k : ℤ) + 2) (y + (-(j : ℤ), (j : ℤ) + 1)) =
      (piece (List.replicate (2 * k + 1) Letter.p ++ [Letter.q])).odo (j + 1)
        (y + (-(j : ℤ), (j : ℤ) + 1)) := by
  have hk' : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  obtain ⟨a, b⟩ := y
  have hab : (a, b) = (0, 0) ∨ (a, b) = (0, 1) ∨ (a, b) = (0, 2) ∨ (a, b) = (1, 0) ∨ (a, b) = (1, 1)
      ∨ (a, b) = (1, 2) := by
    simpa [tileShape] using hy
  have hL := BaseVertPilot.ladder_zero_point (k : ℤ) ((j : ℤ) + 1) hk' (by omega) (by omega) a b hab
  rw [piece_odo_succ (2 * k + 1) j (by omega)]
  have e1 : (a, b) + (-(j : ℤ), (j : ℤ) + 1) = (-((j : ℤ) + 1 - 1) + a, (j : ℤ) + 1 + b) :=
    Prod.ext (by simp only [Prod.fst_add]; ring) (by simp only [Prod.snd_add]; ring)
  have e2 : (-((j : ℤ) + 1 - 1) + a, (j : ℤ) + 1 + b) - (-(j : ℤ), (j : ℤ) + 1) = (a, b) :=
    Prod.ext (by simp only [Prod.fst_sub]; ring) (by simp only [Prod.snd_sub]; ring)
  rw [e1, e2, hL, const_succ k j]
  simp only [zeroOdometer]

/-- The reversed vertical base piece of the odd `3^k` word (`k ≥ 1`), anchored at `(0,0)`, respects its string with the paper
ladder value as its odometer. -/
theorem vm_odd_respects (k : ℕ) (hk : 1 ≤ k) :
    RespectsTiles .vertical true (vRevStringAt (vWordOf (List.replicate k Digit.three) false).reverse (0, 0))
      (paperLadderValue (2 * (k : ℤ) + 2)) := by
  rw [FLatticePaper.Tiles.BaseVertPiece.vWordOf_three_false]
  have hR : (piece (List.replicate (2 * k + 1) Letter.p ++ [Letter.q])).Respects .vertical true :=
    PTFamily.translate_respects _ _ _ _ (vtM_respects _)
  refine ⟨piece (List.replicate (2 * k + 1) Letter.p ++ [Letter.q]), piece_ts _, ?_, hR⟩
  intro J hJ x hx
  rcases J with _ | j
  · have hlen : 0 < (List.replicate (2 * k + 1) Letter.p ++ [Letter.q]).length := by simp
    obtain ⟨h0, hs⟩ := lettersOf_rev_lv (2 * k + 1)
    unfold PTFamily.dom at hx
    rw [piece_tile _ 0 hlen, h0] at hx
    have hone : letterZTile Letter.q = ZTile.one := rfl
    have hp0 : posF .vertical true (lettersOf (List.replicate (2 * k + 1) Letter.p ++ [Letter.q]) true) 0 = 0 := rfl
    rw [hone, hp0] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    simp only [add_zero]
    exact odo_one_pt k hk y hy
  · have hJ' : j + 1 < 2 * k + 2 := by
      have h := hJ
      rw [piece_n] at h
      simp at h
      omega
    have hlen : j + 1 < (List.replicate (2 * k + 1) Letter.p ++ [Letter.q]).length := by simp; omega
    obtain ⟨h0, hs⟩ := lettersOf_rev_lv (2 * k + 1)
    unfold PTFamily.dom at hx
    rw [piece_tile _ (j + 1) hlen, hs j, posF_vert_succ _ h0 hs j] at hx
    have hzp : letterZTile Letter.p = ZTile.zero := rfl
    rw [hzp] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact odo_zero_pt k hk j hJ' y hy

end FLatticePaper.Tiles.BaseVertOdoFamily
