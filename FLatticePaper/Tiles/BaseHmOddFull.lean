import FLatticePaper.Tiles.BaseHmOddRespects
import FLatticePaper.Tiles.BaseHmOddLast
import FLatticePaper.Tiles.BaseHmOddClass3

/-! # The reversed horizontal clause of the odd odometer of `3^k` (`k ≥ 1`)

`HmOddF_odo_eq`: on each tile of the explicit family the paper odometer equals the family's odometer (the four classes of the
per-tile identities). `respects_hm_odd`: the reversed horizontal string of the odd `3^k` word, anchored at `posHm k 0`, is respected by
the paper odometer `paperLadderValue (2k+2)`. -/

namespace FLatticePaper.Tiles.BaseHmOddFull

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.BaseHmOdd FLatticePaper.Construction
open FLatticePaper.Tiles.BaseHmOddValues FLatticePaper.Tiles.BaseHmOddClass1 FLatticePaper.Tiles.BaseHmOddClass2
open FLatticePaper.Tiles.BaseHmOddClass3 FLatticePaper.Tiles.BaseHmOddLast FLatticePaper.Tiles.BaseHmOddRespects
open FLatticePaper.Tiles.BaseHmOddLast FLatticePaper.Tiles.BaseTileProps
open FLatticePaper.Tiles.BaseHpLadder (wL wL_length)

theorem HmOddF_key (k : ℕ) (hk : 1 ≤ k) (j : ℕ) (hj : j < 2 * k + 3) (u : GInt)
    (hu : u ∈ tileShape (hTileAt (lettersOf (wL k) true) j)) :
    paperLadderValue (2 * (k : ℤ) + 2) (u + posHm k j) =
      zTileOdo (hTileAt (lettersOf (wL k) true) j) u + ptDot (aHm k j) u + cHm k j := by
  rw [tile_type_rev_wL k j hk hj] at hu ⊢
  by_cases hA : j ≤ k
  · rw [if_neg (show ¬ (j = k + 1 ∨ j = 2 * k + 2) by omega)] at hu ⊢
    have hP : posHm k j = ((2 * (j : ℤ) - 2 * (k : ℤ)), 2 * (k : ℤ) + 1) := by
      unfold posHm; rw [if_pos hA]
    rw [hP]
    exact val_zero_mid k j hk hA u hu
  · by_cases hB : j = k + 1
    · rw [if_pos (Or.inl hB)] at hu ⊢
      have hP : posHm k j = (2, 2 * (k : ℤ) + 2) := by
        unfold posHm; rw [if_neg hA, if_pos hB]
      rw [hP]
      subst hB
      exact val_one_mid k hk u hu
    · by_cases hC : j = 2 * k + 2
      · rw [if_pos (Or.inr hC)] at hu ⊢
        have hP : posHm k j = (2 * (k : ℤ) + 3, 2 * (k : ℤ) + 3) := by
          unfold posHm; rw [if_neg hA, if_neg hB, if_neg (show ¬ j ≤ 2 * k + 1 by omega)]
        rw [hP]
        subst hC
        exact val_one_last k hk u hu
      · rw [if_neg (show ¬ (j = k + 1 ∨ j = 2 * k + 2) by omega)] at hu ⊢
        have hP : posHm k j = (2 * (j : ℤ) - 2 * (k : ℤ) - 1, 2 * (k : ℤ) + 2) := by
          unfold posHm; rw [if_neg hA, if_neg hB, if_pos (show j ≤ 2 * k + 1 by omega)]
        rw [hP]
        exact val_zero_tail k j (by omega) (by omega) u hu

theorem HmOddF_odo_eq (k : ℕ) (hk : 1 ≤ k) (j : ℕ) (hj : j < 2 * k + 3) (x : GInt)
    (hx : x ∈ (HmOddF k).dom j) :
    paperLadderValue (2 * (k : ℤ) + 2) x = (HmOddF k).odo j x := by
  have hdom := hx
  unfold PTFamily.dom at hdom
  rw [HmOddF_tile k j hj] at hdom
  simp only [List.mem_map] at hdom
  obtain ⟨u, hu, rfl⟩ := hdom
  have key := HmOddF_key k hk j hj u hu
  unfold PTFamily.odo
  rw [HmOddF_tile k j hj]
  show paperLadderValue (2 * (k : ℤ) + 2) (u + posHm k j) =
    zTileOdo (hTileAt (lettersOf (wL k) true) j) (u + posHm k j - posHm k j) +
      (aHm k j).1 * (u + posHm k j).1 + (aHm k j).2 * (u + posHm k j).2 +
      (cHm k j - ptDot (aHm k j) (posHm k j))
  rw [key, add_sub_cancel_right]
  unfold ptDot
  simp only [Prod.fst_add, Prod.snd_add]
  ring

theorem respects_hm_odd (k : ℕ) (hk : 1 ≤ k) :
    RespectsTiles .horizontal true (hRevStringAt (wL k).reverse (posHm k 0))
      (fun x => paperLadderValue (2 * (k : ℤ) + 2) x) := by
  have hl : lettersOf (wL k) true = lettersOf (wL k).reverse false := rfl
  have hts : (HmOddF k).ts = hRevStringAt (wL k).reverse (posHm k 0) := by
    rw [hRevStringAt_eq_map (wL k).reverse (posHm k 0) (posHm k) rfl (fun j hj => by
      rw [List.length_reverse, wL_length] at hj
      exact posHm_succ k j hk (by omega))]
    unfold HmOddF
    rw [hl, List.length_reverse, wL_length]
  exact ⟨HmOddF k, hts, fun j hj x hx => HmOddF_odo_eq k hk j (by rw [HmOddF_n] at hj; exact hj) x hx,
    HmOddF_respects k hk⟩

end FLatticePaper.Tiles.BaseHmOddFull
