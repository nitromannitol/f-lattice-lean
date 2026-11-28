import FLatticePaper.Tiles.AltItem4H
import FLatticePaper.Tiles.AltItem4PairsEvenFalse
import FLatticePaper.Tiles.AltItem4PairsEvenTrue

/-! # Item (4) of `lemma:alternate_tile_properties`, the even alternate child, the directions `k v₁ + v₂`

For `v = k v₁ + v₂`, `k ∈ {-1, 0, 1}`, every point `x` of `T̂(q₀) ∩ (T̂(q₀) + v)` satisfies the conclusion of item (4): `x` lies
in two copies of the decomposition, one of `T̂(q₀)` and one of `T̂(q₀) + v`, and the pair lemmas (`AltItem4PairsEven*`) apply;
the alternate parent piece takes no part, since `H + v` misses `T̂(q₀)` and `H` misses `T̂(q₀) + v` (`AltItem4H`). -/

namespace FLatticePaper.Tiles.AltItem4

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open FLatticePaper.Tiles.Standard (Tile shift mem_shift stateAt IsBase oddTile evenTile oddChildB evenChildB)
open FLatticePaper.Tiles.SurgicalAltTiles (altOddTile altEvenTile altRegs)
open FLatticePaper.Tiles.AltPieces

/-- **Item (4), even alternate child, `v = k v₁ + v₂`.** -/
theorem item4_even_up {w : Word} (hw : ¬ IsBase w) (k1 : ℤ) (hk : k1 = -1 ∨ k1 = 0 ∨ k1 = 1) (x : Site)
    (h1 : x ∈ altEvenTile AltRotStep.B w) (h2 : x - latV w true k1 1 ∈ altEvenTile AltRotStep.B w) :
    Concl (evenCopies w) (latV w true k1 1) x := by
  obtain ⟨u, y, rfl⟩ := exists_snoc_of_not_base hw
  obtain ⟨y', hy', he⟩ := altEvenTile_eq AltRotStep.B hw
  rw [AltRotStep.altTypeOf_snoc] at hy'
  obtain rfl := Option.some.inj hy'
  have hH3 : ∀ z, y = Digit.three → z ∉ AltRotStep.altP1Part (phase (u ++ [y]) == 1) y
      (altRegs AltRotStep.B (u ++ [y])).1 (parentsAt (u ++ [y])).odd (parentsAt (u ++ [y])).even := by
    rintro z rfl hz
    rcases AltBounds.phase_cases (u ++ [Digit.three]) with ⟨ho, -⟩ | ⟨ho, -⟩ <;> rw [ho] at hz <;>
      simp [AltRotStep.altP1Part, SurgicalAlt.altP1Coeff] at hz
  have h1' := h1
  have h2' := h2
  rw [he, Finset.mem_union] at h1' h2'
  rcases h2' with h2s | h2H
  swap
  · by_cases hy3 : y = Digit.three
    · exact absurd h2H (hH3 _ hy3)
    · exact (parent_even_sep u y hy3 hw k1 x h1 h2H).elim
  rcases h1' with h1s | h1H
  swap
  · by_cases hy3 : y = Digit.three
    · exact absurd h1H (hH3 _ hy3)
    · exact (parent_even_sep' u y hy3 hw k1 x h1H h2).elim
  rw [mem_evenStd_iff] at h1s h2s
  rcases AltBounds.phase_cases (u ++ [y]) with ⟨ho, -⟩ | ⟨ho, -⟩ <;> rw [ho] at h1s h2s
  · -- `W₁` odd
    rcases hk with rfl | rfl | rfl
    · rcases h1s with ⟨a, ha, hJ⟩ | ⟨a, ha, hJ⟩ <;> rcases h2s with ⟨b, hb, hK⟩ | ⟨b, hb, hK⟩ <;>
        simp only [evenPOffs, evenQOffs, List.mem_cons, List.not_mem_nil, or_false] at ha hb
      · rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact pair_even_true_m11_00 hw ho x hJ hK
        · exact pair_even_true_m11_01 hw ho x hJ hK
        · exact pair_even_true_m11_10 hw ho x hJ hK
        · exact pair_even_true_m11_11 hw ho x hJ hK
      · rcases ha with rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl
        · exact pair_even_true_m11_02 hw ho x hJ hK
        · exact pair_even_true_m11_03 hw ho x hJ hK
        · exact pair_even_true_m11_04 hw ho x hJ hK
        · exact pair_even_true_m11_05 hw ho x hJ hK
        · exact pair_even_true_m11_12 hw ho x hJ hK
        · exact pair_even_true_m11_13 hw ho x hJ hK
        · exact pair_even_true_m11_14 hw ho x hJ hK
        · exact pair_even_true_m11_15 hw ho x hJ hK
      · rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl
        · exact pair_even_true_m11_20 hw ho x hJ hK
        · exact pair_even_true_m11_21 hw ho x hJ hK
        · exact pair_even_true_m11_30 hw ho x hJ hK
        · exact pair_even_true_m11_31 hw ho x hJ hK
        · exact pair_even_true_m11_40 hw ho x hJ hK
        · exact pair_even_true_m11_41 hw ho x hJ hK
        · exact pair_even_true_m11_50 hw ho x hJ hK
        · exact pair_even_true_m11_51 hw ho x hJ hK
      · rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl
        · exact pair_even_true_m11_22 hw ho x hJ hK
        · exact pair_even_true_m11_23 hw ho x hJ hK
        · exact pair_even_true_m11_24 hw ho x hJ hK
        · exact pair_even_true_m11_25 hw ho x hJ hK
        · exact pair_even_true_m11_32 hw ho x hJ hK
        · exact pair_even_true_m11_33 hw ho x hJ hK
        · exact pair_even_true_m11_34 hw ho x hJ hK
        · exact pair_even_true_m11_35 hw ho x hJ hK
        · exact pair_even_true_m11_42 hw ho x hJ hK
        · exact pair_even_true_m11_43 hw ho x hJ hK
        · exact pair_even_true_m11_44 hw ho x hJ hK
        · exact pair_even_true_m11_45 hw ho x hJ hK
        · exact pair_even_true_m11_52 hw ho x hJ hK
        · exact pair_even_true_m11_53 hw ho x hJ hK
        · exact pair_even_true_m11_54 hw ho x hJ hK
        · exact pair_even_true_m11_55 hw ho x hJ hK
    · rcases h1s with ⟨a, ha, hJ⟩ | ⟨a, ha, hJ⟩ <;> rcases h2s with ⟨b, hb, hK⟩ | ⟨b, hb, hK⟩ <;>
        simp only [evenPOffs, evenQOffs, List.mem_cons, List.not_mem_nil, or_false] at ha hb
      · rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact pair_even_true_01_00 hw ho x hJ hK
        · exact pair_even_true_01_01 hw ho x hJ hK
        · exact pair_even_true_01_10 hw ho x hJ hK
        · exact pair_even_true_01_11 hw ho x hJ hK
      · rcases ha with rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl
        · exact pair_even_true_01_02 hw ho x hJ hK
        · exact pair_even_true_01_03 hw ho x hJ hK
        · exact pair_even_true_01_04 hw ho x hJ hK
        · exact pair_even_true_01_05 hw ho x hJ hK
        · exact pair_even_true_01_12 hw ho x hJ hK
        · exact pair_even_true_01_13 hw ho x hJ hK
        · exact pair_even_true_01_14 hw ho x hJ hK
        · exact pair_even_true_01_15 hw ho x hJ hK
      · rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl
        · exact pair_even_true_01_20 hw ho x hJ hK
        · exact pair_even_true_01_21 hw ho x hJ hK
        · exact pair_even_true_01_30 hw ho x hJ hK
        · exact pair_even_true_01_31 hw ho x hJ hK
        · exact pair_even_true_01_40 hw ho x hJ hK
        · exact pair_even_true_01_41 hw ho x hJ hK
        · exact pair_even_true_01_50 hw ho x hJ hK
        · exact pair_even_true_01_51 hw ho x hJ hK
      · rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl
        · exact pair_even_true_01_22 hw ho x hJ hK
        · exact pair_even_true_01_23 hw ho x hJ hK
        · exact pair_even_true_01_24 hw ho x hJ hK
        · exact pair_even_true_01_25 hw ho x hJ hK
        · exact pair_even_true_01_32 hw ho x hJ hK
        · exact pair_even_true_01_33 hw ho x hJ hK
        · exact pair_even_true_01_34 hw ho x hJ hK
        · exact pair_even_true_01_35 hw ho x hJ hK
        · exact pair_even_true_01_42 hw ho x hJ hK
        · exact pair_even_true_01_43 hw ho x hJ hK
        · exact pair_even_true_01_44 hw ho x hJ hK
        · exact pair_even_true_01_45 hw ho x hJ hK
        · exact pair_even_true_01_52 hw ho x hJ hK
        · exact pair_even_true_01_53 hw ho x hJ hK
        · exact pair_even_true_01_54 hw ho x hJ hK
        · exact pair_even_true_01_55 hw ho x hJ hK
    · rcases h1s with ⟨a, ha, hJ⟩ | ⟨a, ha, hJ⟩ <;> rcases h2s with ⟨b, hb, hK⟩ | ⟨b, hb, hK⟩ <;>
        simp only [evenPOffs, evenQOffs, List.mem_cons, List.not_mem_nil, or_false] at ha hb
      · rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact pair_even_true_11_00 hw ho x hJ hK
        · exact pair_even_true_11_01 hw ho x hJ hK
        · exact pair_even_true_11_10 hw ho x hJ hK
        · exact pair_even_true_11_11 hw ho x hJ hK
      · rcases ha with rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl
        · exact pair_even_true_11_02 hw ho x hJ hK
        · exact pair_even_true_11_03 hw ho x hJ hK
        · exact pair_even_true_11_04 hw ho x hJ hK
        · exact pair_even_true_11_05 hw ho x hJ hK
        · exact pair_even_true_11_12 hw ho x hJ hK
        · exact pair_even_true_11_13 hw ho x hJ hK
        · exact pair_even_true_11_14 hw ho x hJ hK
        · exact pair_even_true_11_15 hw ho x hJ hK
      · rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl
        · exact pair_even_true_11_20 hw ho x hJ hK
        · exact pair_even_true_11_21 hw ho x hJ hK
        · exact pair_even_true_11_30 hw ho x hJ hK
        · exact pair_even_true_11_31 hw ho x hJ hK
        · exact pair_even_true_11_40 hw ho x hJ hK
        · exact pair_even_true_11_41 hw ho x hJ hK
        · exact pair_even_true_11_50 hw ho x hJ hK
        · exact pair_even_true_11_51 hw ho x hJ hK
      · rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl
        · exact pair_even_true_11_22 hw ho x hJ hK
        · exact pair_even_true_11_23 hw ho x hJ hK
        · exact pair_even_true_11_24 hw ho x hJ hK
        · exact pair_even_true_11_25 hw ho x hJ hK
        · exact pair_even_true_11_32 hw ho x hJ hK
        · exact pair_even_true_11_33 hw ho x hJ hK
        · exact pair_even_true_11_34 hw ho x hJ hK
        · exact pair_even_true_11_35 hw ho x hJ hK
        · exact pair_even_true_11_42 hw ho x hJ hK
        · exact pair_even_true_11_43 hw ho x hJ hK
        · exact pair_even_true_11_44 hw ho x hJ hK
        · exact pair_even_true_11_45 hw ho x hJ hK
        · exact pair_even_true_11_52 hw ho x hJ hK
        · exact pair_even_true_11_53 hw ho x hJ hK
        · exact pair_even_true_11_54 hw ho x hJ hK
        · exact pair_even_true_11_55 hw ho x hJ hK
  · -- `W₁` even
    rcases hk with rfl | rfl | rfl
    · rcases h1s with ⟨a, ha, hJ⟩ | ⟨a, ha, hJ⟩ <;> rcases h2s with ⟨b, hb, hK⟩ | ⟨b, hb, hK⟩ <;>
        simp only [evenPOffs, evenQOffs, List.mem_cons, List.not_mem_nil, or_false] at ha hb
      · rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact pair_even_false_m11_00 hw ho x hJ hK
        · exact pair_even_false_m11_01 hw ho x hJ hK
        · exact pair_even_false_m11_10 hw ho x hJ hK
        · exact pair_even_false_m11_11 hw ho x hJ hK
      · rcases ha with rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl
        · exact pair_even_false_m11_02 hw ho x hJ hK
        · exact pair_even_false_m11_03 hw ho x hJ hK
        · exact pair_even_false_m11_04 hw ho x hJ hK
        · exact pair_even_false_m11_05 hw ho x hJ hK
        · exact pair_even_false_m11_12 hw ho x hJ hK
        · exact pair_even_false_m11_13 hw ho x hJ hK
        · exact pair_even_false_m11_14 hw ho x hJ hK
        · exact pair_even_false_m11_15 hw ho x hJ hK
      · rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl
        · exact pair_even_false_m11_20 hw ho x hJ hK
        · exact pair_even_false_m11_21 hw ho x hJ hK
        · exact pair_even_false_m11_30 hw ho x hJ hK
        · exact pair_even_false_m11_31 hw ho x hJ hK
        · exact pair_even_false_m11_40 hw ho x hJ hK
        · exact pair_even_false_m11_41 hw ho x hJ hK
        · exact pair_even_false_m11_50 hw ho x hJ hK
        · exact pair_even_false_m11_51 hw ho x hJ hK
      · rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl
        · exact pair_even_false_m11_22 hw ho x hJ hK
        · exact pair_even_false_m11_23 hw ho x hJ hK
        · exact pair_even_false_m11_24 hw ho x hJ hK
        · exact pair_even_false_m11_25 hw ho x hJ hK
        · exact pair_even_false_m11_32 hw ho x hJ hK
        · exact pair_even_false_m11_33 hw ho x hJ hK
        · exact pair_even_false_m11_34 hw ho x hJ hK
        · exact pair_even_false_m11_35 hw ho x hJ hK
        · exact pair_even_false_m11_42 hw ho x hJ hK
        · exact pair_even_false_m11_43 hw ho x hJ hK
        · exact pair_even_false_m11_44 hw ho x hJ hK
        · exact pair_even_false_m11_45 hw ho x hJ hK
        · exact pair_even_false_m11_52 hw ho x hJ hK
        · exact pair_even_false_m11_53 hw ho x hJ hK
        · exact pair_even_false_m11_54 hw ho x hJ hK
        · exact pair_even_false_m11_55 hw ho x hJ hK
    · rcases h1s with ⟨a, ha, hJ⟩ | ⟨a, ha, hJ⟩ <;> rcases h2s with ⟨b, hb, hK⟩ | ⟨b, hb, hK⟩ <;>
        simp only [evenPOffs, evenQOffs, List.mem_cons, List.not_mem_nil, or_false] at ha hb
      · rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact pair_even_false_01_00 hw ho x hJ hK
        · exact pair_even_false_01_01 hw ho x hJ hK
        · exact pair_even_false_01_10 hw ho x hJ hK
        · exact pair_even_false_01_11 hw ho x hJ hK
      · rcases ha with rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl
        · exact pair_even_false_01_02 hw ho x hJ hK
        · exact pair_even_false_01_03 hw ho x hJ hK
        · exact pair_even_false_01_04 hw ho x hJ hK
        · exact pair_even_false_01_05 hw ho x hJ hK
        · exact pair_even_false_01_12 hw ho x hJ hK
        · exact pair_even_false_01_13 hw ho x hJ hK
        · exact pair_even_false_01_14 hw ho x hJ hK
        · exact pair_even_false_01_15 hw ho x hJ hK
      · rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl
        · exact pair_even_false_01_20 hw ho x hJ hK
        · exact pair_even_false_01_21 hw ho x hJ hK
        · exact pair_even_false_01_30 hw ho x hJ hK
        · exact pair_even_false_01_31 hw ho x hJ hK
        · exact pair_even_false_01_40 hw ho x hJ hK
        · exact pair_even_false_01_41 hw ho x hJ hK
        · exact pair_even_false_01_50 hw ho x hJ hK
        · exact pair_even_false_01_51 hw ho x hJ hK
      · rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl
        · exact pair_even_false_01_22 hw ho x hJ hK
        · exact pair_even_false_01_23 hw ho x hJ hK
        · exact pair_even_false_01_24 hw ho x hJ hK
        · exact pair_even_false_01_25 hw ho x hJ hK
        · exact pair_even_false_01_32 hw ho x hJ hK
        · exact pair_even_false_01_33 hw ho x hJ hK
        · exact pair_even_false_01_34 hw ho x hJ hK
        · exact pair_even_false_01_35 hw ho x hJ hK
        · exact pair_even_false_01_42 hw ho x hJ hK
        · exact pair_even_false_01_43 hw ho x hJ hK
        · exact pair_even_false_01_44 hw ho x hJ hK
        · exact pair_even_false_01_45 hw ho x hJ hK
        · exact pair_even_false_01_52 hw ho x hJ hK
        · exact pair_even_false_01_53 hw ho x hJ hK
        · exact pair_even_false_01_54 hw ho x hJ hK
        · exact pair_even_false_01_55 hw ho x hJ hK
    · rcases h1s with ⟨a, ha, hJ⟩ | ⟨a, ha, hJ⟩ <;> rcases h2s with ⟨b, hb, hK⟩ | ⟨b, hb, hK⟩ <;>
        simp only [evenPOffs, evenQOffs, List.mem_cons, List.not_mem_nil, or_false] at ha hb
      · rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact pair_even_false_11_00 hw ho x hJ hK
        · exact pair_even_false_11_01 hw ho x hJ hK
        · exact pair_even_false_11_10 hw ho x hJ hK
        · exact pair_even_false_11_11 hw ho x hJ hK
      · rcases ha with rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl
        · exact pair_even_false_11_02 hw ho x hJ hK
        · exact pair_even_false_11_03 hw ho x hJ hK
        · exact pair_even_false_11_04 hw ho x hJ hK
        · exact pair_even_false_11_05 hw ho x hJ hK
        · exact pair_even_false_11_12 hw ho x hJ hK
        · exact pair_even_false_11_13 hw ho x hJ hK
        · exact pair_even_false_11_14 hw ho x hJ hK
        · exact pair_even_false_11_15 hw ho x hJ hK
      · rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl
        · exact pair_even_false_11_20 hw ho x hJ hK
        · exact pair_even_false_11_21 hw ho x hJ hK
        · exact pair_even_false_11_30 hw ho x hJ hK
        · exact pair_even_false_11_31 hw ho x hJ hK
        · exact pair_even_false_11_40 hw ho x hJ hK
        · exact pair_even_false_11_41 hw ho x hJ hK
        · exact pair_even_false_11_50 hw ho x hJ hK
        · exact pair_even_false_11_51 hw ho x hJ hK
      · rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl
        · exact pair_even_false_11_22 hw ho x hJ hK
        · exact pair_even_false_11_23 hw ho x hJ hK
        · exact pair_even_false_11_24 hw ho x hJ hK
        · exact pair_even_false_11_25 hw ho x hJ hK
        · exact pair_even_false_11_32 hw ho x hJ hK
        · exact pair_even_false_11_33 hw ho x hJ hK
        · exact pair_even_false_11_34 hw ho x hJ hK
        · exact pair_even_false_11_35 hw ho x hJ hK
        · exact pair_even_false_11_42 hw ho x hJ hK
        · exact pair_even_false_11_43 hw ho x hJ hK
        · exact pair_even_false_11_44 hw ho x hJ hK
        · exact pair_even_false_11_45 hw ho x hJ hK
        · exact pair_even_false_11_52 hw ho x hJ hK
        · exact pair_even_false_11_53 hw ho x hJ hK
        · exact pair_even_false_11_54 hw ho x hJ hK
        · exact pair_even_false_11_55 hw ho x hJ hK

end FLatticePaper.Tiles.AltItem4
