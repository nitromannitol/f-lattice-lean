import FLatticePaper.Plane.Induction.TwosPieces
import FLatticePaper.Construction.NominalAgreement

namespace FLatticePaper.Induction
open Farey Construction

/-- On the closed polygon of `2^(k+1)`: `min(A, C) = V(z + (0,1))` (the tile, and the two boundary points). -/
theorem twos_closed_min (k : ℕ) (z : Site)
    (hz : z ∈ (frameAt (List.replicate (k + 1) Digit.two)).closedPolygon) :
    min ((frameAt (List.replicate (k + 1) Digit.two)).sheetA
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two)))) z)
      ((frameAt (List.replicate (k + 1) Digit.two)).sheetC
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two)))) z) =
      paperNearLadderValue (2 * (k : ℤ) + 4) (z.1, z.2 + 1) := by
  obtain ⟨z1, z2⟩ := z
  rcases closedPolygon_twos_tile k (z1, z2) hz with h | h | h
  · have := twos_tile_min k z1 (z2 + 1) h
    rwa [show z2 + 1 - 1 = z2 by ring] at this
  · simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨h1, h2⟩ := boundaryLeft_piece k (-1) (2 * (k : ℤ) + 5) rfl rfl
    rw [show 2 * (k : ℤ) + 5 - 1 = 2 * (k : ℤ) + 4 by ring] at h1 h2
    show min _ _ = paperNearLadderValue (2 * (k : ℤ) + 4) (-1, 2 * (k : ℤ) + 4 + 1)
    rw [show 2 * (k : ℤ) + 4 + 1 = 2 * (k : ℤ) + 5 by ring]
    exact min_tile_right _ _ _ 2 h1 h2 (by norm_num)
  · simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨h1, h2⟩ := boundaryRight_piece k (2 * (k : ℤ) + 5) (4 * (k : ℤ) + 7) rfl rfl
    rw [show 4 * (k : ℤ) + 7 - 1 = 4 * (k : ℤ) + 6 by ring] at h1 h2
    show min _ _ = paperNearLadderValue (2 * (k : ℤ) + 4) (2 * (k : ℤ) + 5, 4 * (k : ℤ) + 6 + 1)
    rw [show 4 * (k : ℤ) + 6 + 1 = 4 * (k : ℤ) + 7 by ring]
    exact min_tile_left _ _ _ 2 h1 h2 (by norm_num)

/-- The identification on the closed polygon of `2^(k+1)`: the standard field is the near-one value at `z + (0,1)`,
with constant `0`. The hypothesis `hper` (the sheet minimum respects the periods on `E`) is the input that
`standardField_eq_sheetMin` requires. -/
theorem twos_standardField_eq_on_E (k : ℕ)
    (hper : RespectsPeriodsOn (frameAt (List.replicate (k + 1) Digit.two)).child
      (frameAt (List.replicate (k + 1) Digit.two)).coherentConstantU
      (frameAt (List.replicate (k + 1) Digit.two)).coherentConstantV
      (frameAt (List.replicate (k + 1) Digit.two)).closedPolygon
      ((frameAt (List.replicate (k + 1) Digit.two)).sheetMin
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))))
    (z : Site) (hz : z ∈ (frameAt (List.replicate (k + 1) Digit.two)).closedPolygon) :
    standardField (List.replicate (k + 1) Digit.two) z =
      paperNearLadderValue (2 * (k : ℤ) + 4) (z.1, z.2 + 1) := by
  have hproper : ∃ x ∈ List.replicate (k + 1) Digit.two, x ≠ Digit.three :=
    ⟨Digit.two, by simp, by decide⟩
  rw [standardField_eq_sheetMin hproper hz hper]
  exact twos_closed_min k z hz

end FLatticePaper.Induction
