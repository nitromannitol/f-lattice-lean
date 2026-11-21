import FLatticePaper.Tiles.ZeroOneConditions
import FLatticePaper.Tiles.ZeroOneSlopes

/-! The slope relation of consecutive odometers of a zero-one family, for every word (task 16). -/

namespace FLatticePaper.Tiles
open Finset

theorem tile_unitSquares_ne : ∀ a ∈ [Letter.p, Letter.q], unitSquares (tileSites a) ≠ [] := by
  decide +kernel

theorem odo_eq_fun (o : Orientation) (rev : Bool) (ℓ : ℕ → Letter) (n k : ℕ) :
    (familyF o rev ℓ n).odo k = fun x => baseOdometer (ℓ k) (x - posF o rev ℓ k) + dotS (aF o ℓ k) x + bF o rev ℓ k := by
  funext x
  simp only [ZOFamily.odo, familyF, dotS]
  ring

theorem dom_eq_map (o : Orientation) (rev : Bool) (ℓ : ℕ → Letter) (n k : ℕ) :
    (familyF o rev ℓ n).dom k = (tileSites (ℓ k)).map (· + posF o rev ℓ k) := rfl

theorem slopeOf_odo (o : Orientation) (rev : Bool) (ℓ : ℕ → Letter) (n k : ℕ) :
    slopeOf ((familyF o rev ℓ n).odo k) ((familyF o rev ℓ n).dom k) =
      slopeOf (baseOdometer (ℓ k)) (tileSites (ℓ k)) + (((aF o ℓ k).1 : ℚ), ((aF o ℓ k).2 : ℚ)) := by
  rw [odo_eq_fun, dom_eq_map]
  have hne : unitSquares ((tileSites (ℓ k)).map (· + posF o rev ℓ k)) ≠ [] := by
    rw [unitSquares_map_add]
    intro h
    exact tile_unitSquares_ne (ℓ k) (letter_mem _) (List.map_eq_nil_iff.mp h)
  rw [slopeOf_affine _ _ _ _ hne, slopeOf_translate]

/-- The slope relation of consecutive odometers: `s(o_{k+1}) − s(o_k) = slopeDiff`. -/
theorem respects_slope (o : Orientation) (rev : Bool) (ℓ : ℕ → Letter) (n k : ℕ) :
    slopeOf ((familyF o rev ℓ n).odo (k + 1)) ((familyF o rev ℓ n).dom (k + 1)) -
        slopeOf ((familyF o rev ℓ n).odo k) ((familyF o rev ℓ n).dom k) =
      slopeDiff o (ℓ k) (ℓ (k + 1)) := by
  rw [slopeOf_odo, slopeOf_odo, slope_delta_consistent o (orientation_mem o) (ℓ k) (letter_mem _)
    (ℓ (k + 1)) (letter_mem _)]
  have ha : aF o ℓ (k + 1) = aF o ℓ k + deltaOf o (ℓ k) (ℓ (k + 1)) := rfl
  rw [ha]
  ext
  · simp only [Prod.fst_add, Prod.fst_sub]
    push_cast
    ring
  · simp only [Prod.snd_add, Prod.snd_sub]
    push_cast
    ring

end FLatticePaper.Tiles
