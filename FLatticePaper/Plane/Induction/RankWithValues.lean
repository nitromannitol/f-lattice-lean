import FLatticePaper.Plane.Induction.F2F3Pure
import FLatticePaper.Plane.Induction.ReflectedRank
import FLatticePaper.Plane.Induction.ReflectedFull
import FLatticePaper.Plane.Induction.ReflectedRankPlus
import FLatticePaper.Plane.Induction.ReflectedMinusFull

/-!
# The rank with increments `(-1, eta)` at every `3^k`, from the reciprocal values (task 118; the rank field)

The reflected deck ranks `R0plus` (`eta = 1`) and `R0minus` (`eta = -1`) are strict along every policy edge
(`R0plus_edge_full`, `R0minus_edge_full`) and have the characters `(-2d, 2(d+1))` and `(-2d, -2(d+1))` on the frame's
periods `kernel = (d, 1)` and `transverse = (1 - d, 1 + d)`. The hull lemma `rankWithIncrements_of_strict_hull`, with the
frame's price and rounded slip (`priceDrift_threes`, `slipDrift_threes`, and the monotone fields `V.price`, `V.slip` of the
reciprocal values), gives the rank with increments `(-1, eta)`. So `F2F3_threes_of_values` no longer needs `hrank` as a
hypothesis: `pureInputs_threes_of_values` takes only the reciprocal values.
-/

namespace FLatticePaper.EPolicy

open Farey FLatticePaper FLatticePaper.Induction
open FLatticePaper.Construction FLatticePaper.ReflectedRank FLatticePaper.ReflectedRankPlus
  FLatticePaper.ReflectedFull FLatticePaper.ReflectedMinusFull

/-- The rank with increments from a strict rank `R` with characters `cU, cV` on the frame's periods. -/
theorem rank_of_R (k : ℕ) (V : ReciprocalValues k) (η : ℤ) (hη : η = 1 ∨ η = -1) (R : Site → ℤ) (cU cV : ℤ)
    (hRU : ∀ z, R (z + (frameAt (List.replicate k Digit.three)).child.modifiedDeck.kernel) = R z + cU)
    (hRV : ∀ z, R (z + (frameAt (List.replicate k Digit.three)).child.modifiedDeck.transverse) = R z + cV)
    (hstrict : ∀ x i, ePolicy (2 * (k : ℤ) + 3) η (laplacian (reciprocalField k)) x i → R i < R x) :
    RankWithIncrements (ePolicy (2 * (k : ℤ) + 3) η (laplacian (reciprocalField k)))
      (frameAt (List.replicate k Digit.three)).child.modifiedDeck.kernel
      (frameAt (List.replicate k Digit.three)).child.modifiedDeck.transverse (-1) η := by
  have hPU : ∀ z : Site, (frameAt (List.replicate k Digit.three)).price (reciprocalField k)
      (z + (frameAt (List.replicate k Digit.three)).child.modifiedDeck.kernel) =
      (frameAt (List.replicate k Digit.three)).price (reciprocalField k) z - 1 := by
    intro z
    have h := (priceDrift_threes k z).1
    linarith
  have hPV : ∀ z : Site, (frameAt (List.replicate k Digit.three)).price (reciprocalField k)
      (z + (frameAt (List.replicate k Digit.three)).child.modifiedDeck.transverse) =
      (frameAt (List.replicate k Digit.three)).price (reciprocalField k) z := by
    intro z
    have h := (priceDrift_threes k z).2
    linarith
  have hJU : ∀ z : Site, (frameAt (List.replicate k Digit.three)).roundedSlip (reciprocalField k) η
      (z + (frameAt (List.replicate k Digit.three)).child.modifiedDeck.kernel) =
      (frameAt (List.replicate k Digit.three)).roundedSlip (reciprocalField k) η z := by
    intro z
    have h := (slipDrift_threes k η z).1
    unfold ChildFrame.roundedSlip
    congr 1
    linarith
  have hJV : ∀ z : Site, (frameAt (List.replicate k Digit.three)).roundedSlip (reciprocalField k) η
      (z + (frameAt (List.replicate k Digit.three)).child.modifiedDeck.transverse) =
      (frameAt (List.replicate k Digit.three)).roundedSlip (reciprocalField k) η z + η := by
    intro z
    have h := (slipDrift_threes k η z).2
    unfold ChildFrame.roundedSlip
    omega
  have hmono : ∀ x y, ePolicy (2 * (k : ℤ) + 3) η (laplacian (reciprocalField k)) x y →
      (frameAt (List.replicate k Digit.three)).price (reciprocalField k) y ≤
        (frameAt (List.replicate k Digit.three)).price (reciprocalField k) x ∧
      (frameAt (List.replicate k Digit.three)).roundedSlip (reciprocalField k) η y ≤
        (frameAt (List.replicate k Digit.three)).roundedSlip (reciprocalField k) η x := by
    intro x y h
    have hp := V.price η hη x y h
    have hs := V.slip η hη x y h
    unfold slipPermits slipIncrement at hs
    have hsh : (reciprocalFrame k).shortShift = (frameAt (List.replicate k Digit.three)).shortShift := rfl
    rw [hsh] at hs
    dsimp only at hs
    unfold ChildFrame.roundedSlip ChildFrame.slip
    exact ⟨hp, by omega⟩
  have key := rankWithIncrements_of_strict_hull hη
    (P := fun z => (frameAt (List.replicate k Digit.three)).price (reciprocalField k) z)
    (J := fun z => (frameAt (List.replicate k Digit.three)).roundedSlip (reciprocalField k) η z)
    (R := R) (cU := cU) (cV := cV) hPU hPV hJU hJV hmono hRU hRV hstrict 1 1 one_pos one_pos
  simpa using key

/-- The characters of `R0plus` on the frame's periods. -/
theorem R0plus_char_U (k : ℕ) (z : Site) :
    R0plus (2 * (k : ℤ) + 3) (by omega) (stairEven_valid_reciprocal k) (z + (2 * (k : ℤ) + 3, 1)) =
      R0plus (2 * (k : ℤ) + 3) (by omega) (stairEven_valid_reciprocal k) z - 2 * (2 * (k : ℤ) + 3) := by
  have hd3 : (3 : ℤ) ≤ 2 * (k : ℤ) + 3 := by omega
  have hdodd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  exact R0plus_U (2 * (k : ℤ) + 3) hd3 hdodd (stairEven_valid_reciprocal k) z

theorem R0plus_char_V (k : ℕ) (z : Site) :
    R0plus (2 * (k : ℤ) + 3) (by omega) (stairEven_valid_reciprocal k)
        (z + (1 - (2 * (k : ℤ) + 3), 1 + (2 * (k : ℤ) + 3))) =
      R0plus (2 * (k : ℤ) + 3) (by omega) (stairEven_valid_reciprocal k) z + 2 * ((2 * (k : ℤ) + 3) + 1) := by
  have hd3 : (3 : ℤ) ≤ 2 * (k : ℤ) + 3 := by omega
  have hdodd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  exact R0plus_V (2 * (k : ℤ) + 3) hd3 hdodd (stairEven_valid_reciprocal k) z

theorem R0minus_char_U (k : ℕ) (z : Site) :
    R0minus (2 * (k : ℤ) + 3) (by omega) (stairEven_valid_reciprocal k) (z + (2 * (k : ℤ) + 3, 1)) =
      R0minus (2 * (k : ℤ) + 3) (by omega) (stairEven_valid_reciprocal k) z - 2 * (2 * (k : ℤ) + 3) := by
  have hd3 : (3 : ℤ) ≤ 2 * (k : ℤ) + 3 := by omega
  have hdodd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  exact R0minus_U (2 * (k : ℤ) + 3) hd3 hdodd (stairEven_valid_reciprocal k) z

theorem R0minus_char_V (k : ℕ) (z : Site) :
    R0minus (2 * (k : ℤ) + 3) (by omega) (stairEven_valid_reciprocal k)
        (z + (1 - (2 * (k : ℤ) + 3), 1 + (2 * (k : ℤ) + 3))) =
      R0minus (2 * (k : ℤ) + 3) (by omega) (stairEven_valid_reciprocal k) z - 2 * ((2 * (k : ℤ) + 3) + 1) := by
  have hd3 : (3 : ℤ) ≤ 2 * (k : ℤ) + 3 := by omega
  have hdodd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  exact R0minus_V (2 * (k : ℤ) + 3) hd3 hdodd (stairEven_valid_reciprocal k) z

/-- The frame's kernel and transverse at `3^k`, as explicit vectors. -/
theorem frame_kernel_threes (k : ℕ) :
    (frameAt (List.replicate k Digit.three)).child.modifiedDeck.kernel = (2 * (k : ℤ) + 3, 1) := by
  rw [frameAt_threes_child, kernel_threes]

theorem frame_transverse_threes (k : ℕ) :
    (frameAt (List.replicate k Digit.three)).child.modifiedDeck.transverse =
      (1 - (2 * (k : ℤ) + 3), 1 + (2 * (k : ℤ) + 3)) := by
  rw [frameAt_threes_child, transverse_threes]

/-- **The rank with increments `(-1, eta)` at `3^k`**, from the reciprocal values alone. -/
theorem rank_threes_of_values (k : ℕ) (V : ReciprocalValues k) (η : ℤ) (hη : η = 1 ∨ η = -1) :
    RankWithIncrements (ePolicy (2 * (k : ℤ) + 3) η (laplacian (reciprocalField k)))
      (frameAt (List.replicate k Digit.three)).child.modifiedDeck.kernel
      (frameAt (List.replicate k Digit.three)).child.modifiedDeck.transverse (-1) η := by
  rcases hη with rfl | rfl
  · refine rank_of_R k V 1 (Or.inl rfl) (fun z => R0plus (2 * (k : ℤ) + 3) (by omega) (stairEven_valid_reciprocal k) z)
      (-(2 * (2 * (k : ℤ) + 3))) (2 * ((2 * (k : ℤ) + 3) + 1)) ?_ ?_
      (fun x i h => R0plus_edge_full k x i h)
    · intro z
      show R0plus (2 * (k : ℤ) + 3) (by omega) (stairEven_valid_reciprocal k)
          (z + (frameAt (List.replicate k Digit.three)).child.modifiedDeck.kernel) =
        R0plus (2 * (k : ℤ) + 3) (by omega) (stairEven_valid_reciprocal k) z + -(2 * (2 * (k : ℤ) + 3))
      rw [frame_kernel_threes k]
      have h := R0plus_char_U k z
      linarith
    · intro z
      show R0plus (2 * (k : ℤ) + 3) (by omega) (stairEven_valid_reciprocal k)
          (z + (frameAt (List.replicate k Digit.three)).child.modifiedDeck.transverse) =
        R0plus (2 * (k : ℤ) + 3) (by omega) (stairEven_valid_reciprocal k) z + 2 * ((2 * (k : ℤ) + 3) + 1)
      rw [frame_transverse_threes k]
      have h := R0plus_char_V k z
      linarith
  · refine rank_of_R k V (-1) (Or.inr rfl) (fun z => R0minus (2 * (k : ℤ) + 3) (by omega) (stairEven_valid_reciprocal k) z)
      (-(2 * (2 * (k : ℤ) + 3))) (-(2 * ((2 * (k : ℤ) + 3) + 1))) ?_ ?_
      (fun x i h => R0minus_edge_full k x i h)
    · intro z
      show R0minus (2 * (k : ℤ) + 3) (by omega) (stairEven_valid_reciprocal k)
          (z + (frameAt (List.replicate k Digit.three)).child.modifiedDeck.kernel) =
        R0minus (2 * (k : ℤ) + 3) (by omega) (stairEven_valid_reciprocal k) z + -(2 * (2 * (k : ℤ) + 3))
      rw [frame_kernel_threes k]
      have h := R0minus_char_U k z
      linarith
    · intro z
      show R0minus (2 * (k : ℤ) + 3) (by omega) (stairEven_valid_reciprocal k)
          (z + (frameAt (List.replicate k Digit.three)).child.modifiedDeck.transverse) =
        R0minus (2 * (k : ℤ) + 3) (by omega) (stairEven_valid_reciprocal k) z + -(2 * ((2 * (k : ℤ) + 3) + 1))
      rw [frame_transverse_threes k]
      have h := R0minus_char_V k z
      linarith

/-- `StrongResidual` at `3^k` from the reciprocal values alone (the rank is now proved, not assumed). -/
theorem strongResidual_threes_unconditional (k : ℕ) (V : ReciprocalValues k) :
    StrongResidual (List.replicate k Digit.three) :=
  strongResidual_threes_of_values k V (fun η hη => rank_threes_of_values k V η hη)

/-- The headline's pure inputs at every `3^k`, from the reciprocal values alone. -/
theorem pureInputs_threes_of_values (hV : ∀ k : ℕ, ReciprocalValues k) :
    (∀ k : ℕ, FLatticePaper.Induction.BaseSlip (List.replicate k Digit.three)) ∧
      (∀ k : ℕ, FLatticePaper.Induction.StrongResidual (List.replicate k Digit.three)) :=
  ⟨fun k => FLatticePaper.Induction.baseSlip_threes k,
    fun k => strongResidual_threes_unconditional k (hV k)⟩

end FLatticePaper.EPolicy
