import FLatticePaper.Plane.Induction.RankWithValues
import FLatticePaper.Plane.Induction.EPolicyCover

/-!
# The value inequalities at every `k` and the pure threes inputs (task 118, W1 base; the final assembly)

The native covering of the signed policy holds for `k = 0, 1` (`cover_small0`, `cover_small1`) and for `k >= 2` (`cover_ge2`).
From a covering of the native centres, the three value fields `slip`, `price` and `chain` of `ReciprocalValues k` follow at every
centre, by the deck transfer (`ecover_of_ePolicy`, `cov_shift`). The strict rank is then derived from these values
(`rank_threes_of_values`), so `ReciprocalValues` carries no rank field. Hence the pure threes inputs `BaseSlip` and
`StrongResidual` hold at every `3^k`, unconditionally, and the canonical signed games of the reciprocal field exist at every `3^k`.
-/

namespace FLatticePaper.EPolicy

open FLatticePaper FLatticePaper.Induction
open FLatticePaper.Construction
open FLatticePaper.PureRank
open FLatticePaper.Farey

/-- The slip field at `k`, from a covering of the native centres. -/
theorem slip_field_of (k : ℕ)
    (hcov : ∀ η : ℤ, (η = 1 ∨ η = -1) → ∀ r e : Site, NativeP (2 * (k : ℤ) + 3) r → ECover k η r e →
      SE k η r e ∧ PE k r e ∧ CE k η r e)
    (η : ℤ) (hη : η = 1 ∨ η = -1) (c i : Site)
    (h : ePolicy (2 * (k : ℤ) + 3) η (laplacian (reciprocalField k)) c i) :
    slipPermits (reciprocalField k) (fun z => reciprocalField k (z + η • (reciprocalFrame k).shortShift)) c i := by
  have hE := ecover_of_ePolicy k η hη c i h
  obtain ⟨hN, i0, j0, hcr⟩ := nativeRep_spec (stairEven_valid_reciprocal k) c
  have hT := cov_shift k η (nativeRep (2 * (k : ℤ) + 3) c) c (i - c) i0 j0 hcr (hcov η hη _ (i - c) hN hE)
  have hs := slip_of_SE k η c (i - c) hT.1
  have e1 : c + (i - c) = i := by abel
  rw [e1] at hs
  unfold slipPermits slipIncrement
  dsimp only
  unfold ChildFrame.slip at hs
  linarith

/-- The price field at `k`, from a covering of the native centres. -/
theorem price_field_of (k : ℕ)
    (hcov : ∀ η : ℤ, (η = 1 ∨ η = -1) → ∀ r e : Site, NativeP (2 * (k : ℤ) + 3) r → ECover k η r e →
      SE k η r e ∧ PE k r e ∧ CE k η r e)
    (η : ℤ) (hη : η = 1 ∨ η = -1) (c i : Site)
    (h : ePolicy (2 * (k : ℤ) + 3) η (laplacian (reciprocalField k)) c i) :
    (reciprocalFrame k).price (reciprocalField k) i ≤ (reciprocalFrame k).price (reciprocalField k) c := by
  have hE := ecover_of_ePolicy k η hη c i h
  obtain ⟨hN, i0, j0, hcr⟩ := nativeRep_spec (stairEven_valid_reciprocal k) c
  have hT := cov_shift k η (nativeRep (2 * (k : ℤ) + 3) c) c (i - c) i0 j0 hcr (hcov η hη _ (i - c) hN hE)
  have hp := price_of_PE k c (i - c) hT.2.1
  have e1 : c + (i - c) = i := by abel
  rw [e1] at hp
  exact hp

/-- The chain field at `k`, from a covering of the native centres. -/
theorem chain_field_of (k : ℕ)
    (hcov : ∀ η : ℤ, (η = 1 ∨ η = -1) → ∀ r e : Site, NativeP (2 * (k : ℤ) + 3) r → ECover k η r e →
      SE k η r e ∧ PE k r e ∧ CE k η r e)
    (η : ℤ) (hη : η = 1 ∨ η = -1) (c i : Site)
    (h : ePolicy (2 * (k : ℤ) + 3) η (laplacian (reciprocalField k)) c i) :
    (reciprocalFrame k).chainPotential (reciprocalField k) η i ≤
      (reciprocalFrame k).chainPotential (reciprocalField k) η c := by
  have hE := ecover_of_ePolicy k η hη c i h
  obtain ⟨hN, i0, j0, hcr⟩ := nativeRep_spec (stairEven_valid_reciprocal k) c
  have hT := cov_shift k η (nativeRep (2 * (k : ℤ) + 3) c) c (i - c) i0 j0 hcr (hcov η hη _ (i - c) hN hE)
  have hch := chain_of_CE k η c (i - c) hT.2.2
  have e1 : c + (i - c) = i := by abel
  rw [e1] at hch
  exact hch

/-- The value fields of the signed policy at `k`, from a covering of its native centres. -/
theorem valuesOf (k : ℕ)
    (hcov : ∀ η : ℤ, (η = 1 ∨ η = -1) → ∀ r e : Site, NativeP (2 * (k : ℤ) + 3) r → ECover k η r e →
      SE k η r e ∧ PE k r e ∧ CE k η r e) :
    ReciprocalValues k where
  slip := fun η hη c i h => slip_field_of k hcov η hη c i h
  price := fun η hη c i h => price_field_of k hcov η hη c i h
  chain := fun η hη c i h => chain_field_of k hcov η hη c i h

/-- The value fields of the signed policy at every `k`. -/
theorem valuesAll (k : ℕ) : ReciprocalValues k := by
  rcases (show k = 0 ∨ k = 1 ∨ 2 ≤ k by omega) with h | h | h
  · subst h
    exact valuesOf 0 (fun η hη r e hr hc => cover_small0 0 (by norm_num) r hr η hη e hc)
  · subst h
    exact valuesOf 1 (fun η hη r e hr hc => cover_small1 1 (by norm_num) r hr η hη e hc)
  · exact valuesOf k (fun η hη r e hr hc => cover_ge2 k (by omega) η hη r hr e hc)

/-- The strict rank of the policy, derived from the value fields (`rank_threes_of_values`). -/
theorem rank_field (k : ℕ) (V : ReciprocalValues k) (η : ℤ) (hη : η = 1 ∨ η = -1) :
    ∃ R : Site → ℤ, ∀ c i, ePolicy (2 * (k : ℤ) + 3) η (laplacian (reciprocalField k)) c i → R i < R c := by
  obtain ⟨R, -, -, hR, -, -⟩ := rank_threes_of_values k V η hη
  exact ⟨R, fun c i h => hR c i h⟩

/-- The canonical signed games of the reciprocal field at `k`, with every value field and the strict rank derived. -/
noncomputable def canonicalGames (k : ℕ) : CanonicalSignedGames (reciprocalFrame k) (reciprocalField k) :=
  canonicalSignedGames_reciprocal k (valuesAll k) (fun η hη => rank_field k (valuesAll k) η hη)

/-- The pure threes inputs `BaseSlip` and `StrongResidual` at every `3^k`, unconditionally. -/
theorem pure_threes_inputs :
    (∀ k : ℕ, FLatticePaper.Induction.BaseSlip (List.replicate k Digit.three)) ∧
      (∀ k : ℕ, FLatticePaper.Induction.StrongResidual (List.replicate k Digit.three)) :=
  pureInputs_threes_of_values valuesAll

/-- **The final statement.** At every `3^k`: `BaseSlip` and `StrongResidual` of the pure threes word, and the canonical signed
games of the reciprocal field. No hypothesis remains. -/
theorem pure_threes_final :
    (∀ k : ℕ, FLatticePaper.Induction.BaseSlip (List.replicate k Digit.three)) ∧
      (∀ k : ℕ, FLatticePaper.Induction.StrongResidual (List.replicate k Digit.three)) ∧
      ∀ k : ℕ, Nonempty (CanonicalSignedGames (reciprocalFrame k) (reciprocalField k)) :=
  ⟨pure_threes_inputs.1, pure_threes_inputs.2, fun k => ⟨canonicalGames k⟩⟩

end FLatticePaper.EPolicy
