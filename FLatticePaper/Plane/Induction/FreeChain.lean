import FLatticePaper.Plane.Induction.FreePolicy
import FLatticePaper.Plane.Induction.ChainW1
import FLatticePaper.Plane.Induction.W1TieBand
import FLatticePaper.Plane.Induction.ChainDeck
import FLatticePaper.Plane.Induction.DeckSelection

/-! hgames: the chain monotonicity wired to the free policy.

* `chain_drift_of_periods`: the chain potential `Φ_η` drifts by a constant under every deck translate (`Φ(x+U) = Φ x − 1`, `Φ(x+V) = Φ x + 2η`
  from `W1TieBand.chainPotential_drift`, whose slip hypothesis is proved here from the generator periods and `tg(σ) = 2`).
* `chain_free`: `Φ_η` does not increase along `freePolicy F η` (rank-independent), given the packet, the W1 forcing of the frame, and the named
  inputs of the two signs (`FreeNamedInputs`: the permits, `P` and `J` monotone, the strict rank). -/

namespace FLatticePaper.FreeChain

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.DeckSelection FLatticePaper.FreePolicy FLatticePaper.SquareClauses

/-- Translation by `i` kernels and `j` transverse vectors shifts a function with constant increments by `i·c_U + j·c_V`. -/
theorem iter_add {G : Site → ℤ} {v : Site} {c : ℤ} (hG : ∀ x, G (x + v) = G x + c) (i : ℤ) :
    ∀ x, G (x + i • v) = G x + i * c := by
  induction i using Int.induction_on with
  | zero => intro x; simp
  | succ k ih =>
    intro x
    rw [show x + ((k : ℤ) + 1) • v = (x + (k : ℤ) • v) + v by rw [add_smul, one_smul, add_assoc], hG, ih x]
    ring
  | pred k ih =>
    intro x
    have h1 := hG (x + (-(k : ℤ) - 1) • v)
    rw [show x + (-(k : ℤ) - 1) • v + v = x + (-(k : ℤ)) • v by rw [sub_smul, one_smul]; abel, ih x] at h1
    linear_combination (-1 : ℤ) * h1

theorem transverse_grade_smul (frame : ChildFrame) (η : ℤ) :
    frame.child.transverseGrade (η • frame.shortShift) = 2 * η := by
  unfold Fraction.transverseGrade
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  have h := frame.transverseGrade_shortShift
  unfold Fraction.transverseGrade at h
  linear_combination η * h

theorem transverse_grade_add_smul (frame : ChildFrame) (η : ℤ) (z : Site) :
    frame.child.transverseGrade (z + η • frame.shortShift) = frame.child.transverseGrade z + 2 * η := by
  rw [← transverse_grade_smul frame η]
  unfold Fraction.transverseGrade
  simp only [Prod.fst_add, Prod.snd_add]
  ring

/-- **The chain drift from the periods.** `Φ_η(x − (iU + jV)) = Φ_η x + c` for a constant `c`, from the price and slip drifts of the
packet and the generator periods (`chainPotential_drift`). -/
theorem chain_drift_of_periods (frame : ChildFrame) {F : Field} {cU cV : ℤ}
    (hF : HasGeneratorPeriods frame.child F cU cV) (hpk : frame.Packet F) (η : ℤ) :
    ∀ i j : ℤ, ∃ c : ℤ, ∀ x,
      frame.chainPotential F η (x - frame.child.modifiedDeck.combine i j) = frame.chainPotential F η x + c := by
  have hprice : ∀ z, frame.price F (z + frame.child.modifiedDeck.kernel) - frame.price F z = -1 ∧
      frame.price F (z + frame.child.modifiedDeck.transverse) - frame.price F z = 0 := by
    intro z
    have hk : frame.child.modifiedDeck.kernel = frame.child.modifiedDeck.combine 1 0 := by
      rw [combine_eq frame 1 0]
      simp
    have ht : frame.child.modifiedDeck.transverse = frame.child.modifiedDeck.combine 0 1 := by
      rw [combine_eq frame 0 1]
      simp
    have h1 := ChainDeck.price_combine frame hpk 1 0 z
    have h2 := ChainDeck.price_combine frame hpk 0 1 z
    rw [← hk] at h1
    rw [← ht] at h2
    constructor <;> linarith
  have hslip : ∀ z, frame.slip F η (z + frame.child.modifiedDeck.kernel) - frame.slip F η z = 0 ∧
      frame.slip F η (z + frame.child.modifiedDeck.transverse) - frame.slip F η z = 2 * η := by
    intro z
    have a0 := hF.1 z
    have a1 : F (z + frame.child.modifiedDeck.kernel + η • frame.shortShift) =
        F (z + η • frame.shortShift) + cU := by
      rw [show z + frame.child.modifiedDeck.kernel + η • frame.shortShift =
        (z + η • frame.shortShift) + frame.child.modifiedDeck.kernel by abel]
      exact hF.1 _
    have b0 := hF.2 z
    have b1 : F (z + frame.child.modifiedDeck.transverse + η • frame.shortShift) =
        F (z + η • frame.shortShift) - frame.child.transverseGrade (z + η • frame.shortShift) + cV := by
      rw [show z + frame.child.modifiedDeck.transverse + η • frame.shortShift =
        (z + η • frame.shortShift) + frame.child.modifiedDeck.transverse by abel]
      exact hF.2 _
    have tw := transverse_grade_add_smul frame η z
    have hK := hF.1 (z + η • frame.shortShift)
    unfold ChildFrame.slip
    constructor
    · have e1 : F (z + frame.child.modifiedDeck.kernel + η • frame.shortShift) = F (z + η • frame.shortShift) + cU := a1
      linarith
    · linarith
  obtain ⟨hU, hV⟩ := FLatticePaper.W1TieBand.chainPotential_drift hprice hslip
  have hUi := iter_add (G := frame.chainPotential F η) (v := frame.child.modifiedDeck.kernel) (c := -1) hU
  have hVi := iter_add (G := frame.chainPotential F η) (v := frame.child.modifiedDeck.transverse) (c := 2 * η) hV
  have hcomb : ∀ i j x, frame.chainPotential F η (x + frame.child.modifiedDeck.combine i j) =
      frame.chainPotential F η x - i + 2 * η * j := by
    intro i j x
    rw [combine_eq frame i j, show x + (i • frame.child.modifiedDeck.kernel + j • frame.child.modifiedDeck.transverse) =
      (x + j • frame.child.modifiedDeck.transverse) + i • frame.child.modifiedDeck.kernel by abel,
      hUi i, hVi j]
    ring
  intro i j
  refine ⟨i - 2 * η * j, fun x => ?_⟩
  have e : x - frame.child.modifiedDeck.combine i j = x + frame.child.modifiedDeck.combine (-i) (-j) := by
    rw [combine_eq frame i j, combine_eq frame (-i) (-j)]
    ext <;> simp <;> ring
  rw [e, hcomb]
  ring

/-- **The chain monotonicity of the free policy.** `Φ_η` does not increase along `freePolicy F η` (the rank-independent graph), given the
packet, the W1 forcing, and the named inputs of the two signs (the permits, the monotonicity of `P` and `J`, and the strict rank along the
retained edges). The squares and the deck equivariance are derived from the strict ranks. -/
theorem chain_free (frame : ChildFrame) {F : Field} {cU cV : ℤ} (hF : HasGeneratorPeriods frame.child F cU cV)
    (hpk : frame.Packet F) {η : ℤ} (hη : η = 1 ∨ η = -1)
    (hc : 3 ≤ frame.child.den - frame.child.num) (hU : HasUnitPrice frame F)
    (hW1word : FLatticePaper.W1.W1Forced frame.child.num frame.child.den F)
    {R Rm : Site → ℤ} (N : FreeNamedInputs frame F η R) (N' : FreeNamedInputs frame F (-η) Rm) :
    NonincreasingAlong (frame.chainPotential F η) (freePolicy frame F η) := by
  have hex : ForcedExists frame F := forcedExists_of frame hpk hW1word
  have hsq : ∀ a b : ℤ, SquareClauseSat F (freeSel frame F η) a b :=
    squares_of_strict frame hpk N.strictRank
  have hsq' : ∀ a b : ℤ, SquareClauseSat F (freeSel frame F (-η)) a b :=
    squares_of_strict frame hpk N'.strictRank
  exact ChainW1.chain_nonincreasing_of_pair frame (canonicalSigned_of_free frame hpk hex hη N)
    (canonicalSigned_of_free frame hpk hex (neg_unit hη) N') hpk hη hc hU hW1word
    (fun z u i j h => freePolicy_deck frame hpk hex hη hsq i j z u h)
    (fun z u i j h => freePolicy_deck frame hpk hex (neg_unit hη) hsq' i j z u h)
    (chain_drift_of_periods frame hF hpk η)

end FLatticePaper.FreeChain
