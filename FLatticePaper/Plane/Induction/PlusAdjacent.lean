import FLatticePaper.Plane.Induction.PlusOffer
import FLatticePaper.Plane.Induction.AdjacentOffers
import FLatticePaper.Plane.Induction.Sec3Shift
import FLatticePaper.Plane.Induction.SheetPieces
import FLatticePaper.Plane.Induction.W1MSheet
import FLatticePaper.Plane.Induction.RawB
import FLatticePaper.Plane.Induction.W1Step
import FLatticePaper.Plane.Induction.NativeQ34
import FLatticePaper.Plane.Induction.UnitBound

/-! # W3 of Q34: the sign `+1` permit at a strict `A`-edge in the positive adjacent chart

For a sheet-`A` edge `z → u` with `Ψ z ≥ 0` (so `F z = A z`) and `Ψ u ≥ 1` (so `F u = A u`), and both `z − uq`, `u − uq` in the closed
polygon (`uq = ε U_q` is the adjacent shift):

* `D₊(v) = F v − F (v − uq)` (kernel periodicity: `F (v + σ) = F (v − uq)`);
* `D₊(v) = − min(o₁ v, o₂ v)` at an `A`-root, with `o₁ v = ψ₊(v − lv)` and `o₂ v = Ψ v + ψ₊(v − lv − e)` (`AdjacentOffers.offer_plus`);
* `o₁ z ≤ o₁ u` (`PlusOffer.pJump_mono_sheetA`, the conjugate's price on the sheet-`A` edge);
* `o₁ u ≤ o₂ u` from `Ψ u ≥ 1` and the unit bound `ψ₊(x) ≤ ψ₊(x − e) + 1` (`UnitBound.unit_bound`).

Hence `D₊(u) = −o₁ u ≤ −min(o₁ z, o₂ z) = D₊(z)`. -/

namespace FLatticePaper.PlusAdjacent

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1MSheet FLatticePaper.W1Step

/-- `uq` is the signed even shift `ε • (den, num)`. -/
theorem uq_eq_smul (frame : ChildFrame) :
    frame.uq = frame.eps • ((frame.parents.even.den, frame.parents.even.num) : Site) := by
  unfold ChildFrame.uq
  ext <;> simp

/-- `F` is invariant under the kernel in both directions. -/
theorem kernel_period_sub {word : Word} (hW : StrongEstimates word) (y : Site) :
    standardField word (y - (frameAt word).child.modifiedDeck.kernel) = standardField word y := by
  have h := Sec3Shift.kernel_period hW (y - (frameAt word).child.modifiedDeck.kernel)
  rw [sub_add_cancel] at h
  exact h.symm

/-- **The shortShift slip is the adjacent difference.** `D₊(v) = F v − F (v − uq)`. -/
theorem slip_one_eq_uq {word : Word} (hW : StrongEstimates word) (v : Site) :
    (frameAt word).slip (standardField word) 1 v =
      standardField word v - standardField word (v - (frameAt word).uq) := by
  unfold ChildFrame.slip
  rw [one_smul, Sec3Shift.shortShift_eq_eps_Upar word]
  have hK := Sec3Shift.child_kernel_eq word
  rcases ChildFrame.eps_unit (frameAt word) with he | he
  · rw [he, one_smul]
    unfold ChildFrame.uq
    rw [he, one_mul, one_mul]
    congr 1
    have e : v + Upar word = (v - ((frameAt word).parents.even.den, (frameAt word).parents.even.num)) +
        (frameAt word).child.modifiedDeck.kernel := by
      rw [hK]
      unfold Fraction.unmodifiedDeck
      ext <;> simp
    rw [e, Sec3Shift.kernel_period hW]
  · rw [he, neg_one_smul]
    unfold ChildFrame.uq
    rw [he, neg_one_mul, neg_one_mul]
    have e : v + -Upar word = (v - (-(frameAt word).parents.even.den, -(frameAt word).parents.even.num)) -
        (frameAt word).child.modifiedDeck.kernel := by
      rw [hK]
      unfold Fraction.unmodifiedDeck
      ext <;> simp <;> ring
    rw [e, kernel_period_sub hW]

/-- **The `A`-sheet offer at the adjacent point** (the first offer): `A (v − uq) − A v = ψ₊ (v − lv)`. -/
theorem sheetA_sub_uq_eq_pJump {word : Word} (v : Site) :
    (frameAt word).sheetA (FqW word) (v - (frameAt word).uq) - (frameAt word).sheetA (FqW word) v =
      pJump (frameAt word) (FqW word) (v - (frameAt word).sheetShift) := by
  unfold ChildFrame.sheetA pJump
  have e : v - (frameAt word).uq - (frameAt word).sheetShift =
      (v - (frameAt word).sheetShift) +
        (-((frameAt word).eps * (frameAt word).parents.even.den), -((frameAt word).eps * (frameAt word).parents.even.num)) := by
    unfold ChildFrame.uq
    ext <;> simp <;> ring
  rw [e]

/-- **The sheet `C` offer at the adjacent point** (the second offer):
`C (v − uq) − A v = Ψ v + ψ₊ (v − lv − e)`. -/
theorem sheetC_sub_uq_offer {word : Word} (v : Site) :
    (frameAt word).sheetC (FqW word) (v - (frameAt word).uq) - (frameAt word).sheetA (FqW word) v =
      sheetPsi word v + pJump (frameAt word) (FqW word) (v - (frameAt word).sheetShift - (frameAt word).sheetOffset) := by
  have h := AdjacentOffers.offer_plus (FqW word) (frameAt word).parents.even.num (frameAt word).parents.even.den
    (frameAt word).sheetConstant (frameAt word).eps (frameAt word).sheetShift (frameAt word).sheetOffset v
  rw [← uq_eq_smul] at h
  have e : v - (frameAt word).sheetShift - (frameAt word).sheetOffset - (frameAt word).uq =
      (v - (frameAt word).sheetShift - (frameAt word).sheetOffset) +
        (-((frameAt word).eps * (frameAt word).parents.even.den), -((frameAt word).eps * (frameAt word).parents.even.num)) := by
    unfold ChildFrame.uq
    ext <;> simp <;> ring
  rw [e] at h
  unfold sheetPsi ChildFrame.sheetC ChildFrame.sheetA ChildFrame.siblingSlope pJump
  linarith

/-- **The standard field is the `A`-sheet at a point with `Ψ ≥ 0`** (`F = min(A, C)` on the closed polygon). -/
theorem F_eq_sheetA_of_psi_nonneg {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) {v : Site} (hv : v ∈ (frameAt word).closedPolygon)
    (hψ : 0 ≤ sheetPsi word v) :
    standardField word v = (frameAt word).sheetA (FqW word) v := by
  rw [standardField_eq_sheetMin_of_strong h hSE hv]
  unfold ChildFrame.sheetMin
  apply min_eq_left
  unfold sheetPsi at hψ
  simp only [FqW] at *
  omega

/-- **The sign `+1` slip at an `A`-root in the adjacent chart is minus the minimum of the two offers.** -/
theorem slip_adj_min {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hW : StrongEstimates word) (hSE : StrongEstimates (conjWord word)) {v : Site}
    (hv : v ∈ (frameAt word).closedPolygon) (hvA : v - (frameAt word).uq ∈ (frameAt word).closedPolygon)
    (hψ : 0 ≤ sheetPsi word v) :
    (frameAt word).slip (standardField word) 1 v =
      -min (pJump (frameAt word) (FqW word) (v - (frameAt word).sheetShift))
        (sheetPsi word v + pJump (frameAt word) (FqW word) (v - (frameAt word).sheetShift - (frameAt word).sheetOffset)) := by
  rw [slip_one_eq_uq hW v, F_eq_sheetA_of_psi_nonneg h hSE hv hψ,
    standardField_eq_sheetMin_of_strong h hSE hvA]
  unfold ChildFrame.sheetMin
  have e1 := sheetA_sub_uq_eq_pJump (word := word) v
  have e2 := sheetC_sub_uq_offer (word := word) v
  simp only [FqW] at *
  omega

/-- **W3 (Q34): the sign `+1` permit at a strict `A`-edge in the positive adjacent chart.** The unit bound along `e` is
`UnitBound.unit_bound` (proved from the conjugate's price range and drifts), so no premise beyond the word and the edge. -/
theorem plus_adjacent_strictA {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hW : StrongEstimates word) (hSE : StrongEstimates (conjWord word))
    {seed : Site → Site → Prop}
    (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    {z u : Site}
    (hz : z ∈ (frameAt word).closedPolygon) (hu : u ∈ (frameAt word).closedPolygon)
    (hzA : z - (frameAt word).uq ∈ (frameAt word).closedPolygon) (huA : u - (frameAt word).uq ∈ (frameAt word).closedPolygon)
    (hΨz : 0 ≤ sheetPsi word z) (hΨu : 1 ≤ sheetPsi word u)
    (hedge : sheetPolicyA P (frameAt word).sheetShift z u) :
    (frameAt word).slip (standardField word) 1 u ≤ (frameAt word).slip (standardField word) 1 z := by
  have hunit : pJump (frameAt word) (FqW word) (u - (frameAt word).sheetShift) ≤
      pJump (frameAt word) (FqW word) (u - (frameAt word).sheetShift - (frameAt word).sheetOffset) + 1 :=
    UnitBound.unit_bound h hSE _
  rw [slip_adj_min h hW hSE hu huA (by omega), slip_adj_min h hW hSE hz hzA hΨz]
  have hmono := PlusOffer.pJump_mono_sheetA h hSE P hedge
  simp only [FqW] at *
  omega


end FLatticePaper.PlusAdjacent
