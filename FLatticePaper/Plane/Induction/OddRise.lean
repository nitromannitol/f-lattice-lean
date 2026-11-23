import FLatticePaper.Plane.Induction.SlipPermits
import FLatticePaper.Plane.Induction.StarRangeArgument
import FLatticePaper.Plane.Induction.Packet
import FLatticePaper.Plane.Induction.StandardField

/-! Task 56: `OddBlackNoRise` (fixes/Q3.md), the odd black no-rise premise, reduced to the one configuration the fix excludes.

Step 0 of Q3 (proved here): a rise at a black site with odd `D` forces both translated centres to be black and the other input
to fall by one. The unit slip and the binarity give this from the slip sum `e₁ + e₂ = laplacian F c - laplacian F (c + σ)`.

Consequence (proved here): `OddBlackNoRise` follows from the no-black-pair configuration `NoBlackPairRise`: no black site with
odd `D`, black translate, and an input with slip increment `1`. The exclusion of `NoBlackPairRise` is the sheet-case analysis
of Q3 (choose the active sheet and its matched policy; the common-chart cases; the old free roots; the child boundary vertex
argument; the exceptional vertex). It is NOT proved in this file: it is the named premise of the word-level wrapper. -/

namespace FLatticePaper

open Farey FLatticePaper.Induction

/-- The configuration Q3 excludes: a black site with odd `D`, a black translate `c + σ`, and an input with slip increment `1`. -/
def NoBlackPairRise (F : Field) (σ : Site) : Prop :=
  ∀ c : Site, laplacian F c = -1 → (F c - F (c + σ)) % 2 = 1 → laplacian F (c + σ) = -1 →
    ∀ i : Site, (i = incomingNeg c ∨ i = incomingPos c) → slipIncrement F (fun z => F (z + σ)) c i ≠ 1

/-- Q3, step 0 (negative neighbour): if the negative input rises at a black centre, then the positive input falls by one
and the translate `c + σ` is black. -/
theorem rise_partner_neg {F : Field} {σ c : Site} (hσ : EvenSite σ)
    (hbin : ∀ z, laplacian F z = -1 ∨ laplacian F z = 0)
    (hU : HasUnitSlip F (fun z => F (z + σ))) (hc : laplacian F c = -1)
    (hrise : slipIncrement F (fun z => F (z + σ)) c (incomingNeg c) = 1) :
    slipIncrement F (fun z => F (z + σ)) c (incomingPos c) = -1 ∧ laplacian F (c + σ) = -1 := by
  have hsum := slip_sum_eq F σ c hσ
  have hU2 := hU c (incomingPos c) (Or.inr rfl)
  have hb := hbin (c + σ)
  rw [hc] at hsum
  constructor <;> omega

/-- Q3, step 0 (positive neighbour): the symmetric statement. -/
theorem rise_partner_pos {F : Field} {σ c : Site} (hσ : EvenSite σ)
    (hbin : ∀ z, laplacian F z = -1 ∨ laplacian F z = 0)
    (hU : HasUnitSlip F (fun z => F (z + σ))) (hc : laplacian F c = -1)
    (hrise : slipIncrement F (fun z => F (z + σ)) c (incomingPos c) = 1) :
    slipIncrement F (fun z => F (z + σ)) c (incomingNeg c) = -1 ∧ laplacian F (c + σ) = -1 := by
  have hsum := slip_sum_eq F σ c hσ
  have hU1 := hU c (incomingNeg c) (Or.inl rfl)
  have hb := hbin (c + σ)
  rw [hc] at hsum
  constructor <;> omega

/-- `OddBlackNoRise` from the no-black-pair configuration: a rise at an odd black site would give the configuration. -/
theorem oddBlackNoRise_of_noBlackPairRise {F : Field} {σ : Site} (hσ : EvenSite σ)
    (hbin : ∀ z, laplacian F z = -1 ∨ laplacian F z = 0)
    (hU : HasUnitSlip F (fun z => F (z + σ)))
    (hpair : NoBlackPairRise F σ) : OddBlackNoRise F σ := by
  intro c hc hpar i hi
  show slipIncrement F (fun z => F (z + σ)) c i ≤ 0
  have hb := hU c i hi
  by_contra hgt
  have hone : slipIncrement F (fun z => F (z + σ)) c i = 1 := by omega
  rcases hi with rfl | rfl
  · obtain ⟨-, hL⟩ := rise_partner_neg hσ hbin hU hc hone
    exact hpair c hc hpar hL _ (Or.inl rfl) hone
  · obtain ⟨-, hL⟩ := rise_partner_pos hσ hbin hU hc hone
    exact hpair c hc hpar hL _ (Or.inr rfl) hone

/-- The word-level form: at a proper word, the odd black no-rise premise follows from the binarity of the packet, the unit
slip of the standard field, and the no-black-pair exclusion. -/
theorem oddBlackNoRise_standard (word : Word) (hpk : (frameAt word).Packet (standardField word))
    (hU : HasUnitSlip (standardField word) (fun z => standardField word (z + (frameAt word).shortShift)))
    (hpair : NoBlackPairRise (standardField word) (frameAt word).shortShift) :
    OddBlackNoRise (standardField word) (frameAt word).shortShift :=
  oddBlackNoRise_of_noBlackPairRise (evenSite_shortShift (frameAt word)) hpk.binary hU hpair

end FLatticePaper
