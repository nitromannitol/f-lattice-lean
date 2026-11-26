import FLatticePaper.Plane.Induction.ComparisonContacts
import FLatticePaper.Plane.Induction.TieReduce
import FLatticePaper.Plane.Induction.StrongCoreDef

/-! Task 70 part 2 (fixes/Q1.md paragraphs 3–4): the three comparison fields are below `F` on the closed polygon.

* `cmpLow`: `F(z − v) + ε a·z + c₀ − 1 ≤ F z` is the price bound `P ≥ c₀ − 1` (`ChildFrame.price`, the word's
  `StrongEstimates.priceRange`).
* `cmpUp`: `F(z + σ) ≤ F z` is the slip bound `D_+ ≥ 0` (`slipRange_of_strong`).
* `cmpDown`: `F(z − σ) − 2 ≤ F z` is `D_− ≥ −2`, from the slip bound at the reflected site (`slip_reflect_gen`).

With the binary lemmas of `ComparisonContacts`, the black-root contact alternative holds for each field (`contact_black_E`).
The unit-proof transfer and the W1 exclusion of paragraph 4 (the conclusion that `P` and `J_η` do not increase along the
black and forced white edges) are not formalized here: they need the finite square proof of `SquareClauses` and the W1
derivation of the comparison field. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- `cmpLow ≤ F` on the closed polygon: the word's price lower bound `P ≥ c₀ − 1`, with `c₀` the cut price. -/
theorem cmpLow_le_of_price {word : Word} (hWord : StrongCore word) :
    ∀ z ∈ (frameAt word).closedPolygon,
      FLatticePaper.Contacts.cmpLow (standardField word) (frameAt word).parentShift (frameAt word).eps
        ((frameAt word).parents.odd.num, -(frameAt word).parents.odd.den) (frameAt word).cutPrice z ≤
        standardField word z := by
  intro z hz
  have hp := hWord.priceRange z hz
  unfold ChildFrame.price ChildFrame.parentSlope at hp
  unfold FLatticePaper.Contacts.cmpLow
  have e : z + -(frameAt word).parentShift = z - (frameAt word).parentShift := (sub_eq_add_neg z _).symm
  rw [e]
  have hs : (frameAt word).eps * (((frameAt word).parents.odd.num, -(frameAt word).parents.odd.den).1 * z.1 +
      ((frameAt word).parents.odd.num, -(frameAt word).parents.odd.den).2 * z.2) =
      (frameAt word).eps * ((frameAt word).parents.odd.num * z.1 - (frameAt word).parents.odd.den * z.2) := by
    ring
  linarith [hp.1, hs]

/-- `cmpUp ≤ F` on the closed polygon: `F(z + σ) ≤ F z`, the slip lower bound `D_+ ≥ 0`. -/
theorem cmpUp_le_of_slip {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) :
    ∀ z ∈ (frameAt word).closedPolygon,
      FLatticePaper.Contacts.cmpUp (standardField word) (frameAt word).shortShift z ≤ standardField word z := by
  intro z hz
  have hs := slipRange_of_strong h hSE z hz
  unfold FLatticePaper.Contacts.cmpUp
  linarith [hs.1]

/-- `cmpDown ≤ F` on the closed polygon: `F(z − σ) − 2 ≤ F z`, the slip bound `D_− ≥ −2`, from `D_−(z) = D_+(R z) − 2`. -/
theorem cmpDown_le_of_slip {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) :
    ∀ z ∈ (frameAt word).closedPolygon,
      FLatticePaper.Contacts.cmpDown (standardField word) (frameAt word).shortShift z ≤ standardField word z := by
  intro z hz
  have hR := slipRange_of_strong h hSE ((frameAt word).centre - z)
    ((frameAt word).reflect_mem_closedPolygon hz)
  have hsr := (frameAt word).slip_reflect_gen (packet_of_strong h hSE) (frameAt word).shortShift
    ((frameAt word).centre - z)
  rw [sub_sub_cancel, (frameAt word).tGrade_shortShift] at hsr
  unfold FLatticePaper.Contacts.cmpDown
  linarith [hR.1, hsr]

/-- **Contact at a black root, for the comparison fields (task 70).** If `F` is black at the centre `c ∈ E`, the comparison
field `m` is binary and below `F` on `E`, and `F c = m c`, then both inputs of `c` are contacts (`F = m` there). -/
theorem contact_black_E {word : Word} (hpk : (frameAt word).Packet (standardField word))
    {m : Field} (hm : ∀ z, laplacian m z = -1 ∨ laplacian m z = 0)
    (hle : ∀ z ∈ (frameAt word).closedPolygon, m z ≤ standardField word z)
    {c : Site} (hc : c ∈ (frameAt word).closedPolygon) (hF : laplacian (standardField word) c = -1)
    (heq : standardField word c = m c) :
    standardField word (FLatticePaper.incomingNeg c) = m (FLatticePaper.incomingNeg c) ∧
      standardField word (FLatticePaper.incomingPos c) = m (FLatticePaper.incomingPos c) := by
  have hN := (frameAt word).black_input_mem hpk hc hF (Or.inl rfl)
  have hP := (frameAt word).black_input_mem hpk hc hF (Or.inr rfl)
  exact FLatticePaper.Contacts.contact_black hF (hm c) heq
    (hle _ hN) (hle _ hP)

end FLatticePaper.Induction
