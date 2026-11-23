import FLatticePaper.Construction.OddCovering
import FLatticePaper.Plane.Induction.TwosInduction

/-! Task 37, steps 2 and 3: nominal agreement of the odd ordinary standard copies with the odd plane target.

The odd output of a word `w` is the six copies `placedBySlot (standardJets w .odd) (standardSources parents .odd)`. The
powers of two `IsTwoPow w` are excluded: their odd outputs come from the base registers of the pure runs, not from the
ordinary schedule (the lead's decision), so the statement carries the hypothesis `¬ IsTwoPow w`.

Proved here: a copy with a zero jet is its donor (`copy_of_zero_jet`), so phase zero slot zero and phase one slot four
are the donor agreements `hEven` and `hOdd`. The remaining slots, with non-zero offsets, are the named input `hrest`; the
offset algebra for them needs the representative route of step 1 and the sheet identity on the conjugate polygon, and is
not a translation identity on all sites (checked numerically; see the report). -/

namespace FLatticePaper.Construction

open Farey HeightTile FLatticePaper.Induction

/-- The odd standard jet of slot zero is zero in phase zero. -/
theorem standardJets_odd_zero_of_phase_zero (word : Word) (h : phase word = 0) :
    standardJets word .odd 0 = 0 := by
  unfold standardJets
  simp [h, doubleFirst]

/-- The odd standard jet of slot four is zero in phase one. -/
theorem standardJets_odd_four_of_phase_one (word : Word) (h : phase word = 1) :
    standardJets word .odd 4 = 0 := by
  unfold standardJets
  simp [h, doubleFirst]

/-- A copy with a zero jet is its donor: the agreement passes through the placement unchanged. -/
theorem copy_of_zero_jet (parents : TileParents) (word : Word) (parity : Parity) (slot : Fin 6)
    {target : FLatticePaper.Site → ℤ} {g : ℤ} (hz : standardJets word parity slot = 0)
    (hd : (standardSources parents parity slot).val.Agrees target g) :
    (ordinaryStandardCopy parents word parity slot).val.Agrees target g := by
  have h := hd.place 0 0
  unfold ordinaryStandardCopy placedBySlot TileJet.place
  rw [hz]
  simpa [NonemptyTile.place] using h

/-- Step 2, the two zero-offset slots of the odd output: slot zero in phase zero is the even donor, and slot four in
phase one is the odd donor, both agreeing with the odd plane target. -/
theorem odd_copy_zero_offset_agrees (parents : TileParents) (word : Word)
    (hEven : phase word = 0 → ∃ g : ℤ, parents.even.val.Agrees (planeTarget word .odd) g)
    (hOdd : phase word = 1 → ∃ g : ℤ, parents.odd.val.Agrees (planeTarget word .odd) g) :
    (phase word = 0 → ∃ g : ℤ, (ordinaryStandardCopy parents word .odd 0).val.Agrees
      (planeTarget word .odd) g) ∧
    (phase word = 1 → ∃ g : ℤ, (ordinaryStandardCopy parents word .odd 4).val.Agrees
      (planeTarget word .odd) g) := by
  constructor
  · intro h
    obtain ⟨g, hg⟩ := hEven h
    exact ⟨g, copy_of_zero_jet parents word .odd 0 (standardJets_odd_zero_of_phase_zero word h) hg⟩
  · intro h
    obtain ⟨g, hg⟩ := hOdd h
    exact ⟨g, copy_of_zero_jet parents word .odd 4 (standardJets_odd_four_of_phase_one word h) hg⟩

/-- **Step 3: nominal agreement of the six copies of an odd ordinary standard output with the odd plane target, for
every word except the powers of two.** The two zero-offset copies are discharged from the donor agreements `hEven`
(phase zero, slot zero) and `hOdd` (phase one, slot four). The four remaining copies of each phase have non-zero offsets
and are the named input `hrest`, for words that are not powers of two. -/
theorem ordinaryStandard_nominal_odd (parents : TileParents) (word : Word) (hnot : ¬ IsTwoPow word)
    (hEven : phase word = 0 → ∃ g : ℤ, parents.even.val.Agrees (planeTarget word .odd) g)
    (hOdd : phase word = 1 → ∃ g : ℤ, parents.odd.val.Agrees (planeTarget word .odd) g)
    (hrest : ¬ IsTwoPow word → ∀ slot : Fin 6,
      ¬ ((phase word = 0 ∧ slot = 0) ∨ (phase word = 1 ∧ slot = 4)) →
        ∃ g : ℤ, (ordinaryStandardCopy parents word .odd slot).val.Agrees (planeTarget word .odd) g) :
    ∀ slot : Fin 6, ∃ g : ℤ, (ordinaryStandardCopy parents word .odd slot).val.Agrees
      (planeTarget word .odd) g := by
  obtain ⟨hz0, hz4⟩ := odd_copy_zero_offset_agrees parents word hEven hOdd
  intro slot
  by_cases hzero : (phase word = 0 ∧ slot = 0) ∨ (phase word = 1 ∧ slot = 4)
  · rcases hzero with ⟨h, rfl⟩ | ⟨h, rfl⟩
    · exact hz0 h
    · exact hz4 h
  · exact hrest hnot slot hzero

end FLatticePaper.Construction
