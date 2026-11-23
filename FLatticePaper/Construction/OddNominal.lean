import FLatticePaper.Construction.OddCovering
import FLatticePaper.Plane.Induction.TwosInduction

/-! Task 37, steps 2-3: nominal agreement of the odd ordinary standard copies with the odd plane target.

The odd output of a word `w` is the six copies `placedBySlot (standardJets w .odd) (standardSources parents .odd)`, and the
powers of two `IsTwoPow w` are excluded (the lead's decision: their odd outputs come from the base registers of the pure
runs). Each donor tile sits at a chart: its agreement is with the target translated by the jet of its donor slot
`donorSlot slot` (slots 0-3 use the even donor, whose chart is the jet of slot 0; slots 4, 5 the odd donor, whose chart is
the jet of slot 4). The copy of a slot is the donor placed at its own jet `J`, so its heights are the target translated by
`J.1 - chart` plus the slope `J.2`. It agrees with the target exactly when that residual is constant on the copy sites.

Proved here: the residual is zero for the two slots that are their own donor slot (slots 0 and 4), so these copies agree
outright from the chart inputs. For the slots 1, 2, 3, 5 the residual is the named input `hres`: a translation identity of
the odd target on the copy sites (it does not hold on all sites; see the report). -/

namespace FLatticePaper.Construction

open Farey HeightTile FLatticePaper.Induction

/-- The donor slot of a slot: the chart of its donor is the jet of this slot. Slots 0-3 use the even donor (slot 0),
slots 4, 5 the odd donor (slot 4). -/
def donorSlot : Fin 6 → Fin 6 := ![0, 0, 0, 0, 4, 4]

/-- The slope of the odd standard jet of a slot that is its own donor slot is zero. -/
theorem standardJets_odd_slope_zero (word : Word) (s : Fin 6) (hs : donorSlot s = s) :
    (standardJets word .odd s).2 = 0 := by
  have hs' : s = 0 ∨ s = 4 := by
    fin_cases s <;> simp_all [donorSlot]
  rcases hs' with rfl | rfl <;> unfold standardJets <;> by_cases hp : phase word = 0 <;>
    simp [hp, doubleFirst, kernelJet]

/-- Placing a donor with its jet agrees with the target when the residual is constant on the copy sites. -/
theorem copy_agrees_of_residual (parents : TileParents) (word : Word) (slot : Fin 6) (chart : Site) {g : ℤ}
    (hd : (standardSources parents .odd slot).val.Agrees (fun x => planeTarget word .odd (x + chart)) g)
    (hres : ∃ c : ℤ, ∀ x ∈ (ordinaryStandardCopy parents word .odd slot).val.sites,
      planeTarget word .odd (x - (standardJets word .odd slot).1 + chart) +
        ((standardJets word .odd slot).2.1 * x.1 + (standardJets word .odd slot).2.2 * x.2) =
        planeTarget word .odd x + c) :
    ∃ g' : ℤ, (ordinaryStandardCopy parents word .odd slot).val.Agrees (planeTarget word .odd) g' := by
  obtain ⟨c, hc⟩ := hres
  refine ⟨g + c, ?_⟩
  unfold ordinaryStandardCopy placedBySlot TileJet.place NonemptyTile.place
  intro x
  have h := (hd.place (standardJets word .odd slot).1 (standardJets word .odd slot).2) x
  have hx := hc x.1 x.2
  dsimp only at h
  rw [h]
  linarith

/-- Step 3: nominal agreement of the six copies of an odd ordinary standard output with the odd plane target, for every
word that is not a power of two. The donors are given at their charts (`hDonor`); the copies of slots 0 and 4 are
discharged; the copies of slots 1, 2, 3, 5 are the named residual identities `hres` on their copy sites. -/
theorem ordinaryStandard_nominal_odd (parents : TileParents) (word : Word) (hnot : ¬ IsTwoPow word)
    (hDonor : ∀ slot : Fin 6, ∃ g : ℤ, (standardSources parents .odd slot).val.Agrees
      (fun x => planeTarget word .odd (x + (standardJets word .odd (donorSlot slot)).1)) g)
    (hres : ¬ IsTwoPow word → ∀ slot : Fin 6, donorSlot slot ≠ slot → ∃ c : ℤ,
      ∀ x ∈ (ordinaryStandardCopy parents word .odd slot).val.sites,
        planeTarget word .odd (x - (standardJets word .odd slot).1 +
            (standardJets word .odd (donorSlot slot)).1) +
          ((standardJets word .odd slot).2.1 * x.1 + (standardJets word .odd slot).2.2 * x.2) =
        planeTarget word .odd x + c) :
    ∀ slot : Fin 6, ∃ g : ℤ, (ordinaryStandardCopy parents word .odd slot).val.Agrees
      (planeTarget word .odd) g := by
  intro slot
  by_cases h : donorSlot slot = slot
  · obtain ⟨g, hg⟩ := hDonor slot
    rw [h] at hg
    have hs := standardJets_odd_slope_zero word slot h
    have h1 : (standardJets word .odd slot).2.1 = 0 := by simpa using congrArg Prod.fst hs
    have h2 : (standardJets word .odd slot).2.2 = 0 := by simpa using congrArg Prod.snd hs
    exact copy_agrees_of_residual parents word slot (standardJets word .odd slot).1 hg
      ⟨0, fun x _ => by simp [h1, h2]⟩
  · obtain ⟨g, hg⟩ := hDonor slot
    exact copy_agrees_of_residual parents word slot _ hg (hres hnot slot h)

end FLatticePaper.Construction
