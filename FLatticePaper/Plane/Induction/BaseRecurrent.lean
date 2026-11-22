import FLatticePaper.Plane.Induction.BaseInputsProof
import FLatticePaper.Plane.Induction.SheetMinFromConj

/-! The fort form of the recurrence of a binary field (task 37, item 1).

`Recurrent.allowed` gives, for every nonempty finite `S`, a site `x ∈ S` with `incomingDegree S x ≤ laplacian + 1`. For a
binary field, a site of an incoming fort has `incomingDegree ≥ 1` at charge `−1` and `= 2` at charge `0`, which is
excluded. So `Recurrent` implies `RecurrentField`. The sheet minimum of the conjugate chain is binary at every site and
recurrent (`sheetMin_binary_recurrent_of_chain`), which discharges the hypothesis of the comparison. -/

namespace FLatticePaper

/-- A recurrent binary field has no nonempty finite incoming fort. -/
theorem recurrentField_of_recurrent {field : Field} (hr : Recurrent field)
    (hbin : ∀ z, laplacian field z = -1 ∨ laplacian field z = 0) : RecurrentField field := by
  intro S hne hfort
  have hsuper : Superharmonic field := fun z => by
    rcases hbin z with h | h <;> omega
  obtain ⟨x, hx, hle⟩ := hr.allowed hsuper S hne
  have hle' : incomingDegree S x ≤ laplacian field x + 1 := hle
  have hfx := hfort x (Finset.mem_coe.mpr hx)
  unfold incomingDegree at hle'
  rcases hfx with ⟨hlap, hin⟩ | ⟨hlap, hin1, hin2⟩
  · have hin' : incomingNeg x ∈ S ∨ incomingPos x ∈ S := hin
    rw [hlap] at hle'
    split_ifs at hle' <;> simp_all
  · have h1 : incomingNeg x ∈ S := hin1
    have h2 : incomingPos x ∈ S := hin2
    rw [hlap, if_pos h1, if_pos h2] at hle'
    omega

namespace Induction
open Farey

/-- The sheet minimum of the conjugate chain has the fort form of its recurrence. -/
theorem sheetMin_recurrentField_of_chain {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hG : (frameAt (conjWord word)).Packet (standardField (conjWord word)))
    (hunit : ∀ c i : Site, FLatticePaper.Edge i c →
      -1 ≤ sheetChainPotential word (standardField (conjWord word)) i -
          sheetChainPotential word (standardField (conjWord word)) c ∧
        sheetChainPotential word (standardField (conjWord word)) i -
          sheetChainPotential word (standardField (conjWord word)) c ≤ 1)
    {α : Type*} [LinearOrder α] (rankA rankC : Site → α)
    (hrankA : IsConstrainedBurningRank (quarterTurnField (standardField (conjWord word))) rankA
      (fun c i => sheetChainPotential word (standardField (conjWord word)) i ≤
        sheetChainPotential word (standardField (conjWord word)) c))
    (hrankC : IsConstrainedBurningRank (quarterTurnField (standardField (conjWord word))) rankC
      (fun c i => sheetChainPotential word (standardField (conjWord word)) (c + (frameAt word).sheetOffset) ≤
        sheetChainPotential word (standardField (conjWord word)) (i + (frameAt word).sheetOffset))) :
    RecurrentField ((frameAt word).sheetMin (quarterTurnField (standardField (conjWord word)))) := by
  obtain ⟨hbin, hrec⟩ := sheetMin_binary_recurrent_of_chain h hG hunit rankA rankC hrankA hrankC
  exact recurrentField_of_recurrent hrec hbin

end Induction

end FLatticePaper
