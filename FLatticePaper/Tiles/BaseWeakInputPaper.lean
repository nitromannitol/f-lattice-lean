import FLatticePaper.Tiles.WeakStepAssembly
import FLatticePaper.Tiles.BaseWeakDomains
import FLatticePaper.Tiles.BaseWeakLattice
import FLatticePaper.Tiles.BaseRespectsAnchoredFamilies

/-! # `BaseWeakInput` for the paper data

The named input `WeakStepAssembly.BaseWeakInput` (the base cases, (A)) does not mention the joint data, so it is discharged
unconditionally, for every base word, from the three base facts: the domains and the paper base condition
(`base_weak_domains`), the boundary strings (`respectsAnchored_of_base`) and the lattice compatibilities (`weakProps_base`). -/

namespace FLatticePaper.Tiles.BaseWeakInputPaper

/-- The base cases of the weak step, for the paper base condition. -/
theorem baseWeakInput_paper : FLatticePaper.Tiles.WeakStepAssembly.BaseWeakInput := by
  intro w hw
  obtain ⟨wo, we, hod, hed, hS⟩ := FLatticePaper.Tiles.BaseWeakDomains.base_weak_domains w
  obtain ⟨hA, hB⟩ := FLatticePaper.Tiles.BaseRespectsAnchoredFamilies.respectsAnchored_of_base w hw wo we hS
  exact ⟨wo, we, hod, hed, hS, hA, hB, FLatticePaper.Tiles.BaseWeakLattice.weakProps_base w hw wo we hS⟩

end FLatticePaper.Tiles.BaseWeakInputPaper
