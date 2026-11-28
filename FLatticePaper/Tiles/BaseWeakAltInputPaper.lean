import FLatticePaper.Tiles.WeakAltStepAssembly
import FLatticePaper.Tiles.BaseAltEmpty
import FLatticePaper.Tiles.BaseAltThree
import FLatticePaper.Tiles.BaseAltTwo

/-! # `BaseWeakAltInput` for the paper data

At every base word `w` (`w = []`, `w = 3^k`, `w = 2^k`), the alternate base odometers of the families `BaseAltEmpty`, `BaseAltThree`,
`BaseAltTwo` are the odometers on the alternate base tiles `paperAltBaseTiles w`: they satisfy the alternate base condition, respect
the half strings at the anchors `altRevVAnchor`, `altFwdHAnchor` (which are `(0,0)` under the anchors of the data, `PaperAltAnc`), and
are lattice compatible along the second lattice vectors. At a base word `CorrectedAfterTwo`/`CorrectedAfterThree` are false, so both
halves of `WeakAltPropsU` apply. The statement does not depend on `altBase` (the odometers are built from the paper values). -/

namespace FLatticePaper.Tiles.BaseWeakAltInputPaper

open FLatticePaper.Farey
open FLatticePaper.Tiles.JointFamily
open FLatticePaper.Tiles.WeakAltStepAssembly (BaseWeakAltInput)
open FLatticePaper.Tiles.Standard (IsBase)
open FLatticePaper.Tiles.SurgicalAlt (PaperAltBaseCond RespectsHalfV RespectsHalfH altRevVAnchor altFwdHAnchor)
open FLatticePaper.Tiles.SurgicalAltTiles (altOddTile altEvenTile)
open FLatticePaper.Tiles.PaperAltBase (paperAltBaseTiles)

/-- **`BaseWeakAltInput` for the paper data**, at every base word, for every joint data `D`. -/
theorem baseWeakAltInput_paper (D : JointData) : BaseWeakAltInput D := by
  intro _ hAnc w hw
  have hA := hAnc
  rcases hw with rfl | hthree | htwo
  · -- the empty word
    exact ⟨BaseAltEmpty.oddO, BaseAltEmpty.evenE, rfl, rfl, BaseAltEmpty.paperAltBaseCond_empty,
      BaseAltEmpty.respectsHalfV_empty D.anc (hA []).2, BaseAltEmpty.respectsHalfH_empty D.anc (hA []).1,
      BaseAltEmpty.weakAltPropsU_empty⟩
  · obtain ⟨k, rfl⟩ : ∃ k, w = List.replicate k Digit.three :=
      ⟨w.length, List.eq_replicate_iff.2 ⟨rfl, hthree⟩⟩
    by_cases hk : k = 0
    · subst hk
      exact ⟨BaseAltEmpty.oddO, BaseAltEmpty.evenE, rfl, rfl, BaseAltEmpty.paperAltBaseCond_empty,
        BaseAltEmpty.respectsHalfV_empty D.anc (hA []).2, BaseAltEmpty.respectsHalfH_empty D.anc (hA []).1,
        BaseAltEmpty.weakAltPropsU_empty⟩
    · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
      exact ⟨BaseAltThree.oddT k, BaseAltThree.evenT k, rfl, rfl,
        BaseAltThree.paperAltBaseCond_three k hk1,
        BaseAltThree.respectsHalfV_three k hk1 D.anc (hA _).2,
        BaseAltThree.respectsHalfH_three k D.anc (hA _).1,
        BaseAltThree.weakAltPropsU_three k hk1⟩
  · obtain ⟨k, rfl⟩ : ∃ k, w = List.replicate k Digit.two :=
      ⟨w.length, List.eq_replicate_iff.2 ⟨rfl, htwo⟩⟩
    by_cases hk : k = 0
    · subst hk
      exact ⟨BaseAltEmpty.oddO, BaseAltEmpty.evenE, rfl, rfl, BaseAltEmpty.paperAltBaseCond_empty,
        BaseAltEmpty.respectsHalfV_empty D.anc (hA []).2, BaseAltEmpty.respectsHalfH_empty D.anc (hA []).1,
        BaseAltEmpty.weakAltPropsU_empty⟩
    · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
      exact ⟨BaseAltTwo.oddW k, BaseAltTwo.evenW k, rfl, rfl,
        BaseAltTwo.paperAltBaseCond_two k hk1,
        BaseAltTwo.respectsHalfV_two k D.anc (hA _).2,
        BaseAltTwo.respectsHalfH_two k hk1 D.anc (hA _).1,
        BaseAltTwo.weakAltPropsU_two k hk1⟩

end FLatticePaper.Tiles.BaseWeakAltInputPaper
