import FLatticePaper.Plane.Induction.CutReflect
import FLatticePaper.Plane.Induction.CutOnePerProper
import FLatticePaper.Plane.Induction.FreeVOrdinate

/-! The free V set is invariant under the reflection `z ↦ (1,−1) + V − z` (`V` the child transverse).

Every free V site has ordinate in `[0, period)` and equals the cut base of its ordinate (`freeV_eq_base`); the reflection of the base
point at ordinate `j` is the base point at `period − 1 − j` (`refl_cut`), which is free V. -/

namespace FLatticePaper.FreeVReflect

open Farey FLatticePaper FLatticePaper.Induction

theorem freeV_reflect_word {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) {z : Site}
    (hz : z ∈ (frameAt word).freeV) :
    ((1 : ℤ), (-1 : ℤ)) + (frameAt word).child.modifiedDeck.transverse - z ∈ (frameAt word).freeV := by
  have hcut := CutOnePerProper.cutOnePerOrdinate_of_proper h
  obtain ⟨base, hbase⟩ := FreeEnum.exists_base (frameAt word) hcut
  have hord : 0 ≤ z.2 ∧ z.2 < FreeEnum.period (frameAt word) := by
    by_cases he : EvenSite z
    · obtain ⟨o0, o1, -⟩ := FreeVOrdinate.freeV_even_ordinate (frameAt word) hz he
      unfold FreeEnum.period
      omega
    · obtain ⟨o0, o1⟩ := FreeVOrdinate.freeV_odd_ordinate (frameAt word) hcut hz he
      unfold FreeEnum.period
      omega
  have hzb : z = base z.2 := FreeEnum.freeV_eq_base (frameAt word) hcut base hbase hz hord
  have hv : FreeEnum.vAt (frameAt word) base z.2 = base z.2 :=
    FreeEnum.vAt_eq_base (frameAt word) base z.2 hord
  have hrefl := CutReflect.refl_cut (frameAt word) base hbase z.2
  have hPj : 0 ≤ FreeEnum.period (frameAt word) - 1 - z.2 ∧ FreeEnum.period (frameAt word) - 1 - z.2 < FreeEnum.period (frameAt word) :=
    ⟨by omega, by omega⟩
  have hbase' : base (FreeEnum.period (frameAt word) - 1 - z.2) ∈ (frameAt word).freeV :=
    (hbase _ hPj.1 hPj.2).1
  have hvj : FreeEnum.vAt (frameAt word) base (FreeEnum.period (frameAt word) - 1 - z.2) =
      base (FreeEnum.period (frameAt word) - 1 - z.2) :=
    FreeEnum.vAt_eq_base (frameAt word) base _ hPj
  have hT : (frameAt word).child.modifiedDeck.transverse = Vdeck (frameAt word) :=
    (EndpointDeck.transverse_eq_Vdeck (frameAt word))
  rw [hT]
  have hzv : z = FreeEnum.vAt (frameAt word) base z.2 := by
    rw [hv]
    exact hzb
  have key : ((1 : ℤ), (-1 : ℤ)) + Vdeck (frameAt word) - z =
      FreeEnum.vAt (frameAt word) base (FreeEnum.period (frameAt word) - 1 - z.2) := by
    conv_lhs => rw [hzv]
    exact hrefl
  rw [key, hvj]
  exact hbase'

end FLatticePaper.FreeVReflect
