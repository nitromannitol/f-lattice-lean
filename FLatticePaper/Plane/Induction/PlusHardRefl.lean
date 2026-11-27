import FLatticePaper.Plane.Induction.HardVFanBlocks
import FLatticePaper.Plane.Induction.Q3Field
import FLatticePaper.Plane.Induction.RowVPlus
import FLatticePaper.Plane.Induction.CanonicalDirections
import FLatticePaper.Plane.Induction.RotatedCap

/-! # The plus reflection maps of the hard V fan (Q41 section 4, blocks 3 and 4)

For the plus sign the fan nodes sit at the physical sites `Y q`, where `Y q = I − Zs q` (block 3, `I = (1,−1)`) or
`Y q = vLast − Zs q` (block 4, `vLast − V = I`). Both maps are the reflection `z ↦ I − z` up to a span vector, which
swaps the two inputs of every site and preserves the Laplacian. This module proves the three facts that
`HardVFanRefute.fan_refuted` needs for these maps: the input correspondence (`hexact`), the Laplacian (`hlapY`), and the
nonfreeness of the fan nodes (`hnf`). -/

namespace FLatticePaper.PlusHardRefl

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.HardVFanBlocks FLatticePaper.RotatedCap

/-- The reflection `z ↦ (1, −1) − z` swaps the two inputs: the input of `(1,−1) − z` is the reflected opposite input. -/
theorem refl_inputs (z : Site) :
    incomingNeg ((1, -1) - z) = (1, -1) - incomingPos z ∧ incomingPos ((1, -1) - z) = (1, -1) - incomingNeg z := by
  have hpar : EvenSite ((1, -1) - z) ↔ EvenSite z := by
    unfold EvenSite
    simp only [Prod.fst_sub, Prod.snd_sub]
    omega
  unfold incomingNeg incomingPos
  by_cases hz : EvenSite z
  · have hw : EvenSite ((1, -1) - z) := hpar.mpr hz
    simp only [if_pos hw, if_pos hz]
    constructor
    · refine Prod.ext ?_ ?_
      · simp only [Prod.fst_sub]
        all_goals omega
      · simp only [Prod.snd_sub]
    · refine Prod.ext ?_ ?_
      · simp only [Prod.fst_sub]
        all_goals omega
      · simp only [Prod.snd_sub]
  · have hw : ¬ EvenSite ((1, -1) - z) := fun h => hz (hpar.mp h)
    simp only [if_neg hw, if_neg hz]
    constructor
    · refine Prod.ext ?_ ?_
      · simp only [Prod.fst_sub]
      · simp only [Prod.snd_sub]
        all_goals omega
    · refine Prod.ext ?_ ?_
      · simp only [Prod.fst_sub]
      · simp only [Prod.snd_sub]
        all_goals omega

/-- The Laplacian is invariant under the reflection `z ↦ (1,−1) − z` of a packet field. -/
theorem refl_lap {fr : ChildFrame} {G : Field} (hP : fr.Packet G) (z : Site) :
    laplacian G ((1, -1) - z) = laplacian G z := by
  obtain ⟨h1, h2⟩ := refl_inputs z
  unfold laplacian
  rw [h1, h2, packet_reflection_I fr hP, packet_reflection_I fr hP, packet_reflection_I fr hP]
  ring

/-- The two input correspondences of the reflected fan map `Y q = (1,−1) − Zs q` (block 3). -/
theorem refl_Zs_inputs (q : Site) :
    ((1, -1) - Zs (incomingNeg q) = incomingNeg ((1, -1) - Zs q) ∧
        (1, -1) - Zs (incomingPos q) = incomingPos ((1, -1) - Zs q)) ∨
      ((1, -1) - Zs (incomingNeg q) = incomingPos ((1, -1) - Zs q) ∧
        (1, -1) - Zs (incomingPos q) = incomingNeg ((1, -1) - Zs q)) := by
  rcases zs_inputs q with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · right
    refine ⟨?_, ?_⟩
    · rw [h1, (refl_inputs (Zs q)).2]
    · rw [h2, (refl_inputs (Zs q)).1]
  · left
    refine ⟨?_, ?_⟩
    · rw [h1, (refl_inputs (Zs q)).1]
    · rw [h2, (refl_inputs (Zs q)).2]

end FLatticePaper.PlusHardRefl
