import FLatticePaper.Plane.Induction.CoveredSW
import FLatticePaper.Plane.Induction.WestArrows
import FLatticePaper.Plane.Induction.WestForced
import FLatticePaper.Plane.Induction.WestSelect
import FLatticePaper.Plane.Induction.CanonicalSigned
import FLatticePaper.Plane.Induction.W1Witness

/-! # The H-root bridge with the canonical white rule (Q32 (iv), covered odd H roots)

For a covered odd free H root `z` (`t(z) ≥ n+2`, `z ≠ hLast`, `z` and `z+S` white) the three arrows of the west square hold for the
canonical policy `C` (a white keeps exactly its selected input; the root keeps its prescription), with the west corner `z+SW` forced
by `WestForced.hFsw_of_freeH` and the fan designation `z+S → z+SW` by `CoveredSW.he1_covered`. The policy `W` is the witness of
`C` (`W.retained = C.policy`), so the white uniqueness and the prescription are read off the canonical policy. -/

namespace FLatticePaper.WestBridge

open FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.W1 FLatticePaper.W1NonfreeOut
  FLatticePaper.WestArrows FLatticePaper.WestSelect FLatticePaper.WestForced FLatticePaper.CoveredSW
  FLatticePaper.ReflectedFan FLatticePaper.ReturnPrescribed

/-- **The west square at a covered odd H root for the canonical policy.** -/
theorem parentSquareOut_covered_H {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop} {η : ℤ}
    (hP : frame.Packet G)
    (hsig : ∀ w ∈ frame.closedPolygon, G w - G (w - frame.shortShift) ≤ 0)
    (hAS : ∀ K : ℕ, 2 ≤ K → frame.child.den + 2 * frame.child.num - 1 ≤ frame.child.num * (K : ℤ) →
      2 * frame.child.num * (K : ℤ) ≤ 3 * frame.child.den + 5 * frame.child.num - 1 →
      ∃ p q : ℤ, frame.child.num * p - frame.child.den * q = 2 - frame.child.num ∧
        ∀ k : ℕ, k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ G (p + (k : ℤ), q + (k : ℤ)))
    (hsym : ∀ y, G (reflH frame y) = G y)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G)
    (hper : HasGeneratorPeriods frame.child G 0 frame.coherentConstantV)
    (hslip : ∀ z ∈ frame.closedPolygon, 0 ≤ frame.slip G 1 z)
    (hseed : ∀ z : Site, EvenSite z → frame.tGrade z = 2 - (frame.child.den + frame.child.num) → G z = 0)
    (hIsym : ∀ z : Site, G (FLatticePaper.W1Strips.iRefl z) = G z)
    (C : CanonicalSignedPolicy frame G η)
    (W : FLatticePaper.W1Witness.OldPolicyWitness frame G seed η) (hW : W.retained = C.policy)
    (hs : ∀ y i, ¬ seed y i)
    {z : Site} (hz : z ∈ frame.freeH) (hodd : ¬ EvenSite z) (hne : z ≠ frame.hLast)
    (hbt : frame.child.num + 2 ≤ frame.tGrade z) (hzw : laplacian G z = 0)
    (hzS : laplacian G (z.1, z.2 - 1) = 0) :
    ParentSquareOut G W.retained z := by
  have hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0 := hP.binary
  have hpres : PrescribedAt frame G η W.retained := by
    rw [hW]
    exact C.prescribed
  have hwu : ∀ c j j', laplacian G c = 0 → W.retained c j → W.retained c j' → j = j' := by
    intro c j j' hc h1 h2
    rw [hW] at h1 h2
    have e1 := (C.white_policy c hc j).mp h1
    have e2 := (C.white_policy c hc j').mp h2
    rw [e1, e2]
  have hFsw : laplacian G (z.1 - 1, z.2 - 1) = 0 → ∃ i, ForcedEdge G seed (z.1 - 1, z.2 - 1) i := by
    intro hw
    obtain ⟨i, hi⟩ := hFsw_of_freeH hP hW1 hz hodd hne hbt hw
    exact ⟨i, forcedEdge_seed_mono hi⟩
  have he1F : ForcedEdge G (fun _ _ => False) (z.1, z.2 - 1) (z.1 - 1, z.2 - 1) :=
    he1_covered hP hsig hAS hsym hW1 hper hP.strips hslip hseed hIsym hz hodd hne hbt hzS
  have he1 : FLatticePaper.ReturnPrescribed.EdgeP frame η G seed (z.1, z.2 - 1) (z.1 - 1, z.2 - 1) :=
    Or.inl (Or.inr (forcedEdge_seed_mono he1F))
  exact parentSquareOut_of_freeH_west hP.strips W hs hpres hz hodd hne hbt hzw hwu hbin hFsw he1

end FLatticePaper.WestBridge
