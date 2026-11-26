import FLatticePaper.Plane.Induction.WestBridge
import FLatticePaper.Plane.Induction.WestArrows
import FLatticePaper.Plane.Induction.WestForced
import FLatticePaper.Plane.Induction.CoveredSW

/-! # The three arrows of the `h1` row at an odd free H root (the covered west square)

For an odd free H root `z` (`t(z) ≥ n + 2`, `z ≠ hLast`) with zero Laplacian, the west square has the arrows
* `z+S → z+SW` (the fan designation `he1`, `CoveredSW.he1_covered`, when `z+S` is white; trivially when black),
* `z+SW → z+W` (adjacency, `WestArrows.edge_west_adjacency`, with the forced input `WestForced.hFsw_of_freeH`),
* `z+W → z` (the prescription, `WestArrows.edge_west_prescription`; `z+W` is white by `WestArrows.white_west`).
Each arrow is `lap x = -1 ∨ C.policy x y` in the form of the `h1` field of `RouteGenuine`. -/

namespace FLatticePaper.RouteH1

open FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.W1 FLatticePaper.W1NonfreeOut
  FLatticePaper.W1Witness FLatticePaper.ReturnPrescribed FLatticePaper.WestArrows FLatticePaper.WestForced
  FLatticePaper.CoveredSW FLatticePaper.ReflectedFan FLatticePaper.WestBridge FLatticePaper.WestSelect

theorem h1_arrows_covered {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop} {η : ℤ}
    (hP : frame.Packet G)
    (hsig : ∀ w ∈ frame.closedPolygon, G w - G (w - frame.shortShift) ≤ 0)
    (hAS : ∀ K : ℕ, 2 ≤ K → frame.child.den + 2 * frame.child.num - 1 ≤ frame.child.num * (K : ℤ) →
      2 * frame.child.num * (K : ℤ) ≤ 3 * frame.child.den + 3 * frame.child.num - 1 →
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
    (hbt : frame.child.num + 2 ≤ frame.tGrade z) :
    (laplacian G (z.1, z.2 - 1) = -1 ∨ C.policy (z.1, z.2 - 1) (z.1 - 1, z.2 - 1)) ∧
    (laplacian G (z.1 - 1, z.2 - 1) = -1 ∨ C.policy (z.1 - 1, z.2 - 1) (z.1 - 1, z.2)) ∧
    (laplacian G (z.1 - 1, z.2) = -1 ∨ C.policy (z.1 - 1, z.2) z) := by
  have hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0 := hP.binary
  have hpres : PrescribedAt frame G η W.retained := by
    rw [hW]
    exact C.prescribed
  have hwS : laplacian G (z.1 - 1, z.2) = 0 := white_west hP.strips hz hodd hne hbt
  have hFsw0 := hFsw_of_freeH hP hW1 hz hodd hne hbt
  have hFsw : laplacian G (z.1 - 1, z.2 - 1) = 0 → ∃ i, ForcedEdge G seed (z.1 - 1, z.2 - 1) i := by
    intro hw
    obtain ⟨i, hi⟩ := hFsw0 hw
    exact ⟨i, forcedEdge_seed_mono hi⟩
  -- arrow c: the west neighbour keeps z (prescription)
  have he3 := edge_west_prescription (η := η) (seed := seed) (G := G) hz hodd hne hbt hwS
  have hc : W.retained (z.1 - 1, z.2) z := edgeP_retained W.toOldPolicyData hpres he3
  -- arrow b: the odd corner keeps the west neighbour (adjacency)
  have he2 := edge_west_adjacency W hs hz hodd hne hbt hwS hbin hFsw
  have hb : W.retained (z.1 - 1, z.2 - 1) (z.1 - 1, z.2) := edgeP_retained W.toOldPolicyData hpres he2
  refine ⟨?_, ?_, ?_⟩
  · by_cases hA : laplacian G (z.1, z.2 - 1) = 0
    · have he1F := he1_covered hP hsig hAS hsym hW1 hper hP.strips hslip hseed hIsym hz hodd hne hbt hA
      have he1 : EdgeP frame η G seed (z.1, z.2 - 1) (z.1 - 1, z.2 - 1) :=
        Or.inl (Or.inr (forcedEdge_seed_mono he1F))
      right
      rw [← hW]
      exact edgeP_retained W.toOldPolicyData hpres he1
    · left
      exact (hbin _).resolve_right hA
  · right
    rw [← hW]
    exact hb
  · right
    rw [← hW]
    exact hc

end FLatticePaper.RouteH1
