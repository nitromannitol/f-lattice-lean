import FLatticePaper.Plane.Induction.RouteH1
import FLatticePaper.Plane.Induction.FanInputs
import FLatticePaper.Plane.Induction.ShortPassages

/-! # The `h1` field of `RouteGenuine`

For an odd free H root `z` other than `hFirst`, the grade `t(z)` is odd and at least `n` (the odd spectrum), and `t(z) ≠ n`
(`FanInputs.freeH_odd_t_num`); since `n` is odd, `t(z) ≥ n + 2`. So `RouteH1.h1_arrows_covered` applies to every odd free H root
of the field, with no `t`-hypothesis. -/

namespace FLatticePaper.RouteH1Field

open FLatticePaper FLatticePaper.Induction FLatticePaper.W1

/-- **The `h1` field** (`RouteGenuine.h1`) for the canonical policy `C` of the sign `η`. -/
theorem h1_field {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop} {η : ℤ}
    (hP : frame.Packet G)
    (hsig : ∀ w ∈ frame.closedPolygon, G w - G (w - frame.shortShift) ≤ 0)
    (hAS : ∀ K : ℕ, 2 ≤ K → frame.child.den + 2 * frame.child.num - 1 ≤ frame.child.num * (K : ℤ) →
      2 * frame.child.num * (K : ℤ) ≤ 3 * frame.child.den + 3 * frame.child.num - 1 →
      ∃ p q : ℤ, frame.child.num * p - frame.child.den * q = 2 - frame.child.num ∧
        ∀ k : ℕ, k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ G (p + (k : ℤ), q + (k : ℤ)))
    (hsym : ∀ y, G (FLatticePaper.ReflectedFan.reflH frame y) = G y)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G)
    (hper : HasGeneratorPeriods frame.child G 0 frame.coherentConstantV)
    (hslip : ∀ z ∈ frame.closedPolygon, 0 ≤ frame.slip G 1 z)
    (hseed : ∀ z : Site, EvenSite z → frame.tGrade z = 2 - (frame.child.den + frame.child.num) → G z = 0)
    (hIsym : ∀ z : Site, G (FLatticePaper.W1Strips.iRefl z) = G z)
    (C : CanonicalSignedPolicy frame G η)
    (W : FLatticePaper.W1Witness.OldPolicyWitness frame G seed η) (hW : W.retained = C.policy)
    (hs : ∀ y i, ¬ seed y i) :
    ∀ z ∈ frame.freeH, laplacian G z = 0 → ¬ EvenSite z → z ≠ FLatticePaper.Induction.hFirst → z ≠ frame.hLast →
      (laplacian G (z.1, z.2 - 1) = -1 ∨ C.policy (z.1, z.2 - 1) (z.1 - 1, z.2 - 1)) ∧
      (laplacian G (z.1 - 1, z.2 - 1) = -1 ∨ C.policy (z.1 - 1, z.2 - 1) (z.1 - 1, z.2)) ∧
      (laplacian G (z.1 - 1, z.2) = -1 ∨ C.policy (z.1 - 1, z.2) z) := by
  intro z hz _ hodd hF hL
  have hpar : frame.tGrade z % 2 = 1 := FLatticePaper.Induction.ShortPassages.tGrade_parity' frame z hodd
  have hne_t : frame.tGrade z ≠ frame.child.num := fun ht =>
    hF (FLatticePaper.FanInputs.freeH_odd_t_num frame hz hodd ht)
  have hnodd : frame.child.num % 2 = 1 := FLatticePaper.FanInputs.num_odd frame
  have hsp : frame.child.num ≤ frame.tGrade z := by
    have hz' := hz
    simp only [ChildFrame.freeH, Set.mem_setOf_eq] at hz'
    unfold ChildFrame.hSpectrum at hz'
    rcases hz'.2.2 with h | h <;> omega
  have hbt : frame.child.num + 2 ≤ frame.tGrade z := by omega
  exact FLatticePaper.RouteH1.h1_arrows_covered hP hsig hAS hsym hW1 hper hslip hseed hIsym C W hW hs hz hodd hL hbt

end FLatticePaper.RouteH1Field
