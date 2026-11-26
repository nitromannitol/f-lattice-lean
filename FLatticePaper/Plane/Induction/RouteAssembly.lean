import FLatticePaper.Plane.Induction.FreeRoutes
import FLatticePaper.Plane.Induction.RouteH1Field
import FLatticePaper.Plane.Induction.C2Axial
import FLatticePaper.Plane.Induction.V2Minus
import FLatticePaper.Plane.Induction.RoutePresc
import FLatticePaper.Plane.Induction.RouteH3
import FLatticePaper.Plane.Induction.RouteFan
import FLatticePaper.Plane.Induction.RouteH3Easy
import FLatticePaper.Plane.Induction.HEasyP
import FLatticePaper.Plane.Induction.VEasy
import FLatticePaper.Plane.Induction.V3Last
import FLatticePaper.Plane.Induction.RouteRows
import FLatticePaper.Plane.Induction.EndpointStrips
import FLatticePaper.Plane.Induction.HMidStrict
import FLatticePaper.Plane.Induction.V3HardNW

/-! # The route genuine structure from its parts (assembly with explicit open hypotheses)

`RouteGenuine C` is assembled from the field lemmas. Three inputs are explicit hypotheses, each an open claim:
* `hQ37` : the middle target of the `h3` second arrow is white when `t(z) ≤ d` (the claim filed as Q37);
* `hv3hard` : the middle arrow of the `v3` row for `d < 2n` (the rotated fan, in progress).
The `d ≥ 3n − 2` and `d ≥ 2n` cases of the middles are proved from the north fan and the easy-regime lemmas. -/

namespace FLatticePaper.RouteAssembly

open FLatticePaper FLatticePaper.Induction FLatticePaper.W1 FLatticePaper.W1Witness FLatticePaper.FreeRoutes
  FLatticePaper.EndpointRows FLatticePaper.RoutePresc FLatticePaper.RouteH3 FLatticePaper.RouteFan
  FLatticePaper.RouteH3Easy FLatticePaper.VEasy FLatticePaper.V3Last FLatticePaper.RouteRows FLatticePaper.C2Axial
  FLatticePaper.V2Minus

/-- **The route genuine structure of the canonical policy**, from the parts. -/
theorem routeGenuine_of_parts {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop} {η : ℤ}
    (C : CanonicalSignedPolicy frame G η) (hη : η = 1 ∨ η = -1)
    (hP : frame.Packet G)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G)
    (hdeck : ∀ (i j : ℤ) (x u : Site), C.policy x u ↔
      C.policy (x + frame.child.modifiedDeck.combine i j) (u + frame.child.modifiedDeck.combine i j))
    (hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0)
    (W : OldPolicyWitness frame G seed η) (hW : W.retained = C.policy) (hs : ∀ y i, ¬ seed y i)
    (hsig : ∀ w ∈ frame.closedPolygon, G w - G (w - frame.shortShift) ≤ 0)
    (hAS : ∀ K : ℕ, 2 ≤ K → frame.child.den + 2 * frame.child.num - 1 ≤ frame.child.num * (K : ℤ) →
      2 * frame.child.num * (K : ℤ) ≤ 3 * frame.child.den + 3 * frame.child.num - 1 →
      ∃ p q : ℤ, frame.child.num * p - frame.child.den * q = 2 - frame.child.num ∧
        ∀ k : ℕ, k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ G (p + (k : ℤ), q + (k : ℤ)))
    (hsym : ∀ y, G (FLatticePaper.ReflectedFan.reflH frame y) = G y)
    (hper : HasGeneratorPeriods frame.child G 0 frame.coherentConstantV)
    (hslip : ∀ z ∈ frame.closedPolygon, 0 ≤ frame.slip G 1 z)
    (hseed : ∀ z : Site, EvenSite z → frame.tGrade z = 2 - (frame.child.den + frame.child.num) → G z = 0)
    (hIsym : ∀ z : Site, G (FLatticePaper.W1Strips.iRefl z) = G z)
    (hlow : ∀ x : Site, ¬ EvenSite x → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade x →
      frame.sGrade x ≤ 1 - 2 * frame.child.den → G x = harmonicGrid x)
    (hup : ∀ x : Site, ¬ EvenSite x → frame.child.den + frame.child.num - 2 < frame.sGrade x →
      frame.sGrade x ≤ 3 * frame.child.den + frame.child.num - 2 → G x = harmonicGrid x)
    (hQ37 : ∀ z ∈ frame.freeH, EvenSite z → (z.1 - 1, z.2) ∈ frame.freeH → frame.tGrade z ≤ frame.child.den →
      laplacian G (z.1, z.2 + 1) = 0)
    (hprice : ∀ z ∈ frame.closedPolygon, frame.cutPrice - 1 ≤ frame.price G z ∧ frame.price G z ≤ frame.cutPrice)
    (hdrU : ∀ z, frame.price G (z + frame.child.modifiedDeck.kernel) = frame.price G z - 1)
    (hdrV : ∀ z, frame.price G (z + frame.child.modifiedDeck.transverse) = frame.price G z)
    (hperK : ∀ z : Site, G (z + (frame.child.den, frame.child.num)) = G z)
    (hv3plus : η = 1 → frame.child.den < 2 * frame.child.num → ∀ z ∈ frame.freeV, ¬ (η = -1 ∧ z = (0, 1)) →
      laplacian G z = 0 → ¬ EvenSite z → (z.1, z.2 - -η) ∈ frame.freeV →
      (laplacian G (z.1 - -η, z.2 - -η) = -1 ∨ C.policy (z.1 - -η, z.2 - -η) (z.1 - -η, z.2))) :
    RouteGenuine C := by
  have hS : frame.HasStrips G := hP.strips
  have hK : frame.child.modifiedDeck.combine 1 0 = (frame.child.den, frame.child.num) := combine_one_zero frame
  have hV : frame.child.modifiedDeck.combine 0 1 = (frame.child.num - frame.child.den, frame.child.num + frame.child.den) :=
    combine_zero_one frame
  have hdU : ∀ x u, C.policy x u ↔ C.policy (x + (frame.child.den, frame.child.num)) (u + (frame.child.den, frame.child.num)) := by
    intro x u
    have h := hdeck 1 0 x u
    rw [hK] at h
    exact h
  have hdV : ∀ x u, C.policy x u ↔ C.policy (x + (frame.child.num - frame.child.den, frame.child.num + frame.child.den))
      (u + (frame.child.num - frame.child.den, frame.child.num + frame.child.den)) := by
    intro x u
    have h := hdeck 0 1 x u
    rw [hV] at h
    exact h
  have F := FLatticePaper.EndpointStrips.endpointFacts_of_strips hS
  have h3 : ∀ z ∈ frame.freeH, z ≠ (2, 0) → laplacian G z = 0 → EvenSite z → (z.1 - 1, z.2) ∈ frame.freeH →
      (laplacian G (z.1 - 1, z.2) = -1 ∨ C.policy (z.1 - 1, z.2) (z.1 - 1, z.2 + 1)) ∧
      (laplacian G (z.1 - 1, z.2 + 1) = -1 ∨ C.policy (z.1 - 1, z.2 + 1) (z.1, z.2 + 1)) ∧
      (laplacian G (z.1, z.2 + 1) = -1 ∨ C.policy (z.1, z.2 + 1) z) := by
    intro z hz hz2 hw hev hq
    have hodd : ¬ EvenSite (z.1 - 1, z.2) := by
      unfold EvenSite at hev ⊢
      simp only at hev ⊢
      omega
    have hne : (z.1 - 1, z.2) ≠ FLatticePaper.Induction.hFirst := by
      intro h
      apply hz2
      have h1 : (z.1 - 1, z.2).1 = FLatticePaper.Induction.hFirst.1 := by rw [h]
      have h2 : (z.1 - 1, z.2).2 = FLatticePaper.Induction.hFirst.2 := by rw [h]
      unfold FLatticePaper.Induction.hFirst at h1 h2
      dsimp only at h1 h2
      exact Prod.ext (by omega) (by omega)
    refine ⟨h3_arrow_a C hbin hq hodd hne, ?_, h3_arrow_c C hW1 hbin hz hev hq⟩
    by_cases hd : 3 * frame.child.num - 2 ≤ frame.child.den
    · exact Or.inr (h3_arrow_north C W hW hP hsig hAS hW1 hd hz hev hq hz2)
    · have hm' := FLatticePaper.HMidStrict.m_strict frame hz hev hz2 hq
      have hpw : laplacian G (z.1, z.2 + 1) = 0 := by
        by_cases ht : frame.child.den + 1 ≤ frame.tGrade z
        · exact HEasyP.lap_p_zero_of_free hS hz hev ht
        · exact hQ37 z hz hev hq (by omega)
      exact h3_arrow_easy C hW1 hbin hz hev hm' hpw
  have v3 : ∀ z ∈ frame.freeV, ¬ (η = -1 ∧ z = (0, 1)) → laplacian G z = 0 → ¬ EvenSite z →
      (z.1, z.2 - -η) ∈ frame.freeV →
      (laplacian G (z.1, z.2 - -η) = -1 ∨ C.policy (z.1, z.2 - -η) (z.1 - -η, z.2 - -η)) ∧
      (laplacian G (z.1 - -η, z.2 - -η) = -1 ∨ C.policy (z.1 - -η, z.2 - -η) (z.1 - -η, z.2)) ∧
      (laplacian G (z.1 - -η, z.2) = -1 ∨ C.policy (z.1 - -η, z.2) z) := by
    intro z hz hne hw hodd hq
    have hmid : laplacian G (z.1 - -η, z.2 - -η) = -1 ∨ C.policy (z.1 - -η, z.2 - -η) (z.1 - -η, z.2) := by
      by_cases hd2 : 2 * frame.child.num ≤ frame.child.den
      · rcases hη with rfl | rfl
        · have hnb : (z.1, z.2 + 1) ∈ frame.freeV := by simpa using hq
          have h := v3_arrow_plus_easy C hW1 hbin hS hlow hup hd2 hz hodd hnb
          simpa using h
        · have hnb : (z.1, z.2 - 1) ∈ frame.freeV := by simpa using hq
          have h := v3_arrow_minus_easy C hW1 hP hbin hdeck hS hlow hup hd2 hz hodd hnb
          simpa using h
      · rcases hη with rfl | rfl
        · exact hv3plus rfl (by omega) z hz hne hw hodd hq
        · have hne' : z ≠ (0, 1) := fun h => hne ⟨rfl, h⟩
          have h := FLatticePaper.V3HardNW.v3_mid_minus_hard C hP hprice hdrU hdrV hW1 hperK hbin
            (by omega) hz hodd hq hne'
          simpa using h
    have hlast : laplacian G (z.1 - -η, z.2) = -1 ∨ C.policy (z.1 - -η, z.2) z := by
      rcases hη with rfl | rfl
      · have hnb : (z.1, z.2 + 1) ∈ frame.freeV := by simpa using hq
        have h := v3_last_plus C hW1 hbin hz hodd hw hnb
        simpa using h
      · have h := v3_last_minus C hP hW1 hbin hdU hz hodd
        simpa using h
    exact ⟨v3_arrow_a0 C hbin hη hodd hne hq, hmid, hlast⟩
  have rH1 : (η = 1 → (laplacian G (1, 0) = -1 ∨ C.policy (1, 0) (1, -1)) ∧
        (laplacian G (1, -1) = -1 ∨ C.policy (1, -1) (2, -1))) ∧
      (η = -1 → (laplacian G (1, 0) = -1 ∨ C.policy (1, 0) (1, 1)) ∧
        (laplacian G (2, 1) = -1 ∨ C.policy (2, 1) (2, 0))) :=
    ⟨rH1_plus_fields C hdV F, fun h => ⟨rH1_minus_first C F h, rH1_minus_second' C hP hW1 hbin F⟩⟩
  have rVprev : η = 1 → (laplacian G (1, -1) = -1 ∨ C.policy (1, -1) (2, -1)) ∧
      (laplacian G (2, -2) = -1 ∨ C.policy (2, -2) (1, -2)) :=
    fun h => ⟨rVprev_plus_first C hdV F h, rVprev_plus_second' C hP hW1 hbin F⟩
  exact
    { h1 := RouteH1Field.h1_field hP hsig hAS hsym hW1 hper hslip hseed hIsym C W hW hs
      h2 := h2_C2 C hW1 hP hdeck hbin
      h3 := h3
      v2 := v2_field C hW1 hP hdeck hbin hη
      v3 := v3
      rH0 := rH0_fields C hdU hdV F
      rHlast := rHlast_fields' C hP hW1 hbin hdU F
      rH1 := rH1
      rV1 := rV1_fields C F
      rVprev := rVprev }

end FLatticePaper.RouteAssembly
