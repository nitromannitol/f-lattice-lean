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
import FLatticePaper.Plane.Induction.V3ReflPlus
import FLatticePaper.Plane.Induction.StripColours

/-! # The route genuine structure from its parts (assembly with explicit open hypotheses)

`RouteGenuine C` is assembled from the field lemmas. Three inputs are explicit hypotheses, each an open claim:
The `d ≥ 3n − 2` and `d ≥ 2n` cases of the middles are proved from the north fan and the easy-regime lemmas. -/

namespace FLatticePaper.RouteAssembly

open FLatticePaper FLatticePaper.Induction FLatticePaper.W1 FLatticePaper.W1Witness FLatticePaper.FreeRoutes
  FLatticePaper.EndpointRows FLatticePaper.RoutePresc FLatticePaper.RouteH3 FLatticePaper.RouteFan
  FLatticePaper.RouteH3Easy FLatticePaper.VEasy FLatticePaper.V3Last FLatticePaper.RouteRows FLatticePaper.C2Axial
  FLatticePaper.V2Minus

/-- **The easy-regime whiteness of `p` from the child's own lower even zero interval.** In the easy H regime `d < 3n - 2`, an even
free H root `z` with `t(z) ≤ d` whose west neighbour is free has `t(z) ≥ 2n` (the west neighbour is odd, so `t(z) = t(z - (1,0)) + n`),
so the far input `q = z + (0,2)` of `p = z + (0,1)` has `2 - L ≤ t(q) ≤ 1 - d`, and `G q = 0` by `W1Strips.even_zero_lower`. The ordinary
zero strip gives `G z = G p = 0`, so `p` is white. -/
theorem lap_p_zero_of_west {frame : ChildFrame} {G : Field}
    (hper : HasGeneratorPeriods frame.child G 0 frame.coherentConstantV) (hS : frame.HasStrips G)
    (hslip : ∀ z ∈ frame.closedPolygon, 0 ≤ frame.slip G 1 z)
    (hseed : ∀ z : Site, EvenSite z → frame.tGrade z = 2 - (frame.child.den + frame.child.num) → G z = 0)
    {z : Site} (hz : z ∈ frame.freeH) (hev : EvenSite z) (hq : (z.1 - 1, z.2) ∈ frame.freeH)
    (hd : frame.child.den < 3 * frame.child.num - 2) (ht : frame.tGrade z ≤ frame.child.den) :
    laplacian G (z.1, z.2 + 1) = 0 := by
  obtain ⟨hn0, hnd, hdn, hd3, -⟩ := frame.child_facts
  have hz' := hz
  simp only [ChildFrame.freeH, Set.mem_setOf_eq] at hz'
  obtain ⟨-, -, hsp⟩ := hz'
  unfold ChildFrame.hSpectrum at hsp
  have htz2 : 2 ≤ frame.tGrade z := by
    have hp := tGrade_parity frame z
    unfold EvenSite at hev
    rcases hsp with h | h <;> omega
  have hodd : ¬ EvenSite (z.1 - 1, z.2) := by
    unfold EvenSite at hev ⊢
    simp only at hev ⊢
    omega
  have htb : frame.tGrade (z.1 - 1, z.2) = frame.tGrade z - frame.child.num := by
    unfold ChildFrame.tGrade
    ring
  have htb_ge : frame.child.num ≤ frame.tGrade (z.1 - 1, z.2) := by
    have hq' := hq
    simp only [ChildFrame.freeH, Set.mem_setOf_eq] at hq'
    obtain ⟨-, -, hsq⟩ := hq'
    unfold ChildFrame.hSpectrum at hsq
    have hp := tGrade_parity frame (z.1 - 1, z.2)
    unfold EvenSite at hodd
    simp only at hodd hp
    rcases hsq with h | h <;> omega
  have ht2 : 2 * frame.child.num ≤ frame.tGrade z := by omega
  have htq : frame.tGrade (z.1, z.2 + 2) = frame.tGrade z - 2 * frame.child.den := by
    unfold ChildFrame.tGrade
    ring
  have htp : frame.tGrade (z.1, z.2 + 1) = frame.tGrade z - frame.child.den := by
    unfold ChildFrame.tGrade
    ring
  have hqev : EvenSite (z.1, z.2 + 2) := by
    unfold EvenSite at hev ⊢
    simp only at hev ⊢
    omega
  have hGq : G (z.1, z.2 + 2) = 0 :=
    FLatticePaper.W1Strips.even_zero_lower frame hper hS hslip hseed (z.1, z.2 + 2) hqev (by omega) (by omega)
  have hGz : G z = 0 := hS.1 z (by omega) (by omega)
  have hGp : G (z.1, z.2 + 1) = 0 := hS.1 (z.1, z.2 + 1) (by omega) (by omega)
  have hodd' : ¬ EvenSite (z.1, z.2 + 1) := by
    unfold EvenSite at hev ⊢
    simp only at hev ⊢
    omega
  have eN : incomingNeg (z.1, z.2 + 1) = z := by
    unfold incomingNeg
    rw [if_neg hodd']
    refine Prod.ext ?_ ?_ <;> simp
  have eP : incomingPos (z.1, z.2 + 1) = (z.1, z.2 + 2) := by
    unfold incomingPos
    rw [if_neg hodd']
    refine Prod.ext ?_ ?_
    · simp
    · simp
      omega
  unfold laplacian
  rw [eN, eP, hGz, hGq, hGp]
  ring

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
    (hprice : ∀ z ∈ frame.closedPolygon, frame.cutPrice - 1 ≤ frame.price G z ∧ frame.price G z ≤ frame.cutPrice)
    (hdrU : ∀ z, frame.price G (z + frame.child.modifiedDeck.kernel) = frame.price G z - 1)
    (hdrV : ∀ z, frame.price G (z + frame.child.modifiedDeck.transverse) = frame.price G z)
    (hperK : ∀ z : Site, G (z + (frame.child.den, frame.child.num)) = G z) :
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
        · exact lap_p_zero_of_west hper hS hslip hseed hz hev hq (by omega) (by omega)
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
        · by_cases hvl : (z.1, z.2 - -1) = frame.vLast
          · left
            have h := FLatticePaper.StripColours.lap_vLast_east frame hS hP.periods
            have e1 : z.1 - -1 = frame.vLast.1 + 1 := by
              have := congrArg Prod.fst hvl
              simp only at this
              omega
            have e2 : z.2 - -1 = frame.vLast.2 := by
              have := congrArg Prod.snd hvl
              simp only at this
              omega
            rw [e1, e2]
            exact h
          · have hnb : (z.1, z.2 + 1) ∈ frame.freeV := by simpa using hq
            have hnbV : (z.1, z.2 + 1) ≠ frame.vLast := by simpa using hvl
            have h := FLatticePaper.V3ReflPlus.v3_mid_plus_hard C hP hprice hdrU hdrV hW1 hperK hIsym hbin
              (by omega) hz hodd hnb hnbV
            simpa using h
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
