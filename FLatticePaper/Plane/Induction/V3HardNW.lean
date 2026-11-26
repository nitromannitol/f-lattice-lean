import FLatticePaper.Plane.Induction.OddVNWFan
import FLatticePaper.Plane.Induction.VZeroS
import FLatticePaper.Plane.Induction.CanonForced

/-! # The forced arrow of the rotated NW fan for the `v3` middle (`η = −1`, `d < 2n`)

The arrow part of `OddVNWFan.parentSquareOut_oddV_NW_fan_rot`: the rotated fan at `start = (z.2, 1 − z.1)` forces the edge
`(z.1 − 1, z.2 − 1) → (z.1 − 1, z.2)`, the middle arrow of the `v3` row for `η = −1`. It needs the source's `s`-grade nonzero
(`hPs`), which is the case `z ≠ (0,1)` of the field. -/

namespace FLatticePaper.V3HardNW

open FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.W1 FLatticePaper.W1NonfreeOut
open FLatticePaper.RotatedForced FLatticePaper.RotatedCap FLatticePaper.CapConeGrades

theorem nw_arrow_rot {fr : ChildFrame} {G : Field}
    (hP : fr.Packet G)
    (hprice : ∀ z ∈ fr.closedPolygon, fr.cutPrice - 1 ≤ fr.price G z ∧ fr.price G z ≤ fr.cutPrice)
    (hdrU : ∀ z, fr.price G (z + fr.child.modifiedDeck.kernel) = fr.price G z - 1)
    (hdrV : ∀ z, fr.price G (z + fr.child.modifiedDeck.transverse) = fr.price G z)
    (hW1 : FLatticePaper.W1.W1Forced fr.child.num fr.child.den G)
    (hper : ∀ z : Site, G (z + (fr.child.den, fr.child.num)) = G z)
    (N D : ℤ) (hN2 : 2 * N = fr.child.den - fr.child.num) (hD2 : 2 * D = fr.child.den + fr.child.num)
    (hN0 : 0 < N) (hNDlt : N < D) (hreg : fr.child.den < 2 * fr.child.num)
    {z : Site} (hz : z ∈ fr.freeV) (hodd : ¬ EvenSite z)
    (hPfree : (z.1, z.2 - 1) ∈ fr.freeV)
    (hPs : fr.sGrade (z.1, z.2 - 1) ≠ 0) :
    FLatticePaper.SquareClauses.ForcedEdge G (fun _ _ => False) (z.1 - 1, z.2 - 1) (z.1 - 1, z.2) := by
  obtain ⟨hn1, hnd, hdn, hd3, hPT⟩ := fr.child_facts
  have hz0 := hz
  have hPfree0 := hPfree
  have hev : (fr.child.num + fr.child.den) % 2 = 0 := fr.child_even
  have hnum := FLatticePaper.FanInputs.num_odd fr
  have hodd' : (D + N) % 2 = 1 := by omega
  have hPeven : EvenSite (z.1, z.2 - 1) := by
    unfold EvenSite at hodd ⊢
    dsimp only
    omega
  -- the closed polygon at `P` (even) and at `z` (odd)
  simp only [FLatticePaper.Induction.ChildFrame.freeV, Set.mem_setOf_eq] at hPfree hz
  obtain ⟨hPE, -, -⟩ := hPfree
  obtain ⟨hzE, -, hVz⟩ := hz
  rw [FLatticePaper.Induction.mem_closedPolygon_iff, if_pos hPeven] at hPE
  rw [FLatticePaper.Induction.mem_closedPolygon_iff, if_neg hodd] at hzE
  have hsz' : fr.sGrade z = fr.sGrade (z.1, z.2 - 1) + 2 * N := by
    have e1 : fr.sGrade z = (fr.child.den + fr.child.num) * z.1 + (fr.child.den - fr.child.num) * z.2 := rfl
    have e2 : fr.sGrade (z.1, z.2 - 1)
        = (fr.child.den + fr.child.num) * z.1 + (fr.child.den - fr.child.num) * (z.2 - 1) := rfl
    have h2 : fr.child.den - fr.child.num = 2 * N := by omega
    rw [e1, e2, h2]
    ring
  have hsid : fr.sGrade z = 2 * (N * z.2 + D * z.1) := by
    have e : fr.sGrade z = (fr.child.den + fr.child.num) * z.1 + (fr.child.den - fr.child.num) * z.2 := rfl
    have h1 : fr.child.den + fr.child.num = 2 * D := by omega
    have h2 : fr.child.den - fr.child.num = 2 * N := by omega
    rw [e, h1, h2]
    ring
  have hsPeven : fr.sGrade (z.1, z.2 - 1) % 2 = 0 := by
    have e : fr.sGrade (z.1, z.2 - 1) = 2 * (N * z.2 + D * z.1) - 2 * N := by
      have h := hsz'
      omega
    rw [e]
    omega
  have hs0 : 0 ≤ fr.sGrade (z.1, z.2 - 1) := hPE.2.2.1
  have hsP2 : 2 ≤ fr.sGrade (z.1, z.2 - 1) := by omega
  have hs2 : 2 ≤ fr.sGrade z := by omega
  have hsL : fr.sGrade z ≤ fr.child.den + fr.child.num - 2 := by
    unfold FLatticePaper.Induction.ChildFrame.vSpectrum at hVz
    rcases hVz.2 with h | h <;> omega
  have hR : resRegion fr.child.num fr.child.den (z.2, 1 - z.1) :=
    resRegion_start_of_box fr hodd hzE hVz
  obtain ⟨K, hK2, hKs, hKr⟩ := K_bounds_rot (N := N) (D := D) (by omega) (by omega)
  have hstart := nw_start_mem hP hprice hdrU hdrV N D hN2 hD2 hN0 hNDlt hodd hs2 hsL hR K hK2
  have hb : N + 1 ≤ N * (z.2, -z.1).1 - D * (z.2, -z.1).2 := by
    dsimp only
    linarith [hsid, hsz', hsP2]
  have heven : EvenSite (z.2, 1 - z.1) := by
    unfold EvenSite at hodd ⊢
    dsimp only
    omega
  obtain ⟨arrow, hlap⟩ := rotated_fan_arrow_G hP hprice hdrU hdrV hW1 hper N D hN2 hD2 hN0 hNDlt hodd' K hK2 hKs hKr
    (z.2, -z.1) (z.2, 1 - z.1) hb hstart heven hR
  have eR : Zs (z.2, 1 - z.1) = (z.1 - 1, z.2 - 1) := by
    unfold Zs
    refine Prod.ext ?_ ?_
    all_goals simp only
    all_goals omega
  have eQ : Zs (incomingPos (z.2, 1 - z.1)) = (z.1 - 1, z.2) := by
    unfold incomingPos
    rw [if_pos heven]
    unfold Zs
    refine Prod.ext ?_ ?_
    all_goals simp only
    all_goals omega
  rw [eR] at hlap
  rw [eR, eQ] at arrow
  exact arrow

/-- **The `v3` middle for `η = −1` when `d < 2n`**: `(z.1 − 1, z.2 − 1) → (z.1 − 1, z.2)`, kept by the canonical policy: the white
middle is the forced arrow of the rotated NW fan (`nw_arrow_rot`), whose hypothesis `s(z.1, z.2 − 1) ≠ 0` holds unless `z = (0, 1)`
(`VZeroS.origin_of_s_zero`). -/
theorem v3_mid_minus_hard {fr : ChildFrame} {G : Field} (C : CanonicalSignedPolicy fr G (-1))
    (hP : fr.Packet G)
    (hprice : ∀ z ∈ fr.closedPolygon, fr.cutPrice - 1 ≤ fr.price G z ∧ fr.price G z ≤ fr.cutPrice)
    (hdrU : ∀ z, fr.price G (z + fr.child.modifiedDeck.kernel) = fr.price G z - 1)
    (hdrV : ∀ z, fr.price G (z + fr.child.modifiedDeck.transverse) = fr.price G z)
    (hW1 : FLatticePaper.W1.W1Forced fr.child.num fr.child.den G)
    (hper : ∀ z : Site, G (z + (fr.child.den, fr.child.num)) = G z)
    (hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0)
    (hreg : fr.child.den < 2 * fr.child.num)
    {z : Site} (hz : z ∈ fr.freeV) (hodd : ¬ EvenSite z) (hPfree : (z.1, z.2 - 1) ∈ fr.freeV)
    (hne : z ≠ (0, 1)) :
    laplacian G (z.1 - 1, z.2 - 1) = -1 ∨ C.policy (z.1 - 1, z.2 - 1) (z.1 - 1, z.2) := by
  obtain ⟨hn0, hnd, hd2, -, -⟩ := fr.child_facts
  obtain ⟨hnO, hdO⟩ := fr.child_odd
  have hPeven : EvenSite (z.1, z.2 - 1) := by
    unfold EvenSite at hodd ⊢
    simp only at hodd ⊢
    omega
  obtain ⟨N, hN2⟩ : ∃ N : ℤ, 2 * N = fr.child.den - fr.child.num := ⟨(fr.child.den - fr.child.num) / 2, by omega⟩
  obtain ⟨D, hD2⟩ : ∃ D : ℤ, 2 * D = fr.child.den + fr.child.num := ⟨(fr.child.den + fr.child.num) / 2, by omega⟩
  have hPs : fr.sGrade (z.1, z.2 - 1) ≠ 0 := by
    intro h0
    have hPf := hPfree
    simp only [FLatticePaper.Induction.ChildFrame.freeV, Set.mem_setOf_eq] at hPf
    have hPE := hPf.1
    rw [FLatticePaper.Induction.mem_closedPolygon_iff, if_pos hPeven] at hPE
    have hcop : IsCoprime fr.child.num fr.child.den := fr.child_reduced
    have hTd : fr.child.periodDenominator = fr.child.den ^ 2 + 2 * fr.child.den * fr.child.num - fr.child.num ^ 2 := rfl
    rw [hTd] at hPE
    have hx := FLatticePaper.VZeroS.origin_of_s_zero hn0 (by omega) hnO hcop
      (by unfold EvenSite at hPeven; exact hPeven)
      (by unfold ChildFrame.sGrade at h0; linarith)
      (by unfold ChildFrame.tGrade at hPE; linarith [hPE.1])
      (by unfold ChildFrame.tGrade at hPE; linarith [hPE.2.1])
    apply hne
    have h1 : z.1 = 0 := by omega
    have h2 : z.2 = 1 := by omega
    exact Prod.ext h1 h2
  by_cases hb : laplacian G (z.1 - 1, z.2 - 1) = -1
  · exact Or.inl hb
  · right
    have hm0 : laplacian G (z.1 - 1, z.2 - 1) = 0 := (hbin _).resolve_left hb
    have hF := nw_arrow_rot hP hprice hdrU hdrV hW1 hper N D hN2 hD2 (by omega) (by omega) hreg hz hodd hPfree hPs
    exact FLatticePaper.CanonForced.canon_of_forced C hm0 hF

end FLatticePaper.V3HardNW
