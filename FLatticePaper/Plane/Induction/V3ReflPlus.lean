import FLatticePaper.Plane.Induction.V3HardNW
import FLatticePaper.Plane.Induction.WestEastOdd
import FLatticePaper.Plane.Induction.WestEast
import FLatticePaper.Plane.Induction.CentralForced
import FLatticePaper.Plane.Induction.VZeroS
import FLatticePaper.Plane.Induction.FreeVOrdinate
import FLatticePaper.Plane.Induction.CanonForced

/-! # The `v3` middle for `η = +1` when `d < 2n`, transported from the `η = −1` fan by the central reflection

For an odd free V root `z` with `z + (0,1) ≠ vLast`, the central reflection `z' = A − z` (`A = I + tr`) is an odd free V root whose
`η = −1` middle `z' − (1,1) → z' − (1,0)` carries, by `CentralForced.forcedEdge_cref` (with the `I`-symmetry of `G`), the forced
arrow `z + (1,1) → z + (1,0)`. That is the `η = +1` middle of `z`, which the canonical policy keeps when `z + (1,1)` is white. -/

namespace FLatticePaper.V3ReflPlus

open FLatticePaper FLatticePaper.Induction FLatticePaper.W1 FLatticePaper.CentralForced

/-- The forced arrow of the rotated NW fan at an odd free V root away from `(0,1)`. -/
theorem nw_forced_of_ne {fr : ChildFrame} {G : Field}
    (hP : fr.Packet G)
    (hprice : ∀ z ∈ fr.closedPolygon, fr.cutPrice - 1 ≤ fr.price G z ∧ fr.price G z ≤ fr.cutPrice)
    (hdrU : ∀ z, fr.price G (z + fr.child.modifiedDeck.kernel) = fr.price G z - 1)
    (hdrV : ∀ z, fr.price G (z + fr.child.modifiedDeck.transverse) = fr.price G z)
    (hW1 : FLatticePaper.W1.W1Forced fr.child.num fr.child.den G)
    (hper : ∀ z : Site, G (z + (fr.child.den, fr.child.num)) = G z)
    (hreg : fr.child.den < 2 * fr.child.num)
    {z : Site} (hz : z ∈ fr.freeV) (hodd : ¬ EvenSite z) (hPfree : (z.1, z.2 - 1) ∈ fr.freeV)
    (hne : z ≠ (0, 1)) :
    FLatticePaper.SquareClauses.ForcedEdge G (fun _ _ => False) (z.1 - 1, z.2 - 1) (z.1 - 1, z.2) := by
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
  exact FLatticePaper.V3HardNW.nw_arrow_rot hP hprice hdrU hdrV hW1 hper N D hN2 hD2 (by omega) (by omega) hreg hz hodd
    hPfree hPs

/-- **The `v3` middle for `η = +1` (`d < 2n`)**: `z + (1,1) → z + (1,0)`, transported from the `η = −1` forced arrow at `A − z`. -/
theorem v3_mid_plus_hard {frame : ChildFrame} {G : Field} (C : CanonicalSignedPolicy frame G 1)
    (hP : frame.Packet G)
    (hprice : ∀ z ∈ frame.closedPolygon, frame.cutPrice - 1 ≤ frame.price G z ∧ frame.price G z ≤ frame.cutPrice)
    (hdrU : ∀ z, frame.price G (z + frame.child.modifiedDeck.kernel) = frame.price G z - 1)
    (hdrV : ∀ z, frame.price G (z + frame.child.modifiedDeck.transverse) = frame.price G z)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G)
    (hper : ∀ z : Site, G (z + (frame.child.den, frame.child.num)) = G z)
    (hIsym : ∀ z : Site, G (FLatticePaper.W1Strips.iRefl z) = G z)
    (hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0)
    (hreg : frame.child.den < 2 * frame.child.num)
    {z : Site} (hz : z ∈ frame.freeV) (hodd : ¬ EvenSite z) (hnb : (z.1, z.2 + 1) ∈ frame.freeV)
    (hnbV : (z.1, z.2 + 1) ≠ frame.vLast) :
    laplacian G (z.1 + 1, z.2 + 1) = -1 ∨ C.policy (z.1 + 1, z.2 + 1) (z.1 + 1, z.2) := by
  by_cases hb : laplacian G (z.1 + 1, z.2 + 1) = -1
  · exact Or.inl hb
  · right
    have hm0 : laplacian G (z.1 + 1, z.2 + 1) = 0 := (hbin _).resolve_left hb
    have hevnb : EvenSite (z.1, z.2 + 1) := by
      unfold EvenSite at hodd ⊢
      simp only at hodd ⊢
      omega
    have hz' := FLatticePaper.WestEastOdd.cref_freeV_odd frame hz hodd
    have hodd' : ¬ EvenSite (cref (reflectionI + frame.child.modifiedDeck.transverse) z) :=
      fun h => hodd ((evenSite_cref (centre_even frame) z).mp h)
    have hPfree' : ((cref (reflectionI + frame.child.modifiedDeck.transverse) z).1,
        (cref (reflectionI + frame.child.modifiedDeck.transverse) z).2 - 1) ∈ frame.freeV := by
      have e : ((cref (reflectionI + frame.child.modifiedDeck.transverse) z).1,
          (cref (reflectionI + frame.child.modifiedDeck.transverse) z).2 - 1)
          = cref (reflectionI + frame.child.modifiedDeck.transverse) (z.1, z.2 + 1) := by
        refine Prod.ext rfl ?_
        unfold cref
        ring
      rw [e]
      by_cases hv : (z.1, z.2 + 1) = FLatticePaper.Induction.vFirst
      · have hvL : cref (reflectionI + frame.child.modifiedDeck.transverse) (z.1, z.2 + 1) = frame.vLast := by
          rw [hv, centre_eq]
          unfold cref FLatticePaper.Induction.vFirst ChildFrame.vLast
          ext <;> simp <;> ring
        rw [hvL]
        exact FLatticePaper.FreeVOrdinate.vLast_mem_freeV frame
      · exact (FLatticePaper.Induction.cref_freeV frame hnb hevnb hv hnbV).1
    have hne' : cref (reflectionI + frame.child.modifiedDeck.transverse) z ≠ (0, 1) := by
      intro h
      apply hnbV
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      simp only [cref] at h1 h2
      rw [centre_eq] at h1 h2
      unfold ChildFrame.vLast
      ext <;> simp <;> omega
    have hF := nw_forced_of_ne hP hprice hdrU hdrV hW1 hper hreg hz' hodd' hPfree' hne'
    have hI : ∀ y : Site, G (reflectionI - y) = G y := by
      intro y
      have h := hIsym y
      rw [FLatticePaper.W1Strips.iRefl_eq_sub] at h
      exact h
    have hlap : ∀ y : Site, laplacian G (cref (reflectionI + frame.child.modifiedDeck.transverse) y)
        = laplacian G y := fun y => lap_cref_centre frame hI hP.periods y
    have hT := forcedEdge_cref (centre_even frame) hlap hF
    have e1 : cref (reflectionI + frame.child.modifiedDeck.transverse)
        ((cref (reflectionI + frame.child.modifiedDeck.transverse) z).1 - 1,
          (cref (reflectionI + frame.child.modifiedDeck.transverse) z).2 - 1) = (z.1 + 1, z.2 + 1) := by
      unfold cref
      ext <;> simp <;> ring
    have e2 : cref (reflectionI + frame.child.modifiedDeck.transverse)
        ((cref (reflectionI + frame.child.modifiedDeck.transverse) z).1 - 1,
          (cref (reflectionI + frame.child.modifiedDeck.transverse) z).2) = (z.1 + 1, z.2) := by
      unfold cref
      ext
      · simp; ring
      · simp
    rw [e1, e2] at hT
    exact FLatticePaper.CanonForced.canon_of_forced C hm0 hT

end FLatticePaper.V3ReflPlus
