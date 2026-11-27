import FLatticePaper.Plane.Induction.PlusRowH
import FLatticePaper.Plane.Induction.PlusVm1
import FLatticePaper.Plane.Induction.PlusRowEndpoint
import FLatticePaper.Plane.Induction.RoutePlus
import FLatticePaper.Plane.Induction.ListForce

/-! # The plus prefix `V_{-r-1}, …, V_{-1}, H_0, V_0` is outside the restricted fort (eta = 1, easy regime)

The positions `0, …, r` of the plus row are `V_{-r-1}, …, V_{-1}`: the first `r` are removed by the route argument
(`ListForce.plus_removed_route` with `RoutePlus.plus_route_stays`); `V_{-1} = (1,-1)` by the tree of `PlusVm1` from `V_{-2}`;
position `r + 1` is `H_0` (white from `V_{-1}`) and position `r + 2` is `V_0` (white from `H_0`). The labels `V_{-1}` and `V_{-2}`
are the hypotheses `hv1`, `hv2`; the laplacians and free prescriptions are the endpoint inputs. -/

namespace FLatticePaper.PlusRowPrefix

open FLatticePaper FLatticePaper.Induction FLatticePaper.AuxRankQ1 FLatticePaper.FreeRows FLatticePaper.PlusRowWiring

/-- The site of the V label `V (-r-1+i)` in the plus site list, for `i ≤ r`. -/
theorem plusSites_Vneg (frame : ChildFrame) (r : ℤ) (i : ℕ) (hi : (i : ℤ) ≤ r) :
    (plusSites frame r)[i]? = some (RowAt.vAt frame (-r - 1 + (i : ℤ))) := by
  unfold plusSites rowSites
  rw [List.getElem?_map, plusRow_get_Vneg r _ _ i hi]
  simp [labelSite]

/-- The H label `H_0` sits at position `r + 1` of the plus row. -/
theorem plusRow_get_H0 (r L d : ℤ) :
    (plusRow r L d)[(r + 1).toNat]? = some (FreeLabel.H 0) := by
  unfold plusRow
  rw [List.getElem?_append_left (by simp only [List.length_append, List.length_map, List.length_range,
    List.length_cons, List.length_nil]; omega)]
  rw [List.getElem?_append_left (by simp only [List.length_append, List.length_map, List.length_range,
    List.length_cons, List.length_nil]; omega)]
  rw [List.getElem?_append_right (by simp only [List.length_map, List.length_range]; omega)]
  have hsub : (r + 1).toNat - ((List.range (r + 1).toNat).map fun i : ℕ => FreeLabel.V (-r - 1 + (i : ℤ))).length = 0 := by
    simp only [List.length_map, List.length_range]
    omega
  rw [hsub]
  simp

/-- The site list at `r + 2` is `V_0`, the site `(0,0)`. -/
theorem plusSites_V0 (frame : ChildFrame) (r : ℤ) (hL0 : (0 : ℤ) < frame.child.den + frame.child.num) :
    (plusSites frame r)[(r + 1).toNat + 1]? = some ((0 : ℤ), (0 : ℤ)) := by
  unfold plusSites rowSites
  rw [List.getElem?_map, plusRow_get_V0 r _ _]
  have hv : RowAt.vAt frame 0 = ((0 : ℤ), (0 : ℤ)) := by
    have h := RowAt.vAt_nat frame 0 (by omega)
    simp only [Nat.cast_zero] at h
    rw [h, VChain.vpath_zero]
    rfl
  simp only [Option.map_some, labelSite, hv]

/-- The site list at `r + 1` is the site `(1,0)` of `H_0`. -/
theorem plusSites_H0 (frame : ChildFrame) (r : ℤ) :
    (plusSites frame r)[(r + 1).toNat]? = some ((1 : ℤ), (0 : ℤ)) := by
  unfold plusSites rowSites
  rw [List.getElem?_map, plusRow_get_H0 r _ _]
  simp only [Option.map_some, labelSite]
  rw [RowAt.hAt_zero frame, HChain.hpath_zero]
  rfl

/-- **The plus prefix is outside the restricted fort.** The positions `0, …, r + 2` of the plus row are `V_{-r-1}, …, V_{-1},
H_0, V_0`. -/
theorem plus_prefix_removed (frame : ChildFrame) (F : Field) (hP : frame.Packet F) (r : ℤ) (hr1 : 1 ≤ r)
    (hrL2 : r ≤ frame.child.den + frame.child.num - 2)
    (hpat : ∀ k : ℕ, (k : ℤ) < frame.child.den + frame.child.num →
      frame.roundedSlip F 1 (VChain.vpath frame k) =
        if (k : ℤ) ≤ frame.child.den + frame.child.num - r - 2 then 0 else 1)
    (hSwin : ∀ z : Site, 2 - 2 * frame.child.den ≤ frame.sGrade z →
      frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 2 → F z = harmonicGrid z)
    (hOwin : ∀ z : Site, ¬ EvenSite z → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade z →
      frame.sGrade z ≤ 3 * frame.child.den + frame.child.num - 2 → F z = harmonicGrid z)
    (hd : 2 * frame.child.num ≤ frame.child.den)
    (hv1 : RowAt.vAt frame (-1) = ((1 : ℤ), (-1 : ℤ))) (hv2 : RowAt.vAt frame (-2) = ((1 : ℤ), (-2 : ℤ)))
    (hw1 : laplacian F ((1 : ℤ), (-1 : ℤ)) = 0)
    (hp1 : FreePolicy.FreePresc frame 1 ((1 : ℤ), (-1 : ℤ)) ((2 : ℤ), (-1 : ℤ)))
    (hy : laplacian F ((2 : ℤ), (-1 : ℤ)) = -1) (hz : laplacian F ((2 : ℤ), (-2 : ℤ)) = 0)
    (hnfz : ¬ FreeClosure.freeClosure frame ((2 : ℤ), (-2 : ℤ)))
    (hwp : frame.price F ((2 : ℤ), (0 : ℤ)) ≤ frame.cutPrice)
    (hwj : frame.roundedSlip F 1 ((2 : ℤ), (0 : ℤ)) ≤ 0)
    (hwne : frame.price F ((2 : ℤ), (0 : ℤ)) ≠ frame.cutPrice ∨ frame.roundedSlip F 1 ((2 : ℤ), (0 : ℤ)) ≠ 0)
    (hw0 : laplacian F ((1 : ℤ), (0 : ℤ)) = 0)
    (hp0 : FreePolicy.FreePresc frame 1 ((1 : ℤ), (0 : ℤ)) ((1 : ℤ), (-1 : ℤ)))
    (hwV : laplacian F ((0 : ℤ), (0 : ℤ)) = 0)
    (hpV : FreePolicy.FreePresc frame 1 ((0 : ℤ), (0 : ℤ)) ((1 : ℤ), (0 : ℤ)))
    {S : Set Site} (hS : IsRestrictedFort F (permitsQ1 frame F 1) S)
    (hK : ∀ z ∈ S, frame.cutPrice ≤ frame.price F z + frame.roundedSlip F 1 z) :
    ∀ (j : ℕ) (e : Site), j < (r + 1).toNat + 2 → (plusSites frame r)[j]? = some e → e ∉ S := by
  have hr0 : 0 ≤ r := by omega
  have hrem := ListForce.plus_removed_route frame F hP r hr0 (by omega) hpat S hK
    (RoutePlus.plus_route_stays frame hSwin hOwin hd hS r hrL2)
  have hL0 : (0 : ℤ) < frame.child.den + frame.child.num := by
    obtain ⟨hn0, hnd, -, -, -⟩ := frame.child_facts
    omega
  -- positions below r: V_{-r-1}, …, V_{-2}, removed by the route
  have hVlow : ∀ j : ℕ, j < r.toNat → ∀ e : Site, (plusSites frame r)[j]? = some e → e ∉ S := by
    intro j hj e he
    rw [plusSites_Vneg frame r j (by omega)] at he
    have he' : e = RowAt.vAt frame (-r - 1 + (j : ℤ)) := (Option.some.inj he).symm
    rw [he']
    exact hrem j hj
  -- position r: V_{-1} = (1,-1)
  have hpos_m1 : (plusSites frame r)[r.toNat]? = some ((1 : ℤ), (-1 : ℤ)) := by
    have h := plusSites_Vneg frame r r.toNat (by omega)
    have hidx : (-r - 1 + ((r.toNat : ℕ) : ℤ)) = -1 := by omega
    rw [hidx, hv1] at h
    exact h
  have hVm1 : ((1 : ℤ), (-1 : ℤ)) ∉ S := by
    have hE : ∀ x, x ∈ earlierPlus frame r r.toNat → x ∉ S := by
      rintro x ⟨j, hj, hjx⟩
      exact hVlow j (by omega) x hjx
    have hv2mem : ((1 : ℤ), (-2 : ℤ)) ∈ earlierPlus frame r r.toNat := by
      refine ⟨r.toNat - 1, by omega, ?_⟩
      have h := plusSites_Vneg frame r (r.toNat - 1) (by omega)
      have hidx : (-r - 1 + (((r.toNat - 1 : ℕ)) : ℤ)) = -2 := by omega
      rw [hidx, hv2] at h
      exact h
    have href := PlusVm1.refuted_Vm1_plus frame F hw1 hp1 hy hz hnfz hwp hwj hwne
      (E := fun x => x ∈ earlierPlus frame r r.toNat) (C := fun _ => False) hv2mem
    exact RefuteTree.refuted_not_mem frame F (Or.inl rfl) hS hK (E := fun x => x ∈ earlierPlus frame r r.toNat)
      (C := fun _ => False) hE (fun x hx => hx.elim) _ href
  -- position r + 1: H_0 = (1,0), white from V_{-1}
  have hH0 : ((1 : ℤ), (0 : ℤ)) ∉ S := by
    have hV1mem : ((1 : ℤ), (-1 : ℤ)) ∈ earlierPlus frame r (r.toNat + 1) := ⟨r.toNat, by omega, hpos_m1⟩
    have hE : ∀ x, x ∈ earlierPlus frame r (r.toNat + 1) → x ∉ S := by
      rintro x ⟨j, hj, hjx⟩
      rcases (show j < r.toNat ∨ j = r.toNat by omega) with hjr | rfl
      · exact hVlow j hjr x hjx
      · rw [hpos_m1] at hjx
        have hx : x = ((1 : ℤ), (-1 : ℤ)) := (Option.some.inj hjx).symm
        rw [hx]
        exact hVm1
    have href := PlusRowEndpoint.refuted_H0_plus frame F hw0 hp0 (E := fun x => x ∈ earlierPlus frame r (r.toNat + 1))
      (C := fun _ => False) hV1mem
    exact RefuteTree.refuted_not_mem frame F (Or.inl rfl) hS hK (E := fun x => x ∈ earlierPlus frame r (r.toNat + 1))
      (C := fun _ => False) hE (fun x hx => hx.elim) _ href
  -- position r + 2: V_0 = (0,0), white from H_0
  have hV0 : ((0 : ℤ), (0 : ℤ)) ∉ S := by
    have hH0mem : ((1 : ℤ), (0 : ℤ)) ∈ earlierPlus frame r (r.toNat + 2) := ⟨r.toNat + 1, by omega, by
      rw [show r.toNat + 1 = (r + 1).toNat by omega]
      exact plusSites_H0 frame r⟩
    have hE : ∀ x, x ∈ earlierPlus frame r (r.toNat + 2) → x ∉ S := by
      rintro x ⟨j, hj, hjx⟩
      rcases (show j < r.toNat ∨ j = r.toNat ∨ j = r.toNat + 1 by omega) with hjr | rfl | rfl
      · exact hVlow j hjr x hjx
      · rw [hpos_m1] at hjx
        have hx : x = ((1 : ℤ), (-1 : ℤ)) := (Option.some.inj hjx).symm
        rw [hx]
        exact hVm1
      · rw [show r.toNat + 1 = (r + 1).toNat by omega, plusSites_H0 frame r] at hjx
        have hx : x = ((1 : ℤ), (0 : ℤ)) := (Option.some.inj hjx).symm
        rw [hx]
        exact hH0
    have href := PlusRowEndpoint.refuted_V0_plus frame F hwV hpV (E := fun x => x ∈ earlierPlus frame r (r.toNat + 2))
      (C := fun _ => False) hH0mem
    exact RefuteTree.refuted_not_mem frame F (Or.inl rfl) hS hK (E := fun x => x ∈ earlierPlus frame r (r.toNat + 2))
      (C := fun _ => False) hE (fun x hx => hx.elim) _ href
  intro j e hj he
  rcases (show j < r.toNat ∨ j = r.toNat ∨ j = r.toNat + 1 ∨ j = r.toNat + 2 by omega) with hjr | rfl | rfl | rfl
  · exact hVlow j hjr e he
  · rw [hpos_m1] at he
    have hx : e = ((1 : ℤ), (-1 : ℤ)) := (Option.some.inj he).symm
    rw [hx]
    exact hVm1
  · rw [show r.toNat + 1 = (r + 1).toNat by omega, plusSites_H0 frame r] at he
    have hx : e = ((1 : ℤ), (0 : ℤ)) := (Option.some.inj he).symm
    rw [hx]
    exact hH0
  · rw [show r.toNat + 2 = (r + 1).toNat + 1 by omega, plusSites_V0 frame r hL0] at he
    have hx : e = ((0 : ℤ), (0 : ℤ)) := (Option.some.inj he).symm
    rw [hx]
    exact hV0

end FLatticePaper.PlusRowPrefix
