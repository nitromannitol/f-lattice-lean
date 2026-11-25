import FLatticePaper.Plane.Induction.ShapeOneGeom
import FLatticePaper.Plane.Induction.ReturnPrescribed
import FLatticePaper.Plane.Induction.ThreeEdgeSquare
import FLatticePaper.Plane.Induction.FreeAdjacency

/-! # The west arrows at a free H root (Q32 part (a))

For an odd free H root `z` (`n + 2 ≤ t(z)`, `z ≠ hLast`), the west point `w = z + W = (z.1 − 1, z.2)` is an even free H point (`freeH_west`):
its `t`-grade `t(z) − n` lies in the H spectrum, and its south neighbour is outside the closed polygon. Its laplacian is zero (`white_west`):
`F = 0` at `w`, `w − E`, `w + E` in the zero strip. Hence:
* `EdgeP (z+W) z`: `z+W` is a free white with prescription `E` (`prescribedH_even`), so it retains `z` (`e3`);
* `EdgeP (z+SW) (z+W)`: the odd `z+SW` keeps both inputs if black, and if white selects its forced input, which is `z+W` by free adjacency
  (`edgeOK_of_free_input`; the forced existence at the white `z+SW` is the named `hFw`);
* `EdgeP (z+S) (z+SW)`: the fan designation `e1` (named; the reflected contact fan of the west side). -/

namespace FLatticePaper.WestArrows

open FLatticePaper FLatticePaper.Induction FLatticePaper.ShortRoute FLatticePaper.SquareClauses FLatticePaper.W1NonfreeOut FLatticePaper.W1FreeHfree FLatticePaper.ReturnTable
  FLatticePaper.ReturnPrescribed FLatticePaper.FreeAdjacency FLatticePaper.ShapeOneGeom FLatticePaper.ThreeEdgeSquare

theorem freeH_west {frame : ChildFrame} {z : Site} (hz : z ∈ frame.freeH) (hodd : ¬ EvenSite z)
    (hne : z ≠ frame.hLast) (hbt : frame.child.num + 2 ≤ frame.tGrade z) :
    (z.1 - 1, z.2) ∈ frame.freeH := by
  have ht := freeH_tGrade_add_two_le frame hz hodd hne
  obtain ⟨hs1, hs2⟩ := freeH_sGrade_bounds frame hz
  obtain ⟨hn1, hnd, hdn, hd3, hP⟩ := frame.child_facts
  have hev : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  have hPpos : 0 ≤ frame.child.periodDenominator := by
    rw [hP]
    nlinarith
  have hwe : EvenSite (z.1 - 1, z.2) := by
    unfold EvenSite at hodd ⊢
    simp only at hodd ⊢
    omega
  have htw : frame.tGrade (z.1 - 1, z.2) = frame.tGrade z - frame.child.num := by
    unfold ChildFrame.tGrade
    dsimp only
    ring
  have hsw : frame.sGrade (z.1 - 1, z.2) = frame.sGrade z - (frame.child.den + frame.child.num) := by
    unfold ChildFrame.sGrade
    dsimp only
    ring
  have hclosed : (z.1 - 1, z.2) ∈ frame.closedPolygon := by
    unfold ChildFrame.closedPolygon
    simp only [Set.mem_setOf_eq]
    rw [if_pos hwe]
    refine ⟨?_, ?_, ?_, ?_⟩
    · omega
    · omega
    · omega
    · omega
  have hnot : ((z.1 - 1, z.2).1, (z.1 - 1, z.2).2 - 1) ∉ frame.closedPolygon := by
    intro hmem
    unfold ChildFrame.closedPolygon at hmem
    simp only [Set.mem_setOf_eq] at hmem
    have hodd2 : ¬ EvenSite ((z.1 - 1, z.2).1, (z.1 - 1, z.2).2 - 1) := by
      unfold EvenSite at hodd ⊢
      simp only at hodd ⊢
      omega
    rw [if_neg hodd2] at hmem
    have hts : frame.tGrade (z.1 - 1, z.2 - 1) = frame.tGrade (z.1 - 1, z.2) + frame.child.den := by
      unfold ChildFrame.tGrade
      dsimp only
      ring
    obtain ⟨-, hmt2, -⟩ := hmem
    have hmt2' : frame.tGrade (z.1 - 1, z.2 - 1) ≤ frame.child.den := hmt2
    omega
  have hodd' : (z.1 + z.2) % 2 = 1 := by
    unfold EvenSite at hodd
    omega
  obtain ⟨a, c, ha, hc⟩ := FLatticePaper.PriceDeck.child_odd_witness frame
  have hpar : frame.tGrade (z.1 - 1, z.2) % 2 = 0 := by
    unfold ChildFrame.tGrade
    dsimp only
    rw [ha, hc]
    have key : (2 * a + 1) * (z.1 - 1) - (2 * c + 1) * z.2
        = 2 * (a * (z.1 - 1) - c * z.2) + ((z.1 - 1) - z.2) := by ring
    rw [key]
    generalize a * (z.1 - 1) - c * z.2 = K
    omega
  have hspec : frame.hSpectrum (frame.tGrade (z.1 - 1, z.2)) := Or.inl ⟨hpar, by omega, by omega⟩
  unfold ChildFrame.freeH
  exact ⟨hclosed, hnot, hspec⟩

/-- **The west point is white**: `F = 0` at `z+W` and its two horizontal inputs, by the zero strip (`t` of the three sites lies in `[1−d, n+2d−1]`). -/
theorem white_west {frame : ChildFrame} {F : Field} (hS : frame.HasStrips F) {z : Site}
    (hz : z ∈ frame.freeH) (hodd : ¬ EvenSite z) (hne : z ≠ frame.hLast)
    (hbt : frame.child.num + 2 ≤ frame.tGrade z) :
    laplacian F (z.1 - 1, z.2) = 0 := by
  have ht := freeH_tGrade_add_two_le frame hz hodd hne
  obtain ⟨hn1, hnd, hdn, hd3, hP⟩ := frame.child_facts
  have hwe : EvenSite (z.1 - 1, z.2) := by
    unfold EvenSite at hodd ⊢
    omega
  have hzt : frame.tGrade z = frame.child.num * z.1 - frame.child.den * z.2 := rfl
  have htw : frame.tGrade (z.1 - 1, z.2) = frame.tGrade z - frame.child.num := by
    unfold ChildFrame.tGrade
    dsimp only
    ring
  have htn : frame.tGrade (z.1 - 1 - 1, z.2) = frame.tGrade z - 2 * frame.child.num := by
    unfold ChildFrame.tGrade
    dsimp only
    ring
  have htp : frame.tGrade (z.1 - 1 + 1, z.2) = frame.tGrade z := by
    unfold ChildFrame.tGrade
    dsimp only
    ring
  have h0 : F (z.1 - 1, z.2) = 0 :=
    zero_of_tGrade hS (by omega) (by omega)
  have hp : F (z.1 - 1 + 1, z.2) = 0 :=
    zero_of_tGrade hS (by omega) (by omega)
  have hn : F (z.1 - 1 - 1, z.2) = 0 :=
    zero_of_tGrade hS (by omega) (by omega)
  unfold laplacian incomingNeg incomingPos
  simp only [if_pos hwe]
  rw [h0, hp, hn]
  ring

/-- **The prescription edge `z+W → z`** (the even endpoint `z+W` prescribes `E`). -/
theorem edge_west_prescription {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop} {η : ℤ}
    {z : Site} (hz : z ∈ frame.freeH) (hodd : ¬ EvenSite z) (hne : z ≠ frame.hLast)
    (hbt : frame.child.num + 2 ≤ frame.tGrade z) (hwlap : laplacian G (z.1 - 1, z.2) = 0) :
    EdgeP frame η G seed (z.1 - 1, z.2) z := by
  have ht := freeH_tGrade_add_two_le frame hz hodd hne
  have hwe : EvenSite (z.1 - 1, z.2) := by
    unfold EvenSite at hodd ⊢
    simp only at hodd ⊢
    omega
  have hfirst : (z.1 - 1, z.2) ≠ hFirst := by
    intro h
    apply hodd
    unfold hFirst at h
    simp only [Prod.mk.injEq] at h
    unfold EvenSite
    omega
  have hlast : (z.1 - 1, z.2) ≠ frame.hLast := by
    intro h
    unfold ChildFrame.hLast at h
    simp only [Prod.mk.injEq] at h
    have hzt : frame.tGrade z = frame.child.num * z.1 - frame.child.den * z.2 := rfl
    rw [hzt] at ht
    obtain ⟨hA, hB⟩ := h
    have hz1 : z.1 = frame.child.den + 1 := by omega
    have hz2 : z.2 = frame.child.num - 1 := by omega
    rw [hz1, hz2] at ht
    nlinarith [frame.child_facts]
  right
  left
  refine ⟨freeH_west hz hodd hne hbt, hwlap, ?_⟩
  rw [prescribedH_even η hwe hfirst hlast]
  exact Prod.ext (by simp) (by simp)

/-- **The adjacency edge `z+SW → z+W`**: the odd `z+SW` keeps both inputs if black, and selects its free white input `z+W` if white. -/
theorem edge_west_adjacency {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop} {η : ℤ}
    (P : FLatticePaper.W1Witness.OldPolicyWitness frame G seed η) (hs : ∀ y i, ¬ seed y i)
    {z : Site} (hz : z ∈ frame.freeH) (hodd : ¬ EvenSite z) (hne : z ≠ frame.hLast)
    (hbt : frame.child.num + 2 ≤ frame.tGrade z) (hwlap : laplacian G (z.1 - 1, z.2) = 0)
    (hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0)
    (hFsw : laplacian G (z.1 - 1, z.2 - 1) = 0 → ∃ i, ForcedEdge G seed (z.1 - 1, z.2 - 1) i) :
    EdgeP frame η G seed (z.1 - 1, z.2 - 1) (z.1 - 1, z.2) := by
  have hodd1 : ¬ EvenSite (z.1 - 1, z.2 - 1) := by
    unfold EvenSite at hodd ⊢
    simp only at hodd ⊢
    omega
  have hy : (z.1 - 1, z.2) = incomingNeg (z.1 - 1, z.2 - 1) ∨ (z.1 - 1, z.2) = incomingPos (z.1 - 1, z.2 - 1) := by
    refine Or.inr ?_
    unfold incomingPos
    rw [if_neg hodd1]
    exact Prod.ext rfl (by simp)
  left
  exact edgeOK_of_free_input P hs (hbin _) hFsw hy (Or.inl (freeH_west hz hodd hne hbt)) hwlap

/-- **The west three-edge return of a free H root** (Q32, part (a)): with the fan designation `he1 : z+S → z+SW` (named), the arrows
`z+SW → z+W` (adjacency) and `z+W → z` (prescription) are edges of the canonical policy, and `ParentSquareOut` holds at the root. -/
theorem parentSquareOut_of_freeH_west {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop} {η : ℤ}
    (hS : frame.HasStrips G)
    (P : FLatticePaper.W1Witness.OldPolicyWitness frame G seed η) (hs : ∀ y i, ¬ seed y i)
    (hpres : PrescribedAt frame G η P.retained)
    {z : Site} (hz : z ∈ frame.freeH) (hodd : ¬ EvenSite z) (hne : z ≠ frame.hLast)
    (hbt : frame.child.num + 2 ≤ frame.tGrade z) (hzw : laplacian G z = 0)
    (hwu : ∀ c j j', laplacian G c = 0 → P.retained c j → P.retained c j' → j = j')
    (hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0)
    (hFsw : laplacian G (z.1 - 1, z.2 - 1) = 0 → ∃ i, ForcedEdge G seed (z.1 - 1, z.2 - 1) i)
    (he1 : EdgeP frame η G seed (z.1, z.2 - 1) (z.1 - 1, z.2 - 1)) :
    ParentSquareOut G P.retained z := by
  have ht := freeH_tGrade_add_two_le frame hz hodd hne
  have hwlap : laplacian G (z.1 - 1, z.2) = 0 := white_west hS hz hodd hne hbt
  have hfirst : z ≠ hFirst := by
    intro h
    unfold hFirst at h
    have h1 : z.1 = 1 := congrArg Prod.fst h
    have h2 : z.2 = 0 := congrArg Prod.snd h
    have hzt : frame.tGrade z = frame.child.num * z.1 - frame.child.den * z.2 := rfl
    rw [hzt, h1, h2] at hbt
    omega
  have hlast : z ≠ frame.hLast := by
    intro h
    unfold ChildFrame.hLast at h
    have h1 : z.1 = frame.child.den := congrArg Prod.fst h
    have h2 : z.2 = frame.child.num - 1 := congrArg Prod.snd h
    have hzt : frame.tGrade z = frame.child.num * z.1 - frame.child.den * z.2 := rfl
    rw [hzt, h1, h2] at ht
    obtain ⟨hn1, -, -, -, -⟩ := frame.child_facts
    nlinarith
  have he2 := edge_west_adjacency P hs hz hodd hne hbt hwlap hbin hFsw
  have he3 := edge_west_prescription (η := η) (seed := seed) (G := G) hz hodd hne hbt hwlap
  have hR1 := edgeP_retained P.toOldPolicyData hpres he1
  have hR2 := edgeP_retained P.toOldPolicyData hpres he2
  have hR3 := edgeP_retained P.toOldPolicyData hpres he3
  exact parentSquareOut_of_freeH_root hpres hz hzw hodd hfirst hlast hwu hbin hR1 hR2 hR3

end FLatticePaper.WestArrows
