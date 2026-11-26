import FLatticePaper.Plane.Induction.FortPairMin
import FLatticePaper.Plane.Induction.ListForce
import FLatticePaper.Plane.Induction.RouteStay
import FLatticePaper.Plane.Induction.RoutePlus

/-! # The easy-frame reduction of `RestrictedNoFort` for `permitsQ1`

Let `S` be a nonempty restricted fort of `permitsQ1` (sign `η = ±1`) in `{K ≥ level}`, `K = P + J_η`. The translate of `S` with
minimum `c₀` at the pair `(c₀, 0)` (`FortPairMin.exists_fort_translate_c0`) is again a restricted fort. On the easy frames
(`2 num ≤ den`) the route of each entry of the displayed list stays in the fort (`RouteStay.minus_route_stays`,
`RoutePlus.plus_route_stays`), so the removal lists (`ListForce.minus_removed_route`, `plus_removed_route`) and the candidate
lemmas (`minus_hcand_route`, `plus_hcand_route`) place every boundary point of the fort with `K ≥ c₀` at `H₀`, `V₀` (minus) or at
`H₀`, `V₋₁` (plus).

The named inputs are:
* `hpat`: the V pattern of the rounded slip, with break `r` (minus: `0` up to `r`, then `−1`; plus: `0` up to `den + num − r − 2`,
  then `1`);
* `hconf`: a restricted fort with `K ≥ c₀` lies in the closed polygon (plus: in `closedPolygon − plusV`);
* `hcore`: the `H₀`-core step. A restricted fort with `K ≥ c₀` in the closed polygon whose boundary points outside the open rectangle
  are `H₀` or `V₀` (minus) is empty. This is the restricted analogue of `H0Core.h0_core_minus`; it needs the interior no-fort of the
  Q1 game, which is not proved here.
* `hPH`, `hJH` (the free H cut: `P ≤ c₀` with equality only at `H₀`, and `J = 0`), `hS`, `hO` (the strips), `hd`, `hr0`, `hrL2`.

Nothing else is assumed. -/

namespace FLatticePaper.EasyNoFort

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.AuxRankQ1 FLatticePaper.FortPairMin FLatticePaper.RestrictedFortShift

/-! ### The minus sign (`η = −1`) -/

/-- **The minus fort is empty** (the candidates of the route, then the core). -/
theorem minus_fort_empty {F : Field} (frame : ChildFrame) (hP : frame.Packet F) (r : ℤ) (hr0 : 0 ≤ r)
    (hrL2 : r ≤ frame.child.den + frame.child.num - 2)
    (hPH : ∀ h : Site, frame.freeH h → frame.price F h ≤ frame.cutPrice ∧
      (frame.price F h = frame.cutPrice → h = FLatticePaper.Induction.hFirst))
    (hJH : ∀ h : Site, frame.freeH h → frame.roundedSlip F (-1) h = 0)
    (hpat : ∀ k : ℕ, (k : ℤ) < frame.child.den + frame.child.num →
      frame.roundedSlip F (-1) (VChain.vpath frame k) = if (k : ℤ) ≤ r then 0 else -1)
    (hS : ∀ z : Site, 2 - 2 * frame.child.den ≤ frame.sGrade z →
      frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 2 → F z = harmonicGrid z)
    (hO : ∀ z : Site, ¬ EvenSite z → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade z →
      frame.sGrade z ≤ 3 * frame.child.den + frame.child.num - 2 → F z = harmonicGrid z)
    (hd : 2 * frame.child.num ≤ frame.child.den)
    (hcore : ∀ S : Set Site, IsRestrictedFort F (permitsQ1 frame F (-1)) S →
      (∀ z ∈ S, frame.cutPrice ≤ frame.price F z + frame.roundedSlip F (-1) z) →
      (∀ z ∈ S, z ∈ frame.closedPolygon) →
      (∀ z ∈ S, ¬ frame.openRect z → z = FLatticePaper.Induction.hFirst ∨ z = FLatticePaper.Induction.vFirst) → S = ∅)
    {S : Set Site} (hR : IsRestrictedFort F (permitsQ1 frame F (-1)) S)
    (hK : ∀ z ∈ S, frame.cutPrice ≤ frame.price F z + frame.roundedSlip F (-1) z)
    (hsub : ∀ z ∈ S, z ∈ frame.closedPolygon) : S = ∅ := by
  have hroute := RouteStay.minus_route_stays frame hS hO hd hR r hrL2
  refine hcore S hR hK hsub ?_
  intro b hbS hbO
  exact ListForce.minus_hcand_route frame F hP r hr0 hrL2 hPH hJH hpat S hK hroute b hbS (hsub b hbS) hbO

/-- **`RestrictedNoFort` for `permitsQ1` at sign `−1`, on the easy frames.** -/
theorem restrictedNoFort_minus {F : Field} (frame : ChildFrame) (hP : frame.Packet F)
    (hPD : ∀ z, frame.price F (z + frame.child.modifiedDeck.kernel) = frame.price F z + -1 ∧
      frame.price F (z + frame.child.modifiedDeck.transverse) = frame.price F z + 0)
    (hSD : ∀ z, frame.slip F (-1) (z + frame.child.modifiedDeck.kernel) = frame.slip F (-1) z + 0 ∧
      frame.slip F (-1) (z + frame.child.modifiedDeck.transverse) = frame.slip F (-1) z + 2 * (-1))
    (r : ℤ) (hr0 : 0 ≤ r) (hrL2 : r ≤ frame.child.den + frame.child.num - 2)
    (hPH : ∀ h : Site, frame.freeH h → frame.price F h ≤ frame.cutPrice ∧
      (frame.price F h = frame.cutPrice → h = FLatticePaper.Induction.hFirst))
    (hJH : ∀ h : Site, frame.freeH h → frame.roundedSlip F (-1) h = 0)
    (hpat : ∀ k : ℕ, (k : ℤ) < frame.child.den + frame.child.num →
      frame.roundedSlip F (-1) (VChain.vpath frame k) = if (k : ℤ) ≤ r then 0 else -1)
    (hS : ∀ z : Site, 2 - 2 * frame.child.den ≤ frame.sGrade z →
      frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 2 → F z = harmonicGrid z)
    (hO : ∀ z : Site, ¬ EvenSite z → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade z →
      frame.sGrade z ≤ 3 * frame.child.den + frame.child.num - 2 → F z = harmonicGrid z)
    (hd : 2 * frame.child.num ≤ frame.child.den)
    (hconf : ∀ S : Set Site, IsRestrictedFort F (permitsQ1 frame F (-1)) S →
      (∀ z ∈ S, frame.cutPrice ≤ frame.price F z + frame.roundedSlip F (-1) z) →
      ∀ z ∈ S, z ∈ frame.closedPolygon)
    (hcore : ∀ S : Set Site, IsRestrictedFort F (permitsQ1 frame F (-1)) S →
      (∀ z ∈ S, frame.cutPrice ≤ frame.price F z + frame.roundedSlip F (-1) z) →
      (∀ z ∈ S, z ∈ frame.closedPolygon) →
      (∀ z ∈ S, ¬ frame.openRect z → z = FLatticePaper.Induction.hFirst ∨ z = FLatticePaper.Induction.vFirst) → S = ∅) :
    RestrictedNoFort F (fun z => frame.price F z + frame.roundedSlip F (-1) z) (permitsQ1 frame F (-1)) := by
  intro level S hne hres hlev
  obtain ⟨T, -, hfort, ⟨r', hr'S, -, -⟩, hK⟩ :=
    exists_fort_translate_c0 frame F (-1) (Or.inr rfl) hPD hSD (fun c i j => frame.laplacian_add_lattice hP i j c) hres hne
      level hlev
  have hempty := minus_fort_empty frame hP r hr0 hrL2 hPH hJH hpat hS hO hd hcore hfort hK (hconf _ hfort hK)
  simp [hempty] at hr'S

/-! ### The plus sign (`η = +1`) -/

/-- **The plus fort is empty** (the candidates `H₀`, `V₋₁` of `E − V`, then the core). -/
theorem plus_fort_empty {F : Field} (frame : ChildFrame) (hP : frame.Packet F) (r : ℤ) (hr0 : 0 ≤ r)
    (hr2 : r ≤ frame.child.den + frame.child.num - 2)
    (hPH : ∀ h : Site, frame.freeH h → frame.price F h ≤ frame.cutPrice ∧
      (frame.price F h = frame.cutPrice → h = FLatticePaper.Induction.hFirst))
    (hJH : ∀ h : Site, frame.freeH h → frame.roundedSlip F 1 h = 0)
    (hpat : ∀ k : ℕ, (k : ℤ) < frame.child.den + frame.child.num →
      frame.roundedSlip F 1 (VChain.vpath frame k) =
        if (k : ℤ) ≤ frame.child.den + frame.child.num - r - 2 then 0 else 1)
    (hS : ∀ z : Site, 2 - 2 * frame.child.den ≤ frame.sGrade z →
      frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 2 → F z = harmonicGrid z)
    (hO : ∀ z : Site, ¬ EvenSite z → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade z →
      frame.sGrade z ≤ 3 * frame.child.den + frame.child.num - 2 → F z = harmonicGrid z)
    (hd : 2 * frame.child.num ≤ frame.child.den)
    (hcore : ∀ S : Set Site, IsRestrictedFort F (permitsQ1 frame F 1) S →
      (∀ z ∈ S, frame.cutPrice ≤ frame.price F z + frame.roundedSlip F 1 z) →
      (∀ z ∈ S, (z.1 + (frame.child.num - frame.child.den), z.2 + (frame.child.num + frame.child.den)) ∈ frame.closedPolygon) →
      (∀ z ∈ S, ¬ frame.openRect (z.1 + (frame.child.num - frame.child.den), z.2 + (frame.child.num + frame.child.den)) →
        z = FLatticePaper.Induction.hFirst ∨ z = RowAt.vAt frame (-1)) → S = ∅)
    {S : Set Site} (hR : IsRestrictedFort F (permitsQ1 frame F 1) S)
    (hK : ∀ z ∈ S, frame.cutPrice ≤ frame.price F z + frame.roundedSlip F 1 z)
    (hsub : ∀ z ∈ S, (z.1 + (frame.child.num - frame.child.den), z.2 + (frame.child.num + frame.child.den)) ∈
      frame.closedPolygon) : S = ∅ := by
  have hroute := RoutePlus.plus_route_stays frame hS hO hd hR r hr2
  refine hcore S hR hK hsub ?_
  intro b hbS hnot
  have hw := hsub b hbS
  exact ListForce.plus_hcand_route frame F hP r hr0 hr2 hPH hJH hpat S hK hroute b hbS hw hnot

/-- **`RestrictedNoFort` for `permitsQ1` at sign `+1`, on the easy frames.** -/
theorem restrictedNoFort_plus {F : Field} (frame : ChildFrame) (hP : frame.Packet F)
    (hPD : ∀ z, frame.price F (z + frame.child.modifiedDeck.kernel) = frame.price F z + -1 ∧
      frame.price F (z + frame.child.modifiedDeck.transverse) = frame.price F z + 0)
    (hSD : ∀ z, frame.slip F 1 (z + frame.child.modifiedDeck.kernel) = frame.slip F 1 z + 0 ∧
      frame.slip F 1 (z + frame.child.modifiedDeck.transverse) = frame.slip F 1 z + 2 * 1)
    (r : ℤ) (hr0 : 0 ≤ r) (hr2 : r ≤ frame.child.den + frame.child.num - 2)
    (hPH : ∀ h : Site, frame.freeH h → frame.price F h ≤ frame.cutPrice ∧
      (frame.price F h = frame.cutPrice → h = FLatticePaper.Induction.hFirst))
    (hJH : ∀ h : Site, frame.freeH h → frame.roundedSlip F 1 h = 0)
    (hpat : ∀ k : ℕ, (k : ℤ) < frame.child.den + frame.child.num →
      frame.roundedSlip F 1 (VChain.vpath frame k) =
        if (k : ℤ) ≤ frame.child.den + frame.child.num - r - 2 then 0 else 1)
    (hS : ∀ z : Site, 2 - 2 * frame.child.den ≤ frame.sGrade z →
      frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 2 → F z = harmonicGrid z)
    (hO : ∀ z : Site, ¬ EvenSite z → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade z →
      frame.sGrade z ≤ 3 * frame.child.den + frame.child.num - 2 → F z = harmonicGrid z)
    (hd : 2 * frame.child.num ≤ frame.child.den)
    (hconf : ∀ S : Set Site, IsRestrictedFort F (permitsQ1 frame F 1) S →
      (∀ z ∈ S, frame.cutPrice ≤ frame.price F z + frame.roundedSlip F 1 z) →
      ∀ z ∈ S, (z.1 + (frame.child.num - frame.child.den), z.2 + (frame.child.num + frame.child.den)) ∈
        frame.closedPolygon)
    (hcore : ∀ S : Set Site, IsRestrictedFort F (permitsQ1 frame F 1) S →
      (∀ z ∈ S, frame.cutPrice ≤ frame.price F z + frame.roundedSlip F 1 z) →
      (∀ z ∈ S, (z.1 + (frame.child.num - frame.child.den), z.2 + (frame.child.num + frame.child.den)) ∈ frame.closedPolygon) →
      (∀ z ∈ S, ¬ frame.openRect (z.1 + (frame.child.num - frame.child.den), z.2 + (frame.child.num + frame.child.den)) →
        z = FLatticePaper.Induction.hFirst ∨ z = RowAt.vAt frame (-1)) → S = ∅) :
    RestrictedNoFort F (fun z => frame.price F z + frame.roundedSlip F 1 z) (permitsQ1 frame F 1) := by
  intro level S hne hres hlev
  obtain ⟨T, -, hfort, ⟨r', hr'S, -, -⟩, hK⟩ :=
    exists_fort_translate_c0 frame F 1 (Or.inl rfl) hPD hSD (fun c i j => frame.laplacian_add_lattice hP i j c) hres hne
      level hlev
  have hempty := plus_fort_empty frame hP r hr0 hr2 hPH hJH hpat hS hO hd hcore hfort hK (hconf _ hfort hK)
  simp [hempty] at hr'S

end FLatticePaper.EasyNoFort
