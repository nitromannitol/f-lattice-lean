import FLatticePaper.Construction.NativeCoverage
import FLatticePaper.Construction.PeriodExtension
import FLatticePaper.Plane.EndpointGrowth

namespace FLatticePaper.Construction

open Farey

/-- The endpoint heights in the constructor's occupied lower-left chart. -/
def EndpointAtom.planeField : EndpointAtom → Field
  | .zero => fun point => -chooseTwo point.2
  | .one => fun point => oneEndpoint (point + (0, 1))

def EndpointAtom.constantV : EndpointAtom → ℤ
  | .zero => 0
  | .one => -2

private theorem zeroAtom_laplacian (point : Site) :
    laplacian EndpointAtom.zero.planeField point = if EvenSite point then 0 else -1 := by
  have hfield (site : Site) : EndpointAtom.zero.planeField site = zeroEndpoint site + site.2 := by
    have h := chooseTwo_add site.2 1
    simp only [show chooseTwo (1 : ℤ) = 0 by decide, mul_one, add_zero] at h
    have hquad : site.2 * (site.2 + 1) / 2 = chooseTwo (site.2 + 1) := by
      unfold chooseTwo
      rw [add_sub_cancel_right, mul_comm site.2]
    simp only [EndpointAtom.planeField, zeroEndpoint, hquad, h]
    omega
  have hheight : (incomingNeg point).2 + (incomingPos point).2 = 2 * point.2 := by
    by_cases hp : EvenSite point
    · simp only [incomingNeg, incomingPos, if_pos hp]
      omega
    · simp only [incomingNeg, incomingPos, if_neg hp]
      omega
  rw [← laplacian_zeroEndpoint]
  simp only [laplacian, hfield]
  omega

private theorem oneAtom_laplacian (point : Site) :
    laplacian EndpointAtom.one.planeField point = if EvenSite point then -1 else 0 := by
  obtain ⟨x, y⟩ := point
  have h := laplacian_oneEndpoint (x, y + 1)
  by_cases he : EvenSite (x, y)
  · have hxy : (x + y) % 2 = 0 := he
    have hp : ¬ EvenSite (x, y + 1) := by change (x + (y + 1)) % 2 ≠ 0; omega
    simp only [laplacian, incomingNeg, incomingPos, if_neg hp, oneEndpoint] at h
    simp only [laplacian, incomingNeg, incomingPos, if_pos he, EndpointAtom.planeField, oneEndpoint,
      Prod.fst_add, Prod.snd_add, add_zero]
    rw [show y + 1 - (x - 1) = y + 1 + 1 - x by omega,
      show y + 1 - (x + 1) = y + 1 - 1 - x by omega]
    omega
  · have hxy : (x + y) % 2 ≠ 0 := he
    have hp : EvenSite (x, y + 1) := by change (x + (y + 1)) % 2 = 0; omega
    simp only [laplacian, incomingNeg, incomingPos, if_pos hp, oneEndpoint] at h
    simp only [laplacian, incomingNeg, incomingPos, if_neg he, EndpointAtom.planeField, oneEndpoint,
      Prod.fst_add, Prod.snd_add, add_zero]
    rw [show y - 1 + 1 - x = y + 1 - (x + 1) by omega,
      show y + 1 + 1 - x = y + 1 - (x - 1) by omega]
    omega

private theorem oneAtom_rank :
    IsBurningRank EndpointAtom.one.planeField (fun site => 2 * site.2 + (1 - (site.1 + site.2) % 2)) := by
  intro point
  rw [oneAtom_laplacian]
  by_cases he : EvenSite point
  · left
    refine ⟨if_pos he, ?_, ?_⟩
    all_goals simp only [incomingNeg, incomingPos, if_pos he]
    all_goals change (point.1 + point.2) % 2 = 0 at he
    all_goals omega
  · right
    refine ⟨if_neg he, Or.inl ?_⟩
    simp only [incomingNeg, if_neg he]
    change (point.1 + point.2) % 2 ≠ 0 at he
    omega

theorem EndpointAtom.planeField_periods (endpoint : EndpointAtom) :
    HasGeneratorPeriods endpoint.fraction endpoint.planeField 0 endpoint.constantV := by
  cases endpoint
  · constructor
    · intro site
      rw [show EndpointAtom.zero.fraction.modifiedDeck.kernel = ((2, 0) : Site) from rfl]
      simp only [EndpointAtom.planeField, Prod.snd_add, add_zero]
    · intro site
      change -chooseTwo (site.2 + 1) = -chooseTwo site.2 - (1 * site.2 - 0 * site.1) + 0
      have h := chooseTwo_add site.2 1
      rw [show chooseTwo (1 : ℤ) = 0 by decide] at h
      omega
  · constructor
    · intro site
      rw [show EndpointAtom.one.fraction.modifiedDeck.kernel = ((1, 1) : Site) from rfl]
      simp only [EndpointAtom.planeField, oneEndpoint, Prod.fst_add, Prod.snd_add, add_zero]
      rw [show site.2 + 1 + 1 - (site.1 + 1) = site.2 + 1 - site.1 by omega]
    · intro site
      rw [show EndpointAtom.one.fraction.modifiedDeck.transverse = ((0, 2) : Site) from rfl]
      simp only [EndpointAtom.planeField, oneEndpoint, Prod.fst_add, Prod.snd_add, add_zero,
        EndpointAtom.constantV, Fraction.transverseGrade, EndpointAtom.fraction, one_mul]
      rw [show (site.2 + 2 + 1 - site.1) ^ 2 =
          (site.2 + 1 - site.1) ^ 2 + (site.2 + 2 - site.1) * 4 by ring,
        Int.add_mul_ediv_right _ _ (by decide)]
      omega

theorem EndpointAtom.planeField_recurrent (endpoint : EndpointAtom) :
    Superharmonic endpoint.planeField ∧ Recurrent endpoint.planeField ∧
      HasQuadraticGrowth endpoint.planeField endpoint.fraction.matrix := by
  have hinterval : endpoint.fraction.InUnitInterval := by cases endpoint <;> exact ⟨by decide, by decide, by decide⟩
  refine ⟨?_, ?_, generator_periods_growth hinterval endpoint.planeField_periods⟩
  · cases endpoint
    · exact (isBurningRank_of_checkerboard zeroAtom_laplacian).superharmonic
    · exact oneAtom_rank.superharmonic
  · cases endpoint
    · exact (isBurningRank_of_checkerboard zeroAtom_laplacian).recurrent
    · exact oneAtom_rank.recurrent

theorem EndpointAtom.atOrigin_agrees (endpoint : EndpointAtom) :
    endpoint.atOrigin.val.Agrees endpoint.planeField 0 := by
  cases endpoint <;> unfold HeightTile.Agrees <;> decide +kernel

private theorem EndpointAtom.nonnegative_coordinates (endpoint : EndpointAtom) {point : Site}
    (hpoint : point ∈ endpoint.atOrigin.val.sites) : 0 ≤ point.1 ∧ 0 ≤ point.2 := by
  cases endpoint
  · exact ⟨(mem_maskedTile_sites _ _ _ _ |>.mp hpoint).1.1,
      (mem_maskedTile_sites _ _ _ _ |>.mp hpoint).2.1.1⟩
  · exact ⟨(mem_maskedTile_sites _ _ _ _ |>.mp hpoint).1.1,
      (mem_maskedTile_sites _ _ _ _ |>.mp hpoint).2.1.1⟩

/-- The attached endpoint atom returns to its exact occupied physical chart
after rectangular trim and final centering. -/
theorem EndpointAtom.attach_llCenter_agrees (endpoint : EndpointAtom) (standard : NonemptyTile) :
    ((endpoint.attach standard).llCenter).val.Agrees endpoint.planeField 0 := by
  let tile := endpoint.atOrigin.val
  let anchor := standard.val.lowerLeft standard.property
  have hone : (0 : Site) ∈ tile.sites := by
    change (0 : Site) ∈ endpoint.atOrigin.val.sites
    cases endpoint <;> decide +kernel
  have hanchor : anchor ∈ (tile.place anchor 0).sites := by
    rw [HeightTile.mem_place_sites, sub_self]
    exact hone
  have hmin (point : Site) (hmem : point ∈ (tile.place anchor 0).sites) :
      anchor.2 ≤ point.2 ∧ (anchor.2 = point.2 → anchor.1 ≤ point.1) := by
    have h := endpoint.nonnegative_coordinates ((HeightTile.mem_place_sites _ _ _ _).mp hmem)
    simp only [Prod.fst_sub, Prod.snd_sub] at h
    omega
  have h := (endpoint.atOrigin_agrees.place anchor 0).llCenter_trim
    (tile.place_sites_nonempty anchor 0 endpoint.atOrigin.property) hanchor hmin
  simpa only [EndpointAtom.attach, NonemptyTile.llCenter, NonemptyTile.trim, NonemptyTile.place,
    Prod.fst_zero, Prod.snd_zero, zero_mul, add_zero, add_sub_cancel_right] using h

end FLatticePaper.Construction
