import FLatticePaper.Plane.AlternateMidpoint
import Mathlib.Algebra.Group.Prod

namespace FLatticePaper

theorem evenSite_add_iff_of_even (site offset : Site) (heven : EvenSite offset) :
    EvenSite (site + offset) ↔ EvenSite site := by
  change ((site.1 + offset.1) + (site.2 + offset.2)) % 2 = 0 ↔ (site.1 + site.2) % 2 = 0
  change (offset.1 + offset.2) % 2 = 0 at heven
  omega

theorem incomingNeg_add_of_even (site offset : Site) (heven : EvenSite offset) :
    incomingNeg (site + offset) = incomingNeg site + offset := by
  have hparity := evenSite_add_iff_of_even site offset heven
  by_cases hsite : EvenSite site
  · simp only [incomingNeg, if_pos hsite, if_pos (hparity.mpr hsite)]
    apply Prod.ext <;> dsimp
    omega
  · simp only [incomingNeg, if_neg hsite, if_neg (fun h => hsite (hparity.mp h))]
    apply Prod.ext <;> dsimp
    omega

theorem incomingPos_add_of_even (site offset : Site) (heven : EvenSite offset) :
    incomingPos (site + offset) = incomingPos site + offset := by
  have hparity := evenSite_add_iff_of_even site offset heven
  by_cases hsite : EvenSite site
  · simp only [incomingPos, if_pos hsite, if_pos (hparity.mpr hsite)]
    apply Prod.ext <;> dsimp
    omega
  · simp only [incomingPos, if_neg hsite, if_neg (fun h => hsite (hparity.mp h))]
    apply Prod.ext <;> dsimp
    omega

/-- A parity-preserving translation respects both physical incoming directions. -/
theorem laplacian_translate_of_even (field : Field) (site offset : Site) (heven : EvenSite offset) :
    laplacian (fun input => field (input + offset)) site = laplacian field (site + offset) := by
  simp only [laplacian, incomingNeg_add_of_even site offset heven,
    incomingPos_add_of_even site offset heven]

/-- The physical slip for an even child `num/den` and its odd parent
`parentNum/parentDen`: `2 ε (parentDen, parentNum)`. -/
def alternateSlip (num den parentNum parentDen : ℤ) : Site :=
  let det := parentNum * den - parentDen * num
  (2 * (det * parentDen), 2 * (det * parentNum))

theorem evenSite_alternateSlip (num den parentNum parentDen : ℤ) :
    EvenSite (alternateSlip num den parentNum parentDen) := by
  dsimp [EvenSite, alternateSlip]
  omega

/-- The standard field shifted by the manuscript's actual alternate slip on the plane. -/
def alternateCompanion (standard : Field) (num den parentNum parentDen : ℤ) : Field :=
  fun site => standard (site + alternateSlip num den parentNum parentDen)

/-- For the exact slip, binary values on the second sheet follow from those on
the standard sheet. The slip bounds, exclusion and signed ranks are still inputs. -/
theorem isBurningRank_alternateCompanion_midpoint {α : Type*} [LT α]
    {standard : Field} {rank : Site → α} (num den parentNum parentDen : ℤ)
    (hstep : HasUnitSlip standard (alternateCompanion standard num den parentNum parentDen))
    (hnoSaddle : NoEvenSlipSaddle standard (alternateCompanion standard num den parentNum parentDen))
    (hr : IsConstrainedBurningRank standard rank
      (fun center input => slipIncrement standard
        (alternateCompanion standard num den parentNum parentDen) center input ≤ 0)) :
    IsBurningRank
      (roundedMidpoint standard (alternateCompanion standard num den parentNum parentDen))
      (roundedMidpointRank standard (alternateCompanion standard num den parentNum parentDen) rank) := by
  refine isBurningRank_roundedMidpoint (fun site => ?_) hstep hnoSaddle hr
  let offset := alternateSlip num den parentNum parentDen
  have hlap : laplacian (alternateCompanion standard num den parentNum parentDen) site =
      laplacian standard (site + offset) :=
    laplacian_translate_of_even standard site offset
      (evenSite_alternateSlip num den parentNum parentDen)
  rw [hlap]
  rcases hr.toIsBurningRank (site + offset) with ⟨h, -, -⟩ | ⟨h, -⟩
  · exact Or.inl h
  · exact Or.inr h

end FLatticePaper
