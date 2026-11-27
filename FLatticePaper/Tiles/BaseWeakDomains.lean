import FLatticePaper.Tiles.SiteBase
import FLatticePaper.Tiles.SurgicalWeakOdometers
import FLatticePaper.Construction.BaseCaseRecurrence
import FLatticePaper.Construction.NearOneBaseCases

/-! # The domains of the base odometers (part (a) of `BaseWeakInput`)

For every word `w`, the paper base odometers of its two children have the standard tiles of `w` as domains, and satisfy the
base condition `PaperBaseCond w`: the values are the paper values of the shape of `w` (`[]`, `3^k`, `2^k`). The boundary
respect and the lattice compatibilities of `BaseWeakInput` are separate. -/

namespace FLatticePaper.Tiles.BaseWeakDomains

open FLatticePaper.Farey
open FLatticePaper.Tiles.SiteBase
open FLatticePaper.Construction
open FLatticePaper.Tiles
open FLatticePaper.Tiles.Standard
open FLatticePaper.Tiles.SurgicalWeak

/-- The value of the odd base odometer of `w`: the paper value of the shape of `w`. -/
noncomputable def baseOddVal (w : Word) (x : ℤ × ℤ) : ℤ :=
  if w = [] then paperNearStairValue 3 (x + (0, 1))
  else if ∀ d ∈ w, d = Digit.three then paperLadderValue (2 * (w.length : ℤ) + 2) x
  else paperNearStairValue (2 * (w.length : ℤ) + 3) (x + (0, 1))

/-- The value of the even base odometer of `w`: the paper value of the shape of `w`. -/
noncomputable def baseEvenVal (w : Word) (x : ℤ × ℤ) : ℤ :=
  if w = [] then paperStairValue 3 x
  else if ∀ d ∈ w, d = Digit.three then paperStairValue (2 * (w.length : ℤ) + 3) x
  else paperNearLadderValue (2 * (w.length : ℤ) + 2) (x + (0, 1))

/-- For every word, the two base odometers have the standard tiles of `w` as domains and the paper base condition. -/
theorem base_weak_domains (w : Word) :
    ∃ wo we : PartialOdometer, wo.dom = oddTile w ∧ we.dom = evenTile w ∧ PaperBaseCond w wo we := by
  refine ⟨⟨oddTile w, baseOddVal w⟩, ⟨evenTile w, baseEvenVal w⟩, rfl, rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro h
    subst h
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa using oddTile_rep_two 0
    · intro x _
      simp [baseOddVal]
    · simpa using evenTile_rep_three 0
    · intro x _
      simp [baseEvenVal]
  · intro k hk h
    subst h
    have hne : k ≠ 0 := by omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact oddTile_rep_three k hk
    · intro x _
      simp [baseOddVal, hne]
    · exact evenTile_rep_three k
    · intro x _
      simp [baseEvenVal, hne]
  · intro k hk h
    subst h
    have hne : k ≠ 0 := by omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact oddTile_rep_two k
    · intro x _
      simp [baseOddVal, hne]
    · exact evenTile_rep_two k hk
    · intro x _
      simp [baseEvenVal, hne]

end FLatticePaper.Tiles.BaseWeakDomains
