import FLatticePaper.Plane.Induction.SheetFort
import FLatticePaper.Plane.Induction.S3FreeBoundary

/-! # The `H_0` core (Q23 step 4, the minus row)

The surviving boundary candidates of the minus row are `H_0 = (1,0)` and `V_0 = (0,0)`. The core argument of ALL_SLOPE_STEP ("Remaining
entries of the cut", the last paragraph): the candidates are not retained by any strict-interior site, so the strict-interior part of the
fort is an incoming fort of the recurrent comparison chart `M`; it is finite (`openRect` is finite), hence empty (`no_finite_fort_of_recurrent`).
Then a fort containing `H_0` or `V_0` has a strict-interior point: `H_0 ∈ S` forces `(1,1) ∈ S` (its south input `(1,−1)` lies outside the
closed polygon, `hsub`), and `(1,1)` is open; `V_0 ∈ S` forces `(1,0) = H_0 ∈ S` (its west input `(−1,0)` lies outside).

The one named input is `hI`: the strict-interior part is an incoming fort, which is the retained-quota statement of the note (the retained
input of every strict-interior site is not a candidate). Everything else is proved here. -/

namespace FLatticePaper.H0Core

open FLatticePaper FLatticePaper.Induction FLatticePaper.SheetFort FLatticePaper.FanTerminal

/-- `(1, −1)` (the south input of `H_0`) is outside the closed polygon. -/
theorem not_closed_one_neg (frame : ChildFrame) : (1, -1) ∉ frame.closedPolygon := by
  obtain ⟨-, -, -, -, hT⟩ := frame.child_facts
  have h1 : frame.tGrade ((1 : ℤ), (-1 : ℤ)) = frame.child.num + frame.child.den := by
    unfold ChildFrame.tGrade; ring
  unfold ChildFrame.closedPolygon
  simp only [Set.mem_setOf_eq]
  rw [if_pos (show EvenSite ((1 : ℤ), (-1 : ℤ)) by unfold EvenSite; simp)]
  intro h
  have := h.2.1
  rw [h1] at this
  omega

/-- `(−1, 0)` (the west input of `V_0`) is outside the closed polygon. -/
theorem not_closed_neg_one_zero (frame : ChildFrame) : (-1, 0) ∉ frame.closedPolygon := by
  obtain ⟨-, -, -, hd3, hT⟩ := frame.child_facts
  have hs : frame.sGrade ((-1 : ℤ), (0 : ℤ)) = -(frame.child.den + frame.child.num) := by
    unfold ChildFrame.sGrade; ring
  unfold ChildFrame.closedPolygon
  simp only [Set.mem_setOf_eq]
  rw [if_neg (show ¬ EvenSite ((-1 : ℤ), (0 : ℤ)) by unfold EvenSite; simp)]
  intro h
  have := h.2.2.1
  rw [hs] at this
  have hn := (frame.child_facts).1
  omega

/-- `(1, 1)` is in the open rectangle. -/
theorem open_one_one (frame : ChildFrame) : frame.openRect (1, 1) := by
  obtain ⟨hn, hnd, -, hd3, hT⟩ := frame.child_facts
  have hev : EvenSite ((1 : ℤ), (1 : ℤ)) := by unfold EvenSite; simp
  have ht : frame.tGrade ((1 : ℤ), (1 : ℤ)) = frame.child.num - frame.child.den := by
    unfold ChildFrame.tGrade; ring
  have hs : frame.sGrade ((1 : ℤ), (1 : ℤ)) = 2 * frame.child.den := by
    unfold ChildFrame.sGrade; ring
  unfold ChildFrame.openRect
  rw [if_pos hev, ht, hs]
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith
  · omega
  · omega
  · nlinarith

/-- **The `H_0` core** (minus): a fort `S` of the recurrent chart `M`, lying in the closed polygon, whose boundary points are among
`H_0, V_0`, and whose strict-interior part is an incoming fort (`hI`), is empty. -/
theorem h0_core_minus {M : Field} (frame : ChildFrame) (hrec : FLatticePaper.RecurrentField M) {S : Set Site}
    (hfort : IsIncomingFort M S)
    (hsub : ∀ z ∈ S, z ∈ frame.closedPolygon)
    (hcand : ∀ z ∈ S, z ∈ frame.closedPolygon → ¬ frame.openRect z → z = hFirst ∨ z = vFirst)
    (hI : IsIncomingFort M {x | x ∈ S ∧ frame.openRect x}) : S = ∅ := by
  have hfinI : {x | x ∈ S ∧ frame.openRect x}.Finite := (openRect_finite frame).subset (fun x hx => hx.2)
  have hempty := no_finite_fort_of_recurrent hrec hI hfinI
  have hnoint : ∀ z, z ∈ S → ¬ frame.openRect z := by
    intro z hz hopen
    have hm : z ∈ {x | x ∈ S ∧ frame.openRect x} := ⟨hz, hopen⟩
    rw [hempty] at hm
    exact hm
  have hS : ∀ z ∈ S, z = hFirst ∨ z = vFirst := fun z hz =>
    hcand z hz (hsub z hz) (hnoint z hz)
  -- `H_0 ∈ S` forces `(1,1) ∈ S`, an interior point
  have hH0 : hFirst ∉ S := by
    intro h
    have h1 : frame.openRect (1, 1) := open_one_one frame
    have hmem : ((1 : ℤ), (1 : ℤ)) ∈ S := by
      have hf := hfort hFirst h
      have hns : ((1 : ℤ), (-1 : ℤ)) ∉ S := fun hm => not_closed_one_neg frame (hsub _ hm)
      have hfirst : hFirst = ((1 : ℤ), (0 : ℤ)) := rfl
      rw [hfirst] at hf
      unfold incomingNeg incomingPos at hf
      simp only [EvenSite] at hf
      norm_num at hf
      rcases hf with ⟨-, h2 | h2⟩ | ⟨-, h2, h3⟩
      · exact absurd h2 hns
      · exact h2
      · exact h3
    exact hnoint _ hmem h1
  -- `V_0 ∈ S` forces `H_0 ∈ S`, which is excluded
  have hV0 : vFirst ∉ S := by
    intro h
    have hf := hfort vFirst h
    have hns : ((-1 : ℤ), (0 : ℤ)) ∉ S := fun hm => not_closed_neg_one_zero frame (hsub _ hm)
    have hvfirst : vFirst = ((0 : ℤ), (0 : ℤ)) := rfl
    rw [hvfirst] at hf
    unfold incomingNeg incomingPos at hf
    simp only [EvenSite] at hf
    norm_num at hf
    have hH : ((1 : ℤ), (0 : ℤ)) ∈ S := by
      rcases hf with ⟨-, h2 | h2⟩ | ⟨-, h2, h3⟩
      · exact absurd h2 hns
      · exact h2
      · exact h3
    exact hH0 hH
  ext z
  constructor
  · intro hz
    rcases hS z hz with rfl | rfl
    · exact absurd hz hH0
    · exact absurd hz hV0
  · intro hz
    exact absurd hz (Set.notMem_empty z)

end FLatticePaper.H0Core
