import FLatticePaper.Tiles.VGlue
import FLatticePaper.Tiles.HorizontalStep
import FLatticePaper.Tiles.StandardHalfTurn
import FLatticePaper.Farey.Rotation

/-! Task 53, marksIn (vertical induction, the non-base step).

`VInv u` says that the vertical strings of the swapped quad of `u` lie in the tiles and registers of `u`: the vertical block of
`childP (swapW u)` in `evenTile u`, of `childQ (swapW u)` in `oddTile u`, of `parentP (swapW u)` in the even register and of
`parentQ (swapW u)` in the odd register. The step for `u·d` reads the swapped quad with the digit `swapTwoThree d` (the same three
rules as `HorizontalStep`), and the vertical junction offsets are `texV2` of the rotated slopes; the rotated slopes are the parent
fractions of `u·d` by the rotation identities R1 to R4. -/

namespace FLatticePaper.Tiles.VStep

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.Standard FLatticePaper.Tiles.SiteStrings
open FLatticePaper.Tiles.VJunction FLatticePaper.Tiles.VGlue FLatticePaper.Tiles.HorizontalGlue
open FLatticePaper.Tiles.HorizontalStep FLatticePaper.Tiles.CeilWords FLatticePaper.Tiles.CeilBlocks
open FLatticePaper.Tiles.ParentInterior FLatticePaper.Construction

/-- The vertical invariant of a word `u`. -/
def VInv (u : Word) : Prop :=
  HV (vert (quadAt [] (swapW u)).childP) (evenTile u) ∧ HV (vert (quadAt [] (swapW u)).childQ) (oddTile u) ∧
    HV (vert (quadAt [] (swapW u)).parentP) (stateAt u).tEven ∧
    HV (vert (quadAt [] (swapW u)).parentQ) (stateAt u).tOdd

theorem swapW_snoc (u : Word) (d : Digit) : swapW (u ++ [d]) = swapW u ++ [d.swapTwoThree] := by
  simp [swapW]

theorem swapW_map_eq (u : Word) : (swapW u).map Digit.swapTwoThree = u := by
  simp [swapW, List.map_map, Function.comp_def, Digit.swapTwoThree_swapTwoThree]

/-! ### The rotation identities R1 to R4 -/

theorem rot_curO_swap (u : Word) :
    ((parentsAt (swapW u)).current .odd).rotate = (parentsAt u).current .even := by
  have hv := parentsAt_valid (swapW u)
  rw [hv.rotate_current_odd, rotate_parentsAt, swapW_map_eq]

theorem rot_curE_swap (u : Word) :
    ((parentsAt (swapW u)).current .even).rotate = (parentsAt u).current .odd := by
  have hv := parentsAt_valid (swapW u)
  rw [hv.rotate_current_even, rotate_parentsAt, swapW_map_eq]

theorem rot_parent_odd_swap (u : Word) : ((parentsAt (swapW u)).odd).rotate = (parentsAt u).even := by
  have h := rotate_parentsAt (swapW u)
  rw [swapW_map_eq] at h
  exact congrArg Parents.even h

theorem rot_parent_even_swap (u : Word) : ((parentsAt (swapW u)).even).rotate = (parentsAt u).odd := by
  have h := rotate_parentsAt (swapW u)
  rw [swapW_map_eq] at h
  exact congrArg Parents.odd h

/-! ### The glue of the two vertical blocks of a child word -/

/-- The vertical glue of the two blocks `pw`, `qw` of a child word, for both parities. The offsets are `texV2 q` for `pw` and
`texV2 p` for `qw`; the containments are `vert qw ⊆ T1`, `vert pw ⊆ T2`. -/
theorem vglue_all (w' : Word) (pw qw : BinaryWord) (T1 T2 : Tile) (p q : Fraction)
    (hPb : pw.getLast? = some Letter.p) (hQb : qw.getLast? = some Letter.p)
    (hjP : jv (vert pw) = texV2 q) (hjQ : jv (vert qw) = texV2 p)
    (hT1 : HV (vert qw) T1) (hT2 : HV (vert pw) T2) :
    HV (vert (childWords w' pw qw).2) (oddChildB (phase w' == 1) T1 T2 p q) ∧
      HV (vert (childWords w' pw qw).1) (evenChildB (phase w' == 1) T1 T2 p q) := by
  obtain ⟨P', hP'⟩ := vertical_head pw hPb
  obtain ⟨Q', hQ'⟩ := vertical_head qw hQb
  rw [hP'] at hjP hT2
  rw [hQ'] at hjQ hT1
  unfold childWords
  by_cases h : w'.count Digit.one % 2 = 0
  · have hph : (phase w' == 1) = false := by simp [phase, h]
    rw [if_pos h, hph]
    constructor
    · show HV (vert (qw ++ pw)) _
      rw [vert_append, hP', hQ']
      exact glue_vB_false Q' P' T1 T2 p q hT2 hT1 hjP
    · show HV (vert (qw ++ qw ++ pw)) _
      rw [vert_append, vert_append, hP', hQ']
      have := glue_vA_false Q' P' T1 T2 p q hT2 hT1 hjP hjQ
      simpa [List.append_assoc] using this
  · have h1 : w'.count Digit.one % 2 = 1 := by omega
    have hph : (phase w' == 1) = true := by simp [phase, h1]
    rw [if_neg h, hph]
    constructor
    · show HV (vert (pw ++ qw)) _
      rw [vert_append, hP', hQ']
      exact glue_vB_true Q' P' T1 T2 p q hT1 hT2 hjQ
    · show HV (vert (pw ++ qw ++ qw)) _
      rw [vert_append, vert_append, hP', hQ']
      have := glue_vA_true Q' P' T1 T2 p q hT1 hT2 hjQ
      simpa [List.append_assoc] using this


/-! ### The block facts of the swapped quad -/

theorem vblk_odd (x : BinaryWord) (f : Fraction) (hx : CeilOf x (sOdd f)) (hi : Inner01 f) (hf : f.Odd) :
    x.getLast? = some Letter.p ∧ jv (vert x) = texV2 f.rotate := by
  have hC : CeilWord x (2 * f.num) (f.den + f.num) := hx
  have hl : 1 ≤ f.den + f.num := by
    obtain ⟨hi1, hi2⟩ := hi
    omega
  obtain ⟨⟨x', -, hl'⟩, -⟩ := block_odd_blk x f hx hi
  exact ⟨hl', vert_jv_odd x f hC hl hf⟩

theorem vblk_even (x : BinaryWord) (f : Fraction) (hx : CeilOf x (sEven f)) (hi : Inner01 f) (hf : f.Even) :
    x.getLast? = some Letter.p ∧ jv (vert x) = texV2 f.rotate := by
  have hC : CeilWord x f.num ((f.den + f.num) / 2) := hx
  have hl : 1 ≤ (f.den + f.num) / 2 := by
    obtain ⟨hi1, hi2⟩ := hi
    have hf' : (f.num + f.den) % 2 = 0 := hf
    omega
  obtain ⟨⟨x', -, hl'⟩, -⟩ := block_even_blk x f hx hi hf
  exact ⟨hl', vert_jv_even x f hC hl hf⟩

theorem not_three_of_swap (u : Word) (hu : ¬ ∀ x ∈ u, x = Digit.two) : ¬ ∀ x ∈ swapW u, x = Digit.three := by
  intro h
  apply hu
  intro x hx
  have := h x.swapTwoThree (List.mem_map.2 ⟨x, hx, rfl⟩)
  revert this
  cases x <;> decide

theorem not_two_of_swap (u : Word) (hu : ¬ ∀ x ∈ u, x = Digit.three) : ¬ ∀ x ∈ swapW u, x = Digit.two := by
  intro h
  apply hu
  intro x hx
  have := h x.swapTwoThree (List.mem_map.2 ⟨x, hx, rfl⟩)
  revert this
  cases x <;> decide

theorem phase_swap_snoc (u : Word) (d : Digit) : phase (swapW u ++ [d.swapTwoThree]) = phase (u ++ [d]) := by
  have h := phase_rotate_word (u ++ [d])
  have e : (u ++ [d]).map Digit.swapTwoThree = swapW u ++ [d.swapTwoThree] := by
    simp [swapW]
  rw [e] at h
  exact h

/-! ### The three steps -/

theorem vinv_step_one (u : Word) (hI : VInv u) : VInv (u ++ [Digit.one]) := by
  have hQ := quadInv_all (swapW u)
  unfold QuadInv at hQ
  obtain ⟨c1, c2, -, -⟩ := hQ
  have hnb : ¬ IsBase (u ++ [Digit.one]) := by
    rintro (h | h | h)
    · simp at h
    · exact absurd (h Digit.one (by simp)) (by decide)
    · exact absurd (h Digit.one (by simp)) (by decide)
  obtain ⟨hTo, hTe⟩ := tiles_nonbase _ hnb
  have hq : quadAt [] (swapW (u ++ [Digit.one])) = (quadAt [] (swapW u)).step (swapW u) Digit.one := by
    rw [swapW_snoc]
    exact quadAt_snoc_nil _ _
  obtain ⟨hPb, hjP⟩ := vblk_odd (quadAt [] (swapW u)).childP ((parentsAt (swapW u)).current .odd) c1
    (inner_cur_odd (swapW u)) (parentsAt_valid (swapW u)).current_odd_parity
  obtain ⟨hQb, hjQ⟩ := vblk_even (quadAt [] (swapW u)).childQ ((parentsAt (swapW u)).current .even) c2
    (inner_cur_even (swapW u)) (cur_even_even (swapW u))
  rw [rot_curO_swap] at hjP
  rw [rot_curE_swap] at hjQ
  have gg := vglue_all (swapW u ++ [Digit.one]) (quadAt [] (swapW u)).childP (quadAt [] (swapW u)).childQ
    (oddTile u) (evenTile u) ((parentsAt u).current .odd) ((parentsAt u).current .even) hPb hQb hjP hjQ hI.2.1 hI.1
  have hph : phase (swapW u ++ [Digit.one]) = phase (u ++ [Digit.one]) := phase_swap_snoc u Digit.one
  rw [hph] at gg
  have hpar := par_one u
  have hreg := reg_one u
  unfold VInv at hI ⊢
  rw [hq, hTo, hTe, hpar.1, hpar.2, hreg.1, hreg.2]
  simp only [WordQuad.step]
  exact ⟨gg.2, gg.1, hI.1, hI.2.1⟩

theorem vinv_step_two (u : Word) (hI : VInv u) (hu : ¬ ∀ x ∈ u, x = Digit.two) : VInv (u ++ [Digit.two]) := by
  have hQ := quadInv_all (swapW u)
  unfold QuadInv at hQ
  obtain ⟨c1, c2, c3, -⟩ := hQ
  have hnb : ¬ IsBase (u ++ [Digit.two]) := by
    rintro (h | h | h)
    · simp at h
    · exact absurd (h Digit.two (by simp)) (by decide)
    · exact hu (fun x hx => h x (by simp [hx]))
  obtain ⟨hTo, hTe⟩ := tiles_nonbase _ hnb
  have hq : quadAt [] (swapW (u ++ [Digit.two])) = (quadAt [] (swapW u)).step (swapW u) Digit.three := by
    rw [swapW_snoc]
    exact quadAt_snoc_nil _ _
  have hnot := not_three_of_swap u hu
  obtain ⟨hPb, hjP⟩ := vblk_odd (quadAt [] (swapW u)).parentP ((parentsAt (swapW u)).odd) c3
    (odd_inner_of_not_threes (swapW u) hnot) (parentsAt_valid (swapW u)).odd_parity
  obtain ⟨hQb, hjQ⟩ := vblk_even (quadAt [] (swapW u)).childQ ((parentsAt (swapW u)).current .even) c2
    (inner_cur_even (swapW u)) (cur_even_even (swapW u))
  rw [rot_parent_odd_swap] at hjP
  rw [rot_curE_swap] at hjQ
  have gg := vglue_all (swapW u ++ [Digit.three]) (quadAt [] (swapW u)).parentP (quadAt [] (swapW u)).childQ
    (oddTile u) ((stateAt u).tEven) ((parentsAt u).current .odd) ((parentsAt u).even) hPb hQb hjP hjQ
    hI.2.1 hI.2.2.1
  have hph : phase (swapW u ++ [Digit.three]) = phase (u ++ [Digit.two]) := phase_swap_snoc u Digit.two
  rw [hph] at gg
  have hpar := par_two u
  have hreg := reg_two u
  unfold VInv at hI ⊢
  rw [hq, hTo, hTe, hpar.1, hpar.2, hreg.1, hreg.2]
  simp only [WordQuad.step]
  exact ⟨gg.2, gg.1, hI.2.2.1, hI.2.1⟩

theorem vinv_step_three (u : Word) (hI : VInv u) (hu : ¬ ∀ x ∈ u, x = Digit.three) :
    VInv (u ++ [Digit.three]) := by
  have hQ := quadInv_all (swapW u)
  unfold QuadInv at hQ
  obtain ⟨c1, -, -, c4⟩ := hQ
  have hnb : ¬ IsBase (u ++ [Digit.three]) := by
    rintro (h | h | h)
    · simp at h
    · exact hu (fun x hx => h x (by simp [hx]))
    · exact absurd (h Digit.three (by simp)) (by decide)
  obtain ⟨hTo, hTe⟩ := tiles_nonbase _ hnb
  have hq : quadAt [] (swapW (u ++ [Digit.three])) = (quadAt [] (swapW u)).step (swapW u) Digit.two := by
    rw [swapW_snoc]
    exact quadAt_snoc_nil _ _
  have hnot := not_two_of_swap u hu
  obtain ⟨hPb, hjP⟩ := vblk_odd (quadAt [] (swapW u)).childP ((parentsAt (swapW u)).current .odd) c1
    (inner_cur_odd (swapW u)) (parentsAt_valid (swapW u)).current_odd_parity
  obtain ⟨hQb, hjQ⟩ := vblk_even (quadAt [] (swapW u)).parentQ ((parentsAt (swapW u)).even) c4
    (even_inner_of_not_twos (swapW u) hnot) (parentsAt_valid (swapW u)).even_parity
  rw [rot_curO_swap] at hjP
  rw [rot_parent_even_swap] at hjQ
  have gg := vglue_all (swapW u ++ [Digit.two]) (quadAt [] (swapW u)).childP (quadAt [] (swapW u)).parentQ
    ((stateAt u).tOdd) (evenTile u) ((parentsAt u).odd) ((parentsAt u).current .even) hPb hQb hjP hjQ
    hI.2.2.2 hI.1
  have hph : phase (swapW u ++ [Digit.two]) = phase (u ++ [Digit.three]) := phase_swap_snoc u Digit.three
  rw [hph] at gg
  have hpar := par_three u
  have hreg := reg_three u
  unfold VInv at hI ⊢
  rw [hq, hTo, hTe, hpar.1, hpar.2, hreg.1, hreg.2]
  simp only [WordQuad.step]
  exact ⟨gg.2, gg.1, hI.1, hI.2.2.2⟩

end FLatticePaper.Tiles.VStep
