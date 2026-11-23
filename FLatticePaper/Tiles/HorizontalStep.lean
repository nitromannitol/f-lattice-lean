import FLatticePaper.Tiles.HorizontalGlue
import FLatticePaper.Tiles.ParentInterior
import FLatticePaper.Tiles.CeilBlocks
import FLatticePaper.Tiles.CeilWords
import FLatticePaper.Tiles.StandardTiles

/-! Task 53, marksIn (horizontal induction, the non-base step).

`Inv u`: the four forward horizontal strings of `u` lie in the odd tile, the even tile, and the two registers of the state of
`u`. For a word `u·d` that is not a base word, `Inv u` gives `Inv (u·d)`:

* `d = 1`: the blocks are `childP u`, `childQ u` (slopes of the current fractions); the registers become `oddTile u`, `evenTile u`.
* `d = 2`: the blocks are `childP u`, `parentQ u`; the registers become `oddTile u`, the old even register of `u`.
* `d = 3`: the blocks are `parentP u`, `childQ u`; the registers become the old odd register of `u`, `evenTile u`.

The block facts come from `ParentInterior` (the parents are interior off the boundary words) and `CeilBlocks` (ceiling blocks). -/

namespace FLatticePaper.Tiles.HorizontalStep

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.Standard FLatticePaper.Tiles.SiteStrings
open FLatticePaper.Tiles.HorizontalGlue FLatticePaper.Tiles.CeilWords FLatticePaper.Tiles.CeilBlocks
open FLatticePaper.Tiles.ParentInterior FLatticePaper.Construction

/-- The invariant of a word: the horizontal strings of its quad lie in the tiles and registers of its state. -/
def Inv (u : Word) : Prop :=
  HC (quadAt [] u).childP (oddTile u) ∧ HC (quadAt [] u).childQ (evenTile u) ∧
    HC (quadAt [] u).parentP (stateAt u).tOdd ∧ HC (quadAt [] u).parentQ (stateAt u).tEven

/-- A block: a ceiling word starting with `q` and ending with `p`. -/
def Blk (x : BinaryWord) : Prop := ∃ x', x = Letter.q :: x' ∧ x.getLast? = some Letter.p

theorem block_odd_blk (x : BinaryWord) (f : Fraction) (hx : CeilOf x (sOdd f)) (hi : Inner01 f) :
    Blk x ∧ jn x = texV1Odd f := by
  have hC : CeilWord x (2 * f.num) (f.den + f.num) := hx
  obtain ⟨hi1, hi2⟩ := hi
  have hk : 2 * f.num < f.den + f.num := by omega
  obtain ⟨x', hx'⟩ := ceil_head_q x (2 * f.num) (f.den + f.num) hC (by omega) hk
  exact ⟨⟨x', hx', ceil_last_p x _ _ hC (by omega) hk⟩, offset_odd x f hC (by omega)⟩

theorem block_even_blk (x : BinaryWord) (f : Fraction) (hx : CeilOf x (sEven f)) (hi : Inner01 f) (hf : f.Even) :
    Blk x ∧ jn x = texV1Even f := by
  have hC : CeilWord x f.num ((f.den + f.num) / 2) := hx
  obtain ⟨hi1, hi2⟩ := hi
  have hf' : (f.num + f.den) % 2 = 0 := hf
  have hk : f.num < (f.den + f.num) / 2 := by omega
  obtain ⟨x', hx'⟩ := ceil_head_q x f.num ((f.den + f.num) / 2) hC (by omega) hk
  exact ⟨⟨x', hx', ceil_last_p x _ _ hC (by omega) hk⟩, offset_even x f hC (by omega) hf⟩

theorem cur_even_even (u : Word) : ((parentsAt u).current .even).Even := by
  have hv := parentsAt_valid u
  have hE : ((parentsAt u).even.num + (parentsAt u).even.den) % 2 = 0 := hv.even_parity
  unfold Fraction.Even
  simp only [Parents.current, Parents.combine]
  omega

/-- The glue of the two blocks of a child word, for both parities of the number of `1`s of the child. -/
theorem glue_all (w : Word) (pw qw : BinaryWord) (T1 T2 : Tile) (p q : Fraction)
    (hP : Blk pw) (hQ : Blk qw) (hjP : jn pw = texV1Odd p) (hjQ : jn qw = texV1Even q)
    (hT1 : HC pw T1) (hT2 : HC qw T2) :
    HC (childWords w pw qw).1 (oddChildB (phase w == 1) T1 T2 p q) ∧
      HC (childWords w pw qw).2 (evenChildB (phase w == 1) T1 T2 p q) := by
  obtain ⟨pw', rfl, hpl⟩ := hP
  obtain ⟨qw', rfl, hql⟩ := hQ
  unfold childWords
  by_cases h : w.count Digit.one % 2 = 0
  · have hph : (phase w == 1) = false := by simp [phase, h]
    rw [if_pos h, hph]
    exact ⟨glue_childP_false qw' pw' T1 T2 p q hql hjQ hT2 hT1,
      glue_childQ_false qw' pw' T1 T2 p q hql hjQ hT2 hT1⟩
  · have h1 : w.count Digit.one % 2 = 1 := by omega
    have hph : (phase w == 1) = true := by simp [phase, h1]
    rw [if_neg h, hph]
    exact ⟨glue_childP_true pw' qw' T1 T2 p q hpl hql hjP hjQ hT1 hT2,
      glue_childQ_true pw' qw' T1 T2 p q hpl hjP hT1 hT2⟩

/-! ### Registers and parents of `u·d` -/

theorem reg_one (u : Word) :
    (stateAt (u ++ [Digit.one])).tOdd = oddTile u ∧ (stateAt (u ++ [Digit.one])).tEven = evenTile u := by
  rw [stateAt_snoc]
  exact ⟨rfl, rfl⟩

theorem reg_two (u : Word) :
    (stateAt (u ++ [Digit.two])).tOdd = oddTile u ∧ (stateAt (u ++ [Digit.two])).tEven = (stateAt u).tEven := by
  rw [stateAt_snoc]
  exact ⟨rfl, rfl⟩

theorem reg_three (u : Word) :
    (stateAt (u ++ [Digit.three])).tOdd = (stateAt u).tOdd ∧ (stateAt (u ++ [Digit.three])).tEven = evenTile u := by
  rw [stateAt_snoc]
  exact ⟨rfl, rfl⟩

theorem par_one (u : Word) :
    (parentsAt (u ++ [Digit.one])).odd = (parentsAt u).current .odd ∧
      (parentsAt (u ++ [Digit.one])).even = (parentsAt u).current .even := by
  rw [parentsAt_snoc_one]
  exact ⟨rfl, rfl⟩

theorem par_two (u : Word) :
    (parentsAt (u ++ [Digit.two])).odd = (parentsAt u).current .odd ∧
      (parentsAt (u ++ [Digit.two])).even = (parentsAt u).even := by
  rw [parentsAt_snoc_two]
  exact ⟨rfl, rfl⟩

theorem par_three (u : Word) :
    (parentsAt (u ++ [Digit.three])).odd = (parentsAt u).odd ∧
      (parentsAt (u ++ [Digit.three])).even = (parentsAt u).current .even := by
  rw [parentsAt_snoc_three]
  exact ⟨rfl, rfl⟩

/-- The tiles of a non-base word are the child tiles of its state. -/
theorem tiles_nonbase (w : Word) (h : ¬ IsBase w) :
    oddTile w = oddChildB (phase w == 1) (stateAt w).tOdd (stateAt w).tEven (parentsAt w).odd (parentsAt w).even ∧
      evenTile w = evenChildB (phase w == 1) (stateAt w).tOdd (stateAt w).tEven (parentsAt w).odd (parentsAt w).even := by
  have h1 : w ≠ [] := fun e => h (Or.inl e)
  have h2 : ¬ w = List.replicate w.length Digit.three :=
    fun e => h (Or.inr (Or.inl (fun d hd => by rw [e] at hd; exact List.eq_of_mem_replicate hd)))
  have h3 : ¬ w = List.replicate w.length Digit.two :=
    fun e => h (Or.inr (Or.inr (fun d hd => by rw [e] at hd; exact List.eq_of_mem_replicate hd)))
  unfold oddTile evenTile childTiles
  rw [if_neg h1, if_neg h2, if_neg h3]
  rw [stateAt_par]
  exact ⟨rfl, rfl⟩

/-! ### The three steps -/

theorem inv_step_one (u : Word) (hI : Inv u) : Inv (u ++ [Digit.one]) := by
  have hQ := quadInv_all u
  unfold QuadInv at hQ
  obtain ⟨c1, c2, -, -⟩ := hQ
  have hnb : ¬ IsBase (u ++ [Digit.one]) := by
    rintro (h | h | h)
    · simp at h
    · exact absurd (h Digit.one (by simp)) (by decide)
    · exact absurd (h Digit.one (by simp)) (by decide)
  obtain ⟨hTo, hTe⟩ := tiles_nonbase _ hnb
  have hq : quadAt [] (u ++ [Digit.one]) = ⟨(childWords (u ++ [Digit.one]) (quadAt [] u).childP (quadAt [] u).childQ).1,
      (childWords (u ++ [Digit.one]) (quadAt [] u).childP (quadAt [] u).childQ).2,
      (quadAt [] u).childP, (quadAt [] u).childQ⟩ := by
    rw [quadAt_snoc_nil]
    rfl
  obtain ⟨hP1, hj1⟩ := block_odd_blk (quadAt [] u).childP ((parentsAt u).current .odd) c1 (inner_cur_odd u)
  obtain ⟨hQ1, hjq⟩ := block_even_blk (quadAt [] u).childQ ((parentsAt u).current .even) c2
    (inner_cur_even u) (cur_even_even u)
  have hpar := par_one u
  have hreg := reg_one u
  unfold Inv at hI ⊢
  rw [hq, hTo, hTe, hpar.1, hpar.2, hreg.1, hreg.2]
  dsimp only
  obtain ⟨g1, g2⟩ := glue_all (u ++ [Digit.one]) (quadAt [] u).childP (quadAt [] u).childQ (oddTile u) (evenTile u)
    ((parentsAt u).current .odd) ((parentsAt u).current .even) hP1 hQ1 hj1 hjq hI.1 hI.2.1
  exact ⟨g1, g2, hI.1, hI.2.1⟩

theorem inv_step_two (u : Word) (hI : Inv u) (hu : ¬ ∀ x ∈ u, x = Digit.two) : Inv (u ++ [Digit.two]) := by
  have hQ := quadInv_all u
  unfold QuadInv at hQ
  obtain ⟨c1, -, -, c4⟩ := hQ
  have hnb : ¬ IsBase (u ++ [Digit.two]) := by
    rintro (h | h | h)
    · simp at h
    · exact absurd (h Digit.two (by simp)) (by decide)
    · exact hu (fun x hx => h x (by simp [hx]))
  obtain ⟨hTo, hTe⟩ := tiles_nonbase _ hnb
  have hq : quadAt [] (u ++ [Digit.two]) = ⟨(childWords (u ++ [Digit.two]) (quadAt [] u).childP (quadAt [] u).parentQ).1,
      (childWords (u ++ [Digit.two]) (quadAt [] u).childP (quadAt [] u).parentQ).2,
      (quadAt [] u).childP, (quadAt [] u).parentQ⟩ := by
    rw [quadAt_snoc_nil]
    rfl
  obtain ⟨hP1, hj1⟩ := block_odd_blk (quadAt [] u).childP ((parentsAt u).current .odd) c1 (inner_cur_odd u)
  obtain ⟨hQ2, hjq⟩ := block_even_blk (quadAt [] u).parentQ ((parentsAt u).even) c4
    (even_inner_of_not_twos u hu) (parentsAt_valid u).even_parity
  have hpar := par_two u
  have hreg := reg_two u
  unfold Inv at hI ⊢
  rw [hq, hTo, hTe, hpar.1, hpar.2, hreg.1, hreg.2]
  dsimp only
  obtain ⟨g1, g2⟩ := glue_all (u ++ [Digit.two]) (quadAt [] u).childP (quadAt [] u).parentQ (oddTile u)
    (stateAt u).tEven ((parentsAt u).current .odd) ((parentsAt u).even) hP1 hQ2 hj1 hjq hI.1 hI.2.2.2
  exact ⟨g1, g2, hI.1, hI.2.2.2⟩

theorem inv_step_three (u : Word) (hI : Inv u) (hu : ¬ ∀ x ∈ u, x = Digit.three) : Inv (u ++ [Digit.three]) := by
  have hQ := quadInv_all u
  unfold QuadInv at hQ
  obtain ⟨-, c2, c3, -⟩ := hQ
  have hnb : ¬ IsBase (u ++ [Digit.three]) := by
    rintro (h | h | h)
    · simp at h
    · exact hu (fun x hx => h x (by simp [hx]))
    · exact absurd (h Digit.three (by simp)) (by decide)
  obtain ⟨hTo, hTe⟩ := tiles_nonbase _ hnb
  have hq : quadAt [] (u ++ [Digit.three]) = ⟨(childWords (u ++ [Digit.three]) (quadAt [] u).parentP (quadAt [] u).childQ).1,
      (childWords (u ++ [Digit.three]) (quadAt [] u).parentP (quadAt [] u).childQ).2,
      (quadAt [] u).parentP, (quadAt [] u).childQ⟩ := by
    rw [quadAt_snoc_nil]
    rfl
  obtain ⟨hP3, hj3⟩ := block_odd_blk (quadAt [] u).parentP ((parentsAt u).odd) c3 (odd_inner_of_not_threes u hu)
  obtain ⟨hQ3, hjq⟩ := block_even_blk (quadAt [] u).childQ ((parentsAt u).current .even) c2
    (inner_cur_even u) (cur_even_even u)
  have hpar := par_three u
  have hreg := reg_three u
  unfold Inv at hI ⊢
  rw [hq, hTo, hTe, hpar.1, hpar.2, hreg.1, hreg.2]
  dsimp only
  obtain ⟨g1, g2⟩ := glue_all (u ++ [Digit.three]) (quadAt [] u).parentP (quadAt [] u).childQ (stateAt u).tOdd
    (evenTile u) ((parentsAt u).odd) ((parentsAt u).current .even) hP3 hQ3 hj3 hjq hI.2.2.1 hI.2.1
  exact ⟨g1, g2, hI.2.2.1, hI.2.1⟩

end FLatticePaper.Tiles.HorizontalStep
