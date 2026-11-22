import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Algebra.Group.Basic

/-! # The missing sites of a union of placed pieces (task 44, step 1)

A placed piece has an offset, the TeX donor and the constructor's donor (both in the donor frame). The TeX union covers a
site `x` when some placed TeX donor contains it; the constructor's union covers `x` when some placed constructor donor
contains it. A site is *missing* when the TeX union covers it and the constructor's does not.

The lemmas here give the membership of the missing set from the pieces' data, for families whose constructor donors are
TeX donors (`ctor ⊆ tex`), and in the case where each constructor donor is the TeX donor minus a missing set (`ctor =
tex \ miss`): then a site is missing exactly when every placed TeX donor containing it misses it there. The list union
`List.foldl (· ∪ ·)` of `insertAll_sites` (OrderedOverlap.lean) is handled by `mem_foldl_union_iff`. -/

namespace FLatticePaper.Construction.MissingSites

variable {α : Type*} [AddCommGroup α] [DecidableEq α]

omit [DecidableEq α] in
/-- A placed piece: its offset, the TeX donor and the constructor's donor, both in the donor frame. -/
structure Piece (α : Type*) where
  offset : α
  tex : Finset α
  ctor : Finset α

/-- The TeX union of a family of placed pieces covers `x`. -/
def TeXCovers (F : List (Piece α)) (x : α) : Prop :=
  ∃ p ∈ F, x - p.offset ∈ p.tex

/-- The constructor's union of a family of placed pieces covers `x`. -/
def CtorCovers (F : List (Piece α)) (x : α) : Prop :=
  ∃ p ∈ F, x - p.offset ∈ p.ctor

/-- The missing sites of a family: covered by the TeX union, not by the constructor's. -/
def Missing (F : List (Piece α)) (x : α) : Prop :=
  TeXCovers F x ∧ ¬ CtorCovers F x

/-- The constructor's donors lie in the TeX donors. -/
def Nested (F : List (Piece α)) : Prop :=
  ∀ p ∈ F, p.ctor ⊆ p.tex

omit [DecidableEq α] in
/-- The missing sites, piece by piece: `x` is missing iff some placed TeX donor contains it and every placed TeX donor
that contains it also misses it in its donor frame. -/
theorem missing_iff (F : List (Piece α)) (hF : Nested F) (x : α) :
    Missing F x ↔
      (∃ p ∈ F, x - p.offset ∈ p.tex) ∧ ∀ p ∈ F, x - p.offset ∈ p.tex → x - p.offset ∉ p.ctor := by
  constructor
  · rintro ⟨hT, hC⟩
    refine ⟨hT, fun p hp hpt hpc => hC ⟨p, hp, hpc⟩⟩
  · rintro ⟨hT, hall⟩
    refine ⟨hT, ?_⟩
    rintro ⟨p, hp, hpc⟩
    exact hall p hp (hF p hp hpc) hpc

/-- When each constructor donor is its TeX donor minus a missing set `miss p`, a site is missing iff every placed TeX
donor containing it misses it there. -/
theorem missing_iff_of_sdiff (F : List (Piece α)) (miss : Piece α → Finset α)
    (hF : ∀ p ∈ F, p.ctor = p.tex \ miss p) (x : α) :
    Missing F x ↔
      (∃ p ∈ F, x - p.offset ∈ p.tex) ∧ ∀ p ∈ F, x - p.offset ∈ p.tex → x - p.offset ∈ miss p := by
  rw [missing_iff F (fun p hp => by rw [hF p hp]; exact Finset.sdiff_subset) x]
  constructor
  · rintro ⟨hT, hall⟩
    refine ⟨hT, fun p hp hpt => ?_⟩
    by_contra hmiss
    exact hall p hp hpt (by rw [hF p hp]; exact Finset.mem_sdiff.mpr ⟨hpt, hmiss⟩)
  · rintro ⟨hT, hall⟩
    refine ⟨hT, fun p hp hpt hpc => ?_⟩
    rw [hF p hp, Finset.mem_sdiff] at hpc
    exact hpc.2 (hall p hp hpt)

omit [DecidableEq α] in
/-- The sites of the constructor's union are the TeX union minus the missing sites: the constructor covers exactly the
TeX-covered sites that are not missing. -/
theorem ctorCovers_iff_texCovers_and_not_missing (F : List (Piece α)) (hF : Nested F) (x : α) :
    CtorCovers F x ↔ TeXCovers F x ∧ ¬ Missing F x := by
  constructor
  · rintro ⟨p, hp, hpc⟩
    exact ⟨⟨p, hp, hF p hp hpc⟩, fun h => h.2 ⟨p, hp, hpc⟩⟩
  · rintro ⟨hT, hnm⟩
    by_contra hC
    exact hnm ⟨hT, hC⟩

omit [AddCommGroup α] in
/-- Membership in a left-folded union of finite sets. -/
theorem mem_foldl_union_iff (init : Finset α) (copies : List (Finset α)) (x : α) :
    x ∈ copies.foldl (fun occupied incoming => occupied ∪ incoming) init ↔
      x ∈ init ∨ ∃ s ∈ copies, x ∈ s := by
  induction copies generalizing init with
  | nil => simp
  | cons s rest ih =>
    simp only [List.foldl_cons, ih, Finset.mem_union, List.mem_cons]
    constructor
    · rintro (h | ⟨t, ht, hx⟩)
      · rcases h with h | h
        · exact Or.inl h
        · exact Or.inr ⟨s, Or.inl rfl, h⟩
      · exact Or.inr ⟨t, Or.inr ht, hx⟩
    · rintro (h | ⟨t, ht | ht, hx⟩)
      · exact Or.inl (Or.inl h)
      · subst ht
        exact Or.inl (Or.inr hx)
      · exact Or.inr ⟨t, ht, hx⟩

/-- The sites of a placed donor: `x` is in `donor` translated by `offset` iff `x - offset` is in the donor. -/
theorem mem_image_add_iff (donor : Finset α) (offset x : α) :
    x ∈ donor.image (· + offset) ↔ x - offset ∈ donor := by
  constructor
  · intro h
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp h
    simpa using hy
  · intro h
    exact Finset.mem_image.mpr ⟨x - offset, h, by simp⟩

end FLatticePaper.Construction.MissingSites
