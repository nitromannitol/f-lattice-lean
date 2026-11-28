import FLatticePaper.Tiles.MixedCompatBase
import FLatticePaper.Tiles.MixedCompatStair
import FLatticePaper.Tiles.MixedCompatNear
import FLatticePaper.Tiles.AltMixedCompat
import FLatticePaper.Tiles.WeakStepAssembly

/-! The local comparisons in the joint induction when the preceding word is a base
word. The register update selects either the same two children or the even or odd
child from the preceding run. -/

namespace FLatticePaper.Tiles.MixedCompatBaseStep

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.Standard
open FLatticePaper.Tiles.SurgicalWeak FLatticePaper.Tiles.ClosedPathAssembly
open FLatticePaper.Tiles.JointFamily FLatticePaper.Tiles.JointInduction

private theorem base_at_register {D : JointData} (hS : D.S = WeakStepPaper.paperS) {f : Word → JSlice} {n : ℕ}
    (hg : GoodBelow D f n) (u : Word) (hu : u.length < n) (hb : IsBase u) :
    PaperBaseCond u (f u).tOdd (f u).tEven := by
  have hs := (hg u hu).1
  obtain ⟨hO, hE, -⟩ := hs.2.2.1.1 hb
  rw [hO, hE]
  have h := hs.1.2.2.1 hb
  rwa [hS] at h

/-- The mixed-compatibility input of the joint induction for the first step away
from a run of threes, including the word consisting of one. -/
private theorem mixed_at_three_registers (D : JointData) (hS : D.S = WeakStepPaper.paperS)
    (f : Word → JSlice) (w u₁ u₂ : Word) (hg : GoodBelow D f w.length)
    (hr : regsAt w = (some u₁, some u₂))
    (hw : ∃ k : ℕ, w = List.replicate k .three ++ [.one] ∨ w = List.replicate (k+1) .three ++ [.two]) :
    MixedCompatOdd w u₁ u₂ (placedOdd w (f u₁).tOdd.val (f u₂).tEven.val 0) ∧
      MixedCompatEven w u₁ u₂ (placedEven w (f u₁).tOdd.val (f u₂).tEven.val 0) := by
  have hb (k : ℕ) : IsBase (List.replicate k Digit.three) :=
    Or.inr (Or.inl (fun _ h => (List.mem_replicate.mp h).2))
  obtain ⟨k, rfl | rfl⟩ := hw
  · rw [WeakStepPaper.regsAt_snoc] at hr
    simp only [regStep, Prod.mk.injEq, Option.some.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    have H := base_at_register hS hg _ (by simp) (hb k)
    cases k with
    | zero => exact ⟨MixedCompatBase.mixedCompatOdd_one _ _ H 0, MixedCompatBase.mixedCompatEven_one _ _ H 0⟩
    | succ k => exact MixedCompatStair.three_run_one (k + 1) (by omega) _ _ H 0
  · rw [WeakStepPaper.regsAt_snoc] at hr
    have prev : (regsAt (List.replicate (k+1) .three)).2 = some (List.replicate k .three) := by
      rw [List.replicate_succ', WeakStepPaper.regsAt_snoc]
      rfl
    simp only [regStep, prev, Prod.mk.injEq, Option.some.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    have H := base_at_register hS hg _ (by simp) (hb (k+1))
    have H' := base_at_register hS hg _ (by simp) (hb k)
    exact MixedCompatStair.three_run_two k _ _ _ _ H H' 0

/-- The mixed-compatibility input of the joint induction for the first step away
from a run of twos, including the word consisting of one. -/
private theorem mixed_at_two_registers (D : JointData) (hS : D.S = WeakStepPaper.paperS)
    (f : Word → JSlice) (w u₁ u₂ : Word) (hg : GoodBelow D f w.length)
    (hr : regsAt w = (some u₁, some u₂))
    (hw : ∃ k : ℕ, w = List.replicate k .two ++ [.one] ∨ w = List.replicate (k+1) .two ++ [.three]) :
    MixedCompatOdd w u₁ u₂ (placedOdd w (f u₁).tOdd.val (f u₂).tEven.val 0) ∧
      MixedCompatEven w u₁ u₂ (placedEven w (f u₁).tOdd.val (f u₂).tEven.val 0) := by
  have hb (k : ℕ) : IsBase (List.replicate k Digit.two) :=
    Or.inr (Or.inr (fun _ h => (List.mem_replicate.mp h).2))
  obtain ⟨k, rfl | rfl⟩ := hw
  · rw [WeakStepPaper.regsAt_snoc] at hr
    simp only [regStep, Prod.mk.injEq, Option.some.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    have H := base_at_register hS hg _ (by simp) (hb k)
    cases k with
    | zero => exact ⟨MixedCompatBase.mixedCompatOdd_one _ _ H 0, MixedCompatBase.mixedCompatEven_one _ _ H 0⟩
    | succ k => exact MixedCompatNear.two_run_one (k + 1) (by omega) _ _ H 0
  · rw [WeakStepPaper.regsAt_snoc] at hr
    have prev : (regsAt (List.replicate (k+1) .two)).1 = some (List.replicate k .two) := by
      rw [List.replicate_succ', WeakStepPaper.regsAt_snoc]
      rfl
    simp only [regStep, prev, Prod.mk.injEq, Option.some.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    have H := base_at_register hS hg _ (by simp) (hb (k+1))
    have H' := base_at_register hS hg _ (by simp) (hb k)
    exact MixedCompatNear.two_run_three k _ _ _ _ H H' 0

/-- The joint standard mixed input at every non-base child whose preceding word is a
base word, in both child parities. -/
theorem mixed_at_base_prefix (D : JointData) (hS : D.S = WeakStepPaper.paperS)
    (f : Word → JSlice) (w u₁ u₂ : Word) (hg : GoodBelow D f w.length) (hw : ¬ IsBase w)
    (hr : regsAt w = (some u₁, some u₂)) (hb : IsBase w.dropLast) :
    MixedCompatOdd w u₁ u₂ (placedOdd w (f u₁).tOdd.val (f u₂).tEven.val 0) ∧
      MixedCompatEven w u₁ u₂ (placedEven w (f u₁).tOdd.val (f u₂).tEven.val 0) := by
  cases w using List.reverseRecOn with
  | nil => exact (hw (Or.inl rfl)).elim
  | append_singleton v s =>
    rw [List.dropLast_concat] at hb
    rcases hb with rfl | h3 | h2
    · cases s
      · exact mixed_at_three_registers D hS f _ _ _ hg hr ⟨0, Or.inl rfl⟩
      · exact (hw (Or.inr (Or.inr (by simp)))).elim
      · exact (hw (Or.inr (Or.inl (by simp)))).elim
    · obtain ⟨k, rfl⟩ : ∃ k, v = List.replicate k Digit.three :=
        ⟨v.length, List.eq_replicate_iff.mpr ⟨rfl, h3⟩⟩
      cases s
      · exact mixed_at_three_registers D hS f _ _ _ hg hr ⟨k, Or.inl rfl⟩
      · cases k with
        | zero => exact (hw (Or.inr (Or.inr (by simp)))).elim
        | succ k => exact mixed_at_three_registers D hS f _ _ _ hg hr ⟨k, Or.inr rfl⟩
      · exact (hw (Or.inr (Or.inl (by simp_all [List.mem_replicate])))).elim
    · obtain ⟨k, rfl⟩ : ∃ k, v = List.replicate k Digit.two :=
        ⟨v.length, List.eq_replicate_iff.mpr ⟨rfl, h2⟩⟩
      cases s
      · exact mixed_at_two_registers D hS f _ _ _ hg hr ⟨k, Or.inl rfl⟩
      · exact (hw (Or.inr (Or.inr (by simp_all [List.mem_replicate])))).elim
      · cases k with
        | zero => exact (hw (Or.inr (Or.inl (by simp)))).elim
        | succ k => exact mixed_at_two_registers D hS f _ _ _ hg hr ⟨k, Or.inr rfl⟩

/-- The mixed input when both register odometers come from base words. -/
theorem mixed_of_base_registers (D : JointData) (hS : D.S = WeakStepPaper.paperS)
    (f : Word → JSlice) (w u₁ u₂ : Word) (hg : GoodBelow D f w.length) (hw : ¬ IsBase w)
    (hr : regsAt w = (some u₁, some u₂)) (h₁ : IsBase u₁) (h₂ : IsBase u₂) :
    MixedCompatOdd w u₁ u₂ (placedOdd w (f u₁).tOdd.val (f u₂).tEven.val 0) ∧
      MixedCompatEven w u₁ u₂ (placedEven w (f u₁).tOdd.val (f u₂).tEven.val 0) := by
  apply mixed_at_base_prefix D hS f w u₁ u₂ hg hw hr
  cases w using List.reverseRecOn with
  | nil => exact Or.inl rfl
  | append_singleton v s =>
    rw [List.dropLast_concat]
    rw [WeakStepPaper.regsAt_snoc] at hr
    cases s <;> simp only [regStep, Prod.mk.injEq, Option.some.injEq] at hr
    · exact hr.1.symm ▸ h₁
    · exact hr.1.symm ▸ h₁
    · exact hr.2.symm ▸ h₂

/-- It suffices to establish the joint mixed input at children of non-base words. -/
theorem mixedCompatInput_of_nonbase_prefix (D : JointData) (hS : D.S = WeakStepPaper.paperS)
    (h : ∀ (f : Word → JSlice) (w u₁ u₂ : Word), GoodBelow D f w.length → ¬ IsBase w →
      regsAt w = (some u₁, some u₂) → ¬ IsBase w.dropLast →
      MixedCompatOdd w u₁ u₂ (placedOdd w (f u₁).tOdd.val (f u₂).tEven.val 0) ∧
        MixedCompatEven w u₁ u₂ (placedEven w (f u₁).tOdd.val (f u₂).tEven.val 0)) :
    WeakStepAssembly.MixedCompatInput D := by
  intro f w u₁ u₂ hg hw hr
  by_cases hb : IsBase w.dropLast
  · exact mixed_at_base_prefix D hS f w u₁ u₂ hg hw hr hb
  · exact h f w u₁ u₂ hg hw hr hb

/-- The six standard pieces in either alternate child at the same base registers. -/
theorem alt_mixed_of_base_registers (D : JointData) (hS : D.S = WeakStepPaper.paperS)
    (f : Word → JSlice) (w u₁ u₂ : Word) (hg : GoodBelow D f w.length) (hw : ¬ IsBase w)
    (hr : regsAt w = (some u₁, some u₂)) (h₁ : IsBase u₁) (h₂ : IsBase u₂) (c : ℕ → ℤ) :
    ClosedPathAlt.AltMixedCompatOdd w u₁ u₂
        (ClosedPathAlt.placedAltOdd w (f u₁).tOdd.val (f u₂).tEven.val c) ∧
      ClosedPathAlt.AltMixedCompatEven w u₁ u₂
        (ClosedPathAlt.placedAltEven w (f u₁).tOdd.val (f u₂).tEven.val c) := by
  have hs := (mixed_of_base_registers D hS f w u₁ u₂ hg hw hr h₁ h₂).1
  have hp := (WeakStepAssembly.regsAt_parents w).1 u₁ (by rw [hr])
  have hq := (WeakStepAssembly.regsAt_parents w).2 u₂ (by rw [hr])
  exact ⟨AltMixedCompat.odd_of_standard w u₁ u₂ hp hq _ _ c hs,
    AltMixedCompat.even_of_standard w u₁ u₂ hp hq _ _ c hs⟩

end FLatticePaper.Tiles.MixedCompatBaseStep
