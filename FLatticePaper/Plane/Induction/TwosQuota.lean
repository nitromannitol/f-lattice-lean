import FLatticePaper.Plane.Induction.TwosNativeCopy
import FLatticePaper.Plane.Induction.TwosDrifts
import FLatticePaper.Plane.Induction.TwosPeriods
import FLatticePaper.Plane.Induction.TwosValues

/-! The quota of the twos signed policy at the white centres (task 72): every white centre retains exactly one input.
The twos field is periodic under the lattice `⟨U, V⟩` (the child deck of `2^(k+1)`), so the Laplacian is constant along the
alias translates; a non-free white class has a native copy (`native_copy_exists`), its candidate guard holds there
(`native_white_cover`, and the freeness of the class), and the native copy is unique (`native_alias_unique`). -/

namespace FLatticePaper.TwosEPolicy

open FLatticePaper FLatticePaper.Construction FLatticePaper.Induction Farey

theorem twos_child_inUnitInterval (k : ℕ) :
    (frameAt (List.replicate (k + 1) Digit.two)).child.InUnitInterval :=
  ((frameAt (List.replicate (k + 1) Digit.two)).valid.current_interior .even).inUnitInterval

/-- The twos Laplacian is constant along the alias translates. -/
theorem laplacian_twos_alias {k : ℕ} {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    {c u : Site} (hu : AliasOf (2 * (k : ℤ) + 4) c u) :
    laplacian (standardField (List.replicate (k + 1) Digit.two)) u =
      laplacian (standardField (List.replicate (k + 1) Digit.two)) c := by
  obtain ⟨i, l, hi⟩ := hu
  have hF := twos_standardField_periods k hagree hperiod
  have hoff : PeriodDeck.combine (frameAt (List.replicate (k + 1) Digit.two)).child.modifiedDeck (-i) (-l) ∈
      (frameAt (List.replicate (k + 1) Digit.two)).child.modifiedDeck.span := ⟨-i, -l, rfl⟩
  have hper := laplacian_periodic_of_generatorPeriods (twos_child_inUnitInterval k) hF hoff c
  have hc : c + PeriodDeck.combine (frameAt (List.replicate (k + 1) Digit.two)).child.modifiedDeck (-i) (-l) = u := by
    simp only [PeriodDeck.combine, twos_kernel_explicit, twos_transverse_explicit]
    rw [hi]
    ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring
  rw [hc] at hper
  exact hper

/-- A white centre of a non-free class keeps the candidate input of its native copy. -/
theorem twosSel_white_nonfree_iff {a η : ℤ} {F : Field} {c i : Site} (h : laplacian F c = 0)
    (hnf : ¬ FreeClass a c) :
    TwosSel a η F c i ↔ ∃ u, AliasOf a c u ∧ NativeT a u.1 u.2 ∧ CandGuard a u.1 u.2 ∧
      i = (c.1 + (candDisp a u.1 u.2).1, c.2 + (candDisp a u.1 u.2).2) := by
  unfold TwosSel
  rw [h]
  constructor
  · rintro (h1 | ⟨-, (⟨u, hu, hf, _⟩ | ⟨-, hn⟩)⟩)
    · exact absurd h1.1 (by norm_num)
    · exact absurd ⟨u, hu, hf⟩ hnf
    · exact hn
  · intro hn
    exact Or.inr ⟨rfl, Or.inr ⟨hnf, hn⟩⟩

/-- The quota at a white centre of the twos field: some input is retained, and at most one. -/
theorem twos_white_quota (k : ℕ) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    (η : ℤ) (c : Site) (hw : laplacian (standardField (List.replicate (k + 1) Digit.two)) c = 0) :
    (∃ i, TwosSel (2 * (k : ℤ) + 4) η (standardField (List.replicate (k + 1) Digit.two)) c i) ∧
      ∀ i i', TwosSel (2 * (k : ℤ) + 4) η (standardField (List.replicate (k + 1) Digit.two)) c i →
        TwosSel (2 * (k : ℤ) + 4) η (standardField (List.replicate (k + 1) Digit.two)) c i' → i = i' := by
  have hvalid := ladderOdd_valid_twos k
  have ha2 : (2 * (k : ℤ) + 4) % 2 = 0 := by omega
  have ha4 : 4 ≤ 2 * (k : ℤ) + 4 := by omega
  by_cases hf : FreeClass (2 * (k : ℤ) + 4) c
  · obtain ⟨u, hu, hfu⟩ := hf
    refine ⟨⟨_, (twosSel_white_freeClass hw ⟨u, hu, hfu⟩).mpr ⟨u, hu, hfu, rfl⟩⟩, fun i i' hi hi' => ?_⟩
    exact twosSel_white_freeClass_eq ha4 hw ⟨u, hu, hfu⟩ hi hi'
  · have hnf := hf
    obtain ⟨u, hu, hn⟩ := native_copy_exists ha2 hvalid c
    have hlu : laplacian (standardField (List.replicate (k + 1) Digit.two)) u = 0 := by
      rw [laplacian_twos_alias hagree hperiod hu]
      exact hw
    have hguard : CandGuard (2 * (k : ℤ) + 4) u.1 u.2 := by
      rcases native_white_cover k hagree hperiod hn hlu with h | h | h | h
      · exact h
      · exact absurd ⟨u, hu, h⟩ hnf
      · obtain ⟨i, l, hi⟩ := hu
        exact absurd ⟨(u.1 + 2, u.2 - 2 * (2 * (k : ℤ) + 4)), ⟨i, l + 1, by rw [hi]; ext <;> simp <;> ring⟩, h⟩ hnf
      · obtain ⟨i, l, hi⟩ := hu
        exact absurd ⟨(u.1 - ((2 * (k : ℤ) + 4) + 1), u.2 - ((2 * (k : ℤ) + 4) - 1)),
          ⟨i + 1, l, by rw [hi]; ext <;> simp <;> ring⟩, h⟩ hnf
    refine ⟨⟨_, (twosSel_white_nonfree_iff hw hnf).mpr ⟨u, hu, hn, hguard, rfl⟩⟩, fun i i' hi hi' => ?_⟩
    rw [twosSel_white_nonfree_iff hw hnf] at hi hi'
    obtain ⟨v, hv, hvn, _, rfl⟩ := hi
    obtain ⟨v', hv', hvn', _, rfl⟩ := hi'
    have heq : v = v' := native_alias_unique ha4 hv hv' hvn hvn' hnf
    subst heq
    rfl

end FLatticePaper.TwosEPolicy
