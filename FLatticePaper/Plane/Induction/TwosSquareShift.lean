import FLatticePaper.Plane.Induction.TwosSquareCover
import FLatticePaper.Plane.Induction.SquareClauses

/-! The square clause of the twos signed policy on all unit squares (task 72). The policy is equivariant under the period
lattice (`AliasOf`): a translate of a square by a lattice vector satisfies the clause when the square does. Every square has a
native lower-left translate (`native_copy_exists`), so the clause `sq_clause_native` on the native squares gives all squares,
and `SquareClauseSat` (the clause of the canonical signed policy) follows, with the selection `twosSel` the retained input. -/

namespace FLatticePaper.TwosEPolicy

open FLatticePaper FLatticePaper.Construction FLatticePaper.Induction Farey FLatticePaper.SquareClauses
open FLatticePaper.AndOrRank

/-- The translation vector of an alias has even coordinate sum. -/
theorem alias_parity {a : ℤ} {v v' : Site} (h : AliasOf a v v') : (v'.1 - v.1 + (v'.2 - v.2)) % 2 = 0 := by
  obtain ⟨i, l, rfl⟩ := h
  have h2 : (v.1 - i * (a + 1) + 2 * l - v.1) + (v.2 - i * (a - 1) - 2 * a * l - v.2) =
      2 * (-(i * a) + l - a * l) := by ring
  simp only
  rw [h2]
  simp

/-- The incoming neighbours of a translate are the translates of the incoming neighbours (even translations). -/
theorem incomingNeg_add (x : Site) (μ : Site) (hμ : (μ.1 + μ.2) % 2 = 0) :
    incomingNeg (x.1 + μ.1, x.2 + μ.2) = ((incomingNeg x).1 + μ.1, (incomingNeg x).2 + μ.2) := by
  unfold incomingNeg EvenSite
  by_cases h : (x.1 + x.2) % 2 = 0
  · have h' : ((x.1 + μ.1) + (x.2 + μ.2)) % 2 = 0 := by omega
    simp only [h, h', if_true]
    ext <;> (dsimp only; try ring)
  · have h' : ¬ ((x.1 + μ.1) + (x.2 + μ.2)) % 2 = 0 := by omega
    simp only [h, h', if_false]
    ext <;> (dsimp only; try ring)

theorem incomingPos_add (x : Site) (μ : Site) (hμ : (μ.1 + μ.2) % 2 = 0) :
    incomingPos (x.1 + μ.1, x.2 + μ.2) = ((incomingPos x).1 + μ.1, (incomingPos x).2 + μ.2) := by
  unfold incomingPos EvenSite
  by_cases h : (x.1 + x.2) % 2 = 0
  · have h' : ((x.1 + μ.1) + (x.2 + μ.2)) % 2 = 0 := by omega
    simp only [h, h', if_true]
    ext <;> (dsimp only; try ring)
  · have h' : ¬ ((x.1 + μ.1) + (x.2 + μ.2)) % 2 = 0 := by omega
    simp only [h, h', if_false]
    ext <;> (dsimp only; try ring)


/-- Edges are equivariant under even translations (the translation given by two integers). -/
theorem edge_add (i v : Site) (m1 m2 : ℤ) (hμ : (m1 + m2) % 2 = 0) :
    Edge (i.1 + m1, i.2 + m2) (v.1 + m1, v.2 + m2) ↔ Edge i v := by
  unfold Edge
  rw [incomingNeg_add v (m1, m2) hμ, incomingPos_add v (m1, m2) hμ]
  constructor
  · rintro (h | h)
    · left
      rw [Prod.ext_iff] at h ⊢
      simp only at h ⊢
      omega
    · right
      rw [Prod.ext_iff] at h ⊢
      simp only at h ⊢
      omega
  · rintro (h | h)
    · left
      rw [Prod.ext_iff] at h ⊢
      simp only at h ⊢
      omega
    · right
      rw [Prod.ext_iff] at h ⊢
      simp only at h ⊢
      omega

/-- The retained inputs of the twos policy are equivariant under a lattice alias: the same alias witnesses the free or the
non-free branch, and the Laplacian is constant along the alias (`hl`). -/
theorem twosSel_alias {a η : ℤ} {F : Field} {v v' : Site} (hA : AliasOf a v v') (hl : laplacian F v' = laplacian F v)
    (i : Site) :
    TwosSel a η F v i ↔ TwosSel a η F v' (i.1 + (v'.1 - v.1), i.2 + (v'.2 - v.2)) := by
  have hμ := alias_parity hA
  have hv' : v' = (v.1 + (v'.1 - v.1), v.2 + (v'.2 - v.2)) := Prod.ext (by simp) (by simp)
  have hE : ∀ x : Site, Edge (x.1 + (v'.1 - v.1), x.2 + (v'.2 - v.2)) v' ↔ Edge x v := by
    intro x
    have h := edge_add x v (v'.1 - v.1) (v'.2 - v.2) hμ
    rw [← hv'] at h
    exact h
  have hfree : ∀ u : Site, (AliasOf a v u ↔ AliasOf a v' u) := fun u =>
    ⟨fun h => aliasOf_trans (aliasOf_symm hA) h, fun h => aliasOf_trans hA h⟩
  unfold TwosSel
  rw [hl]
  apply or_congr
  · exact and_congr_right fun _ => (hE i).symm
  · apply and_congr_right
    intro _
    apply or_congr
    · constructor
      · rintro ⟨u, hu, hf, hi⟩
        refine ⟨u, (hfree u).mp hu, hf, ?_⟩
        rw [Prod.ext_iff] at hi ⊢
        simp only at hi ⊢
        omega
      · rintro ⟨u, hu, hf, hi⟩
        refine ⟨u, (hfree u).mpr hu, hf, ?_⟩
        rw [Prod.ext_iff] at hi ⊢
        simp only at hi ⊢
        omega
    · refine and_congr (not_congr (freeClass_alias hA)) ?_
      constructor
      · rintro ⟨u, hu, hn, hg, hi⟩
        refine ⟨u, (hfree u).mp hu, hn, hg, ?_⟩
        rw [Prod.ext_iff] at hi ⊢
        simp only at hi ⊢
        omega
      · rintro ⟨u, hu, hn, hg, hi⟩
        refine ⟨u, (hfree u).mpr hu, hn, hg, ?_⟩
        rw [Prod.ext_iff] at hi ⊢
        simp only at hi ⊢
        omega

/-- The corners of an alias shift by the same alias. -/
theorem alias_corner {a : ℤ} {u u' : Site} (hA : AliasOf a u u') (e : Site) :
    AliasOf a (u.1 + e.1, u.2 + e.2) (u'.1 + e.1, u'.2 + e.2) := by
  obtain ⟨i, l, rfl⟩ := hA
  exact ⟨i, l, by ext <;> simp <;> ring⟩

/-- The square clause is equivariant under the period lattice. -/
theorem sqClause_alias_shift {k : ℕ} {S : Field} {η : ℤ}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    {u u' : Site} (hA : AliasOf (2 * (k : ℤ) + 4) u u')
    (h : SqClause (2 * (k : ℤ) + 4) η (standardField (List.replicate (k + 1) Digit.two)) u) :
    SqClause (2 * (k : ℤ) + 4) η (standardField (List.replicate (k + 1) Digit.two)) u' := by
  obtain ⟨v, hv, hlap, i, hTS, hout⟩ := h
  have hv' : ∃ e : Site, (e = (0, 0) ∨ e = (1, 0) ∨ e = (0, 1) ∨ e = (1, 1)) ∧
      v = (u.1 + e.1, u.2 + e.2) := by
    rcases hv with rfl | rfl | rfl | rfl
    · exact ⟨(0, 0), by simp, by simp⟩
    · exact ⟨(1, 0), by simp, by simp⟩
    · exact ⟨(0, 1), by simp, by simp⟩
    · exact ⟨(1, 1), by simp, by simp⟩
  obtain ⟨e, he, rfl⟩ := hv'
  have hA' := alias_corner hA e
  have hlap' : laplacian (standardField (List.replicate (k + 1) Digit.two)) (u'.1 + e.1, u'.2 + e.2) = 0 := by
    rw [laplacian_twos_alias hagree hperiod hA']
    exact hlap
  refine ⟨(u'.1 + e.1, u'.2 + e.2), ?_, hlap', (i.1 + ((u'.1 + e.1) - (u.1 + e.1)), i.2 + ((u'.2 + e.2) - (u.2 + e.2))), ?_, ?_⟩
  · unfold SqCorner
    rcases he with rfl | rfl | rfl | rfl
    · simp
    · simp
    · simp
    · simp
  · exact (twosSel_alias hA' (laplacian_twos_alias hagree hperiod hA') i).mp hTS
  · unfold SqOut at hout ⊢
    obtain ⟨h1, h2, h3, h4⟩ := hout
    refine ⟨fun hc => h1 ?_, fun hc => h2 ?_, fun hc => h3 ?_, fun hc => h4 ?_⟩ <;>
      (rw [Prod.ext_iff] at hc ⊢; simp only at hc ⊢; omega)

/-- The square clause of an arbitrary unit square of the twos field, for both signs (from the native squares). -/
theorem sqClause_all {k : ℕ} {S : Field} {η : ℤ} (hη : η = 1 ∨ η = -1)
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    (a b : ℤ) :
    SqClause (2 * (k : ℤ) + 4) η (standardField (List.replicate (k + 1) Digit.two)) (a, b) := by
  have ha2 : (2 * (k : ℤ) + 4) % 2 = 0 := by omega
  obtain ⟨u, hu, hn⟩ := native_copy_exists ha2 (ladderOdd_valid_twos k) (a, b)
  have h := sq_clause_native k hagree hperiod η hη u.1 u.2 hn
  exact sqClause_alias_shift hagree hperiod (aliasOf_symm hu) h

/-- The selected input of the twos signed policy at a site: the retained input (unique at a white centre by the quota). -/
noncomputable def twosSelFun (k : ℕ) (η : ℤ) (F : Field) (c : Site) : Site :=
  Classical.epsilon (fun i => TwosSel (2 * (k : ℤ) + 4) η F c i)

/-- The square clause of the canonical signed policy (`SquareClauseSat`) for the selection of the twos policy. -/
theorem twos_squareClauseSat {k : ℕ} {S : Field} {η : ℤ} (hη : η = 1 ∨ η = -1)
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    (a b : ℤ) :
    SquareClauseSat (standardField (List.replicate (k + 1) Digit.two))
      (twosSelFun k η (standardField (List.replicate (k + 1) Digit.two))) a b := by
  obtain ⟨v, hv, hlap, i, hTS, hout⟩ := sqClause_all (S := S) hη hagree hperiod a b
  intro hall
  have hmem : v ∈ squareCorners a b := by
    unfold SqCorner at hv
    unfold squareCorners
    rcases hv with rfl | rfl | rfl | rfl <;> simp
  have hk := hall v hmem
  unfold keptInside at hk
  rw [if_neg (by rw [hlap]; norm_num)] at hk
  have hsel : twosSelFun k η (standardField (List.replicate (k + 1) Digit.two)) v = i := by
    have hex : ∃ j, TwosSel (2 * (k : ℤ) + 4) η (standardField (List.replicate (k + 1) Digit.two)) v j :=
      ⟨i, hTS⟩
    have hs := Classical.epsilon_spec hex
    exact (twos_white_quota k hagree hperiod η v hlap).2 _ _ hs hTS
  rw [hsel] at hk
  unfold squareCorners at hk
  unfold SqOut at hout
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with h | h | h | h
  · exact hout.1 h
  · exact hout.2.1 h
  · exact hout.2.2.1 h
  · exact hout.2.2.2 h

end FLatticePaper.TwosEPolicy
