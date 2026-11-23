import FLatticePaper.Plane.Induction.I3Local
import FLatticePaper.Plane.Induction.PermitMonotone
import FLatticePaper.Plane.Induction.SignedPolicy

/-! Task 38: the restricted no-fort condition from a constrained burning rank (the least-rank argument of `I3Local`, with the
strict rank replaced by the constrained one).

A constrained burning rank gives, at each centre, a permitted lower input for the quota: both for a black centre, one for a
white one. At the least-rank site of a restricted fort, every blocking input would then be a permitted lower input, which is
excluded by minimality. So no restricted fort lies in the half-space of the grade. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- A quota together with a rank strictly decreasing along the permitted inputs is a constrained burning rank. -/
theorem isConstrainedBurningRank_of_strict_quota {field : Field} {permits : Site → Site → Prop} {rank : Site → ℤ}
    (hbin : ∀ c, laplacian field c = -1 ∨ laplacian field c = 0)
    (hq : RetainQuota field permits)
    (hstrict : ∀ c i, Edge i c → permits c i → rank i < rank c) :
    IsConstrainedBurningRank field rank permits := by
  intro c
  rcases hbin c with hl | hl
  · obtain ⟨a, b⟩ := hq.1 c hl
    exact Or.inl ⟨hl, ⟨a, hstrict c _ (Or.inl rfl) a⟩, ⟨b, hstrict c _ (Or.inr rfl) b⟩⟩
  · rcases hq.2 c hl with a | b
    · exact Or.inr ⟨hl, Or.inl ⟨a, hstrict c _ (Or.inl rfl) a⟩⟩
    · exact Or.inr ⟨hl, Or.inr ⟨b, hstrict c _ (Or.inr rfl) b⟩⟩

/-- **Least-rank argument for a constrained burning rank.** A rank satisfying the constrained condition for the permits, and
dominating `κ · grade − C` with `κ > 0`, forbids a restricted fort in a half-space of the grade. -/
theorem restrictedNoFort_of_constrainedRank {field grade : Field} {permits : Site → Site → Prop}
    (rank : Site → ℤ) (hcon : IsConstrainedBurningRank field rank permits)
    (κ C : ℤ) (hκ : 0 < κ) (hbound : ∀ x, κ * grade x - C ≤ rank x) :
    RestrictedNoFort field grade permits := by
  classical
  intro level fort hne hfort hlevel
  obtain ⟨x0, hx0⟩ := hne
  obtain ⟨least, ⟨s, hs, hsv⟩, hmin⟩ := Int.exists_least_of_bdd
    (P := fun v => ∃ x ∈ fort, rank x = v)
    ⟨κ * level - C, by
      rintro _ ⟨x, hx, rfl⟩
      have h1 := mul_le_mul_of_nonneg_left (hlevel x hx) hκ.le
      have h2 := hbound x
      linarith⟩
    ⟨rank x0, x0, hx0, rfl⟩
  -- a lower site of the least site cannot lie in the fort
  have key : ∀ i, rank i < rank s → i ∈ fort → False := by
    intro i hlt hi
    have h1 := hmin (rank i) ⟨i, hi, rfl⟩
    omega
  rcases hfort s hs with ⟨hl, hA | hB⟩ | ⟨hl, hA, hB⟩
  · rcases hcon s with ⟨hl2, hn, hp⟩ | ⟨hl2, hn | hp⟩
    · exact hA.elim (fun h => key _ hn.2 h) (fun h => h hn.1)
    all_goals exact absurd (hl.symm.trans hl2) (by norm_num)
  · rcases hcon s with ⟨hl2, hn, hp⟩ | ⟨hl2, hn | hp⟩
    · exact hB.elim (fun h => key _ hp.2 h) (fun h => h hp.1)
    all_goals exact absurd (hl.symm.trans hl2) (by norm_num)
  · rcases hcon s with ⟨hl2, hn, hp⟩ | ⟨hl2, hn | hp⟩
    · exact absurd (hl.symm.trans hl2) (by norm_num)
    · exact hA.elim (fun h => key _ hn.2 h) (fun h => h hn.1)
    · exact hB.elim (fun h => key _ hp.2 h) (fun h => h hp.1)

/-- **The restricted no-fort condition from a constrained rank with grade increments.** A rank whose increments along the two
generators of the deck are a common positive multiple of the grade's increments, and which is constrained for the permits,
gives the restricted no-fort condition. -/
theorem restrictedNoFort_of_constrained_rankGrade {field grade : Field} {permits : Site → Site → Prop}
    {deck : PeriodDeck} (hpos : 0 < deck.det) (rank : Site → ℤ) (κ : ℤ) (hκ : 0 < κ)
    (hcon : IsConstrainedBurningRank field rank permits)
    (hK : ∀ x, rank (x + deck.kernel) - rank x = κ * (grade (x + deck.kernel) - grade x))
    (hT : ∀ x, rank (x + deck.transverse) - rank x = κ * (grade (x + deck.transverse) - grade x)) :
    RestrictedNoFort field grade permits := by
  have hK' : ∀ y, (rank - fun z => κ * grade z) (y + deck.kernel) = (rank - fun z => κ * grade z) y := by
    intro y
    simp only [Pi.sub_apply]
    linear_combination hK y
  have hT' : ∀ y, (rank - fun z => κ * grade z) (y + deck.transverse) =
      (rank - fun z => κ * grade z) y := by
    intro y
    simp only [Pi.sub_apply]
    linear_combination hT y
  have hinv : ∀ x i j, (rank - fun z => κ * grade z) (x + deck.combine i j) =
      (rank - fun z => κ * grade z) x :=
    fun x i j => invariant_of_combine hK' hT' x i j
  obtain ⟨C, hC⟩ := exists_lower_bound_of_periodic hpos hinv
  exact restrictedNoFort_of_constrainedRank rank hcon κ C hκ (fun x => by
    have h := hC x
    simp only [Pi.sub_apply] at h
    linarith)

end FLatticePaper.Induction
