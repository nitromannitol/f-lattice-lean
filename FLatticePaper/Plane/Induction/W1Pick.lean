import FLatticePaper.Plane.Induction.W1Constructor

/-! Task 46, step 2: the Pick step, in the form the rectangle supports.

The deck of the child is `U = (d, n)` and `V = (n − d, d + n)` (the unmodified deck, since `L = d + n` is even), with
`det = T`. On the grades the deck acts by `t(z + iU + jV) = t(z) − jT` and `s(z + iU + jV) = s(z) + iT`, and it preserves the parity
of sites. Consequences proved here:
* uniqueness: two points of `StrictInterior` in one deck class coincide (each open rectangle has width at most `T` in `t` and `s`);
* covering: every deck class has a representative in the closed rectangle `closedRect`;
* `pickUnique`: a deck class all of whose closed-rectangle points lie in `StrictInterior` has exactly one `StrictInterior`
  representative.
The count `T − d − L` of the interior classes needs the boundary classes (the arc sites of section 1) and is not proved here. -/

namespace FLatticePaper.W1Pick

open FLatticePaper FLatticePaper.W1 FLatticePaper.Induction

/-- The deck translation `i U + j V`, with `U = (d, n)` and `V = (n − d, d + n)`. -/
def lat (n d i j : ℤ) : Site := (i * d + j * (n - d), i * n + j * (d + n))

theorem w1t_lat (n d : ℤ) (z : Site) (i j : ℤ) :
    w1t n d (z + lat n d i j) = w1t n d z - j * w1T n d := by
  show n * (z.1 + (i * d + j * (n - d))) - d * (z.2 + (i * n + j * (d + n))) =
    (n * z.1 - d * z.2) - j * (d ^ 2 + 2 * d * n - n ^ 2)
  ring

theorem w1s_lat (n d : ℤ) (z : Site) (i j : ℤ) :
    w1s n d (z + lat n d i j) = w1s n d z + i * w1T n d := by
  show (d + n) * (z.1 + (i * d + j * (n - d))) + (d - n) * (z.2 + (i * n + j * (d + n))) =
    ((d + n) * z.1 + (d - n) * z.2) + i * (d ^ 2 + 2 * d * n - n ^ 2)
  ring

theorem evenSite_lat (n d : ℤ) (hLev : (d + n) % 2 = 0) (z : Site) (i j : ℤ) :
    EvenSite (z + lat n d i j) ↔ EvenSite z := by
  obtain ⟨k, hk⟩ : ∃ k, d + n = 2 * k := ⟨(d + n) / 2, by omega⟩
  have key : (z + lat n d i j).1 + (z + lat n d i j).2 = (z.1 + z.2) + 2 * (i * k + j * n) := by
    show (z.1 + (i * d + j * (n - d))) + (z.2 + (i * n + j * (d + n))) = (z.1 + z.2) + 2 * (i * k + j * n)
    linear_combination i * hk
  unfold EvenSite
  rw [key, Int.add_mul_emod_self_left]

/-- The uniqueness estimate: two grade differences of strict-interior points are less than `T`. -/
theorem strictInterior_t_diff (n d : ℤ) (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d)
    (w1 w2 : Site) (h1 : StrictInterior n d w1) (h2 : StrictInterior n d w2)
    (hp : EvenSite w1 ↔ EvenSite w2) :
    w1t n d w1 - w1t n d w2 < w1T n d ∧ w1t n d w2 - w1t n d w1 < w1T n d ∧
      w1s n d w1 - w1s n d w2 < w1T n d ∧ w1s n d w2 - w1s n d w1 < w1T n d := by
  have hT : 0 < w1T n d := by
    show 0 < d ^ 2 + 2 * d * n - n ^ 2
    nlinarith
  by_cases hE : EvenSite w1
  · have hE2 : EvenSite w2 := hp.1 hE
    simp only [StrictInterior, w1a, w1b, w1c, w1h, hE, hE2, if_true, add_zero] at h1 h2
    obtain ⟨a1, a2, a3, a4⟩ := h1
    obtain ⟨b1, b2, b3, b4⟩ := h2
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  · have hE2 : ¬ EvenSite w2 := fun h => hE (hp.2 h)
    simp only [StrictInterior, w1a, w1b, w1c, w1h, hE, hE2, if_false] at h1 h2
    obtain ⟨a1, a2, a3, a4⟩ := h1
    obtain ⟨b1, b2, b3, b4⟩ := h2
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- **Uniqueness.** Two strict-interior points of one deck class coincide. -/
theorem strictInterior_eq_of_lat (n d : ℤ) (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d) (hLev : (d + n) % 2 = 0)
    (z : Site) (i1 j1 i2 j2 : ℤ)
    (h1 : StrictInterior n d (z + lat n d i1 j1)) (h2 : StrictInterior n d (z + lat n d i2 j2)) :
    z + lat n d i1 j1 = z + lat n d i2 j2 := by
  have hp : EvenSite (z + lat n d i1 j1) ↔ EvenSite (z + lat n d i2 j2) :=
    (evenSite_lat n d hLev z i1 j1).trans (evenSite_lat n d hLev z i2 j2).symm
  obtain ⟨a1, a2, a3, a4⟩ := strictInterior_t_diff n d hn1 hnd _ _ h1 h2 hp
  rw [w1t_lat, w1t_lat] at a1 a2
  rw [w1s_lat, w1s_lat] at a3 a4
  have hT : 0 < w1T n d := by
    show 0 < d ^ 2 + 2 * d * n - n ^ 2
    nlinarith
  have hj : j1 = j2 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · nlinarith
    · nlinarith
  have hi : i1 = i2 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · nlinarith
    · nlinarith
  rw [hi, hj]

/-- **Covering.** Every deck class has a representative in the closed rectangle `closedRect`. -/
theorem exists_closed_rep (n d : ℤ) (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d) (hLev : (d + n) % 2 = 0) (z : Site) :
    ∃ i j : ℤ, closedRect n d (z + lat n d i j) := by
  have hT : 0 < w1T n d := by
    show 0 < d ^ 2 + 2 * d * n - n ^ 2
    nlinarith
  have hL4 : 4 ≤ d + n := by omega
  have hdn2 : 2 ≤ d := by omega
  have hTne : w1T n d ≠ 0 := hT.ne'
  by_cases hE : EvenSite z
  · have hp : EvenSite (z + lat n d (-((w1s n d z - 0) / w1T n d)) ((w1t n d z - (2 - w1T n d)) / w1T n d)) :=
      (evenSite_lat n d hLev z _ _).2 hE
    refine ⟨-((w1s n d z - 0) / w1T n d), (w1t n d z - (2 - w1T n d)) / w1T n d, ?_⟩
    unfold closedRect
    rw [if_pos hp, w1t_lat, w1s_lat]
    have ht1 := Int.emod_def (w1t n d z - (2 - w1T n d)) (w1T n d)
    have ht2 := Int.emod_nonneg (w1t n d z - (2 - w1T n d)) hTne
    have ht3 := Int.emod_lt_of_pos (w1t n d z - (2 - w1T n d)) hT
    have hs1 := Int.emod_def (w1s n d z - 0) (w1T n d)
    have hs2 := Int.emod_nonneg (w1s n d z - 0) hTne
    have hs3 := Int.emod_lt_of_pos (w1s n d z - 0) hT
    refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
  · have hp : ¬ EvenSite (z + lat n d (-((w1s n d z - (2 - d + n)) / w1T n d))
        ((w1t n d z - (n - w1T n d)) / w1T n d)) := fun h => hE ((evenSite_lat n d hLev z _ _).1 h)
    refine ⟨-((w1s n d z - (2 - d + n)) / w1T n d), (w1t n d z - (n - w1T n d)) / w1T n d, ?_⟩
    unfold closedRect
    rw [if_neg hp, w1t_lat, w1s_lat]
    have ht1 := Int.emod_def (w1t n d z - (n - w1T n d)) (w1T n d)
    have ht2 := Int.emod_nonneg (w1t n d z - (n - w1T n d)) hTne
    have ht3 := Int.emod_lt_of_pos (w1t n d z - (n - w1T n d)) hT
    have hs1 := Int.emod_def (w1s n d z - (2 - d + n)) (w1T n d)
    have hs2 := Int.emod_nonneg (w1s n d z - (2 - d + n)) hTne
    have hs3 := Int.emod_lt_of_pos (w1s n d z - (2 - d + n)) hT
    refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

/-- A deck class is a boundary class when it has a closed-rectangle point outside `StrictInterior`. -/
def boundaryClass (n d : ℤ) (z : Site) : Prop :=
  ∃ i j : ℤ, closedRect n d (z + lat n d i j) ∧ ¬ StrictInterior n d (z + lat n d i j)

/-- **PickUniqueness (non-boundary classes).** A deck class that is not a boundary class has exactly one representative in
`StrictInterior`. (The count `T − d − L` of the non-boundary classes is not proved here.) -/
theorem pickUnique (n d : ℤ) (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d) (hLev : (d + n) % 2 = 0) (z : Site)
    (hnb : ¬ boundaryClass n d z) :
    ∃! w : Site, StrictInterior n d w ∧ ∃ i j : ℤ, w = z + lat n d i j := by
  have hall : ∀ i j : ℤ, closedRect n d (z + lat n d i j) → StrictInterior n d (z + lat n d i j) := by
    intro i j hc
    by_contra hns
    exact hnb ⟨i, j, hc, hns⟩
  obtain ⟨i0, j0, hc0⟩ := exists_closed_rep n d hn1 hnd hLev z
  refine ⟨z + lat n d i0 j0, ⟨hall i0 j0 hc0, i0, j0, rfl⟩, ?_⟩
  rintro w ⟨hw, i, j, rfl⟩
  exact strictInterior_eq_of_lat n d hn1 hnd hLev z i j i0 j0 hw (hall i0 j0 hc0)

end FLatticePaper.W1Pick
