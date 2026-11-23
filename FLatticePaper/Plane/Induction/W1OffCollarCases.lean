import FLatticePaper.Plane.Induction.W1OffCollar

/-! # Task 90 (hsq): the case analysis of the off-collar lemma, in the grades (t, s)

Each arc membership of a site is stated through its grades `(t, s)` and its parity: `CH` (bottom H arc, with the top arc `CH` at `t + T`)
and `CV` (left V arc, with the right arc at `s − T`). A site `z + δ` has grades `(t + n δ₁ − d δ₂, s + (d+n) δ₁ + (d−n) δ₂)`, so every
witness condition is linear in `(t, s, n, d, T)` once the parity is fixed. The lattice exclusions of `W1OffCollar` supply the remaining facts. -/

namespace FLatticePaper.W1OffCollarCases

open FLatticePaper FLatticePaper.W1 FLatticePaper.W1OffCollar

/-- The closed rectangle by parity, in the grades. -/
def closedTS (n d : ℤ) (ev : Prop) (t s : ℤ) : Prop :=
  (ev ∧ 2 - w1T n d ≤ t ∧ t ≤ d + n - 2 ∧ 0 ≤ s ∧ s ≤ w1T n d + 2 * n) ∨
    (¬ ev ∧ n - w1T n d ≤ t ∧ t ≤ d ∧ 2 - d + n ≤ s ∧ s ≤ w1T n d + d + n - 2)

theorem closedRect_ts (n d : ℤ) (z : Site) :
    closedRect n d z ↔ closedTS n d (EvenSite z) (w1t n d z) (w1s n d z) :=
  closedRect_iff n d z


/-- The grades of the top translate `p − (n − d, d + n)`: `t` shifts by `T`, `s` is unchanged. -/
theorem w1t_top (n d : ℤ) (p : Site) :
    w1t n d (p.1 - (n - d), p.2 - (d + n)) = w1t n d p + w1T n d := by
  unfold w1t w1T
  ring

theorem w1s_top (n d : ℤ) (p : Site) :
    w1s n d (p.1 - (n - d), p.2 - (d + n)) = w1s n d p := by
  unfold w1s
  ring

/-- `t = 0` on the lattice forces `s` to a multiple of `T`: no value of `s` in `(0, T)`. -/
theorem no_t0_s_range (n d : ℤ) (hcop : IsCoprime n d) (hd : d ≠ 0) (u : Site)
    (ht : w1t n d u = 0) (hlo : 0 < w1s n d u) (hhi : w1s n d u < w1T n d) (hT : 0 < w1T n d) : False := by
  obtain ⟨k, hk⟩ := FLatticePaper.W1OffCollar.s_of_t_zero n d hcop hd u ht
  rw [hk] at hlo hhi
  have : k ≤ 0 ∨ 1 ≤ k := by omega
  rcases this with h5 | h5 <;> nlinarith

/-- `t = −d` on the lattice forces `s` outside `(L − 2, T + 2 − d + n)`: the strict odd range is empty. -/
theorem T_pos (n d : ℤ) (hn : 3 ≤ n) (hnd : n + 2 ≤ d) : 0 < w1T n d := by
  unfold w1T
  nlinarith

theorem no_strict_odd_tnegd (n d : ℤ) (hn : 1 ≤ n) (hnd : n + 2 ≤ d) (hT : 0 < w1T n d)
    (hcop : IsCoprime n d) (z : Site) (hod : ¬ EvenSite z) (hz : StrictInterior n d z)
    (ht : w1t n d z = -d) : False := by
  rw [strict_odd n d z hod] at hz
  obtain ⟨h1, h2, h3, h4⟩ := hz
  have hd0 : d ≠ 0 := by
    intro h
    linarith [hn, hnd]
  obtain ⟨k, hk⟩ := FLatticePaper.W1OffCollar.s_of_t_negd n d hcop hd0 z ht
  rw [hk] at h3 h4
  have : k ≤ 0 ∨ 1 ≤ k := by omega
  rcases this with h5 | h5 <;> nlinarith [hn, hnd, hT]

/-- The reflection of the child: `z ↦ (n + 1, 2n + d − 1) − z` (the centre of the sheet exchange). -/
def mirror (n d : ℤ) (z : Site) : Site := (n + 1 - z.1, 2 * n + d - 1 - z.2)

theorem mirror_t (n d : ℤ) (z : Site) :
    w1t n d (mirror n d z) = (d + n) - w1T n d - w1t n d z := by
  unfold mirror w1t w1T
  ring

theorem mirror_s (n d : ℤ) (z : Site) :
    w1s n d (mirror n d z) = w1T n d + 2 * n - w1s n d z := by
  unfold mirror w1s w1T
  ring

theorem mirror_even (n d : ℤ) (hno : n % 2 = 1) (hdo : d % 2 = 1) (z : Site) :
    EvenSite (mirror n d z) ↔ EvenSite z := by
  unfold mirror EvenSite
  omega

theorem mirror_strict (n d : ℤ) (hno : n % 2 = 1) (hdo : d % 2 = 1)
    (z : Site) (hz : StrictInterior n d z) : StrictInterior n d (mirror n d z) := by
  by_cases hev : EvenSite z
  · have hm := (mirror_even n d hno hdo z).2 hev
    rw [strict_even n d z hev] at hz
    rw [strict_even n d (mirror n d z) hm, mirror_t, mirror_s]
    obtain ⟨h1, h2, h3, h4⟩ := hz
    refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
  · have hm : ¬ EvenSite (mirror n d z) := fun h => hev ((mirror_even n d hno hdo z).1 h)
    rw [strict_odd n d z hev] at hz
    rw [strict_odd n d (mirror n d z) hm, mirror_t, mirror_s]
    obtain ⟨h1, h2, h3, h4⟩ := hz
    refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

theorem T_pos' (n d : ℤ) (hn : 1 ≤ n) (hnd : n + 2 ≤ d) : 0 < w1T n d := by
  unfold w1T
  nlinarith [hn, hnd]

/-- The bottom H arc, in the grades `(t, s)` of its vertex, with the neighbour below at `(t + d, s − (d − n))`. -/
def CH (n d : ℤ) (ev : Prop) (t s : ℤ) : Prop :=
  closedTS n d ev t s ∧ ¬ closedTS n d (¬ ev) (t + d) (s - (d - n)) ∧ hSp n d t

/-- The left V arc, in the grades of its vertex, with the neighbour to the left at `(t − n, s − (d + n))`. -/
def CV (n d : ℤ) (ev : Prop) (t s : ℤ) : Prop :=
  closedTS n d ev t s ∧ ¬ closedTS n d (¬ ev) (t - n) (s - (d + n)) ∧ vSp n d s

theorem freeHn_CH (n d : ℤ) (p : Site) :
    freeHn n d p ↔ CH n d (EvenSite p) (w1t n d p) (w1s n d p) := by
  have e1 : w1t n d (p.1, p.2 - 1) = w1t n d p + d := FLatticePaper.W1Exit.t_negO n d p.1 p.2
  have e2 : w1s n d (p.1, p.2 - 1) = w1s n d p - (d - n) := FLatticePaper.W1Exit.s_negO n d p.1 p.2
  have e3 : EvenSite (p.1, p.2 - 1) = ¬ EvenSite p := propext (by simp only [EvenSite]; omega)
  unfold freeHn CH
  rw [closedRect_ts n d p, closedRect_ts n d (p.1, p.2 - 1), e1, e2, e3]

theorem freeVn_CV (n d : ℤ) (p : Site) :
    freeVn n d p ↔ CV n d (EvenSite p) (w1t n d p) (w1s n d p) := by
  have e1 : w1t n d (p.1 - 1, p.2) = w1t n d p - n := FLatticePaper.W1Exit.t_negE n d p.1 p.2
  have e2 : w1s n d (p.1 - 1, p.2) = w1s n d p - (d + n) := FLatticePaper.W1Exit.s_negE n d p.1 p.2
  have e3 : EvenSite (p.1 - 1, p.2) = ¬ EvenSite p := propext (by simp only [EvenSite]; omega)
  unfold freeVn CV
  rw [closedRect_ts n d p, closedRect_ts n d (p.1 - 1, p.2), e1, e2, e3]

/-- A collar point: within Chebyshev distance one of a vertex of the bottom H arc, the left V arc, the top arc `freeH + V`, or the right
arc `freeV + U`, with `U = (d, n)` and `V = (n − d, d + n)`. -/
def Collar (n d : ℤ) (z : Site) : Prop :=
  ∃ v : Site, |v.1 - z.1| ≤ 1 ∧ |v.2 - z.2| ≤ 1 ∧
    (freeHn n d v ∨ freeVn n d v ∨ freeHn n d (v.1 - (n - d), v.2 - (d + n)) ∨ freeVn n d (v.1 - d, v.2 - n))

/-- The strict interior, by parity, in the grades of a site. -/
theorem strict_grades (n d : ℤ) (p : Site) :
    StrictInterior n d p ↔
      ((EvenSite p ∧ d + n - 2 - w1T n d < w1t n d p ∧ w1t n d p < 2 ∧ 2 * n < w1s n d p ∧ w1s n d p < w1T n d) ∨
        (¬ EvenSite p ∧ d - w1T n d < w1t n d p ∧ w1t n d p < n ∧ d + n - 2 < w1s n d p ∧
          w1s n d p < w1T n d + (2 - d + n))) := by
  by_cases h : EvenSite p
  · rw [strict_even n d p h]
    simp [h]
  · rw [strict_odd n d p h]
    simp [h]

/-- `T` is even (`n`, `d` odd). -/
theorem T_even (n d : ℤ) (hno : n % 2 = 1) (hdo : d % 2 = 1) : w1T n d % 2 = 0 := by
  obtain ⟨L', hL⟩ : ∃ L' : ℤ, d + n = 2 * L' := ⟨(d + n) / 2, by omega⟩
  rw [T_half n d L' hL]
  omega

/-- The s-grade of a site is even. -/
theorem s_even (n d : ℤ) (hno : n % 2 = 1) (hdo : d % 2 = 1) (z : Site) : w1s n d z % 2 = 0 := by
  obtain ⟨a, ha⟩ : ∃ a : ℤ, d + n = 2 * a := ⟨(d + n) / 2, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b : ℤ, d - n = 2 * b := ⟨(d - n) / 2, by omega⟩
  have : w1s n d z = 2 * (a * z.1 + b * z.2) := by
    unfold w1s
    linear_combination z.1 * ha + z.2 * hb
  omega

/-- The top arc `freeH + V`: its grades are shifted by `T` in `t`. -/
theorem freeHn_top (n d : ℤ) (p : Site) :
    freeHn n d (p.1 - (n - d), p.2 - (d + n)) ↔
      CH n d (EvenSite p) (w1t n d p + w1T n d) (w1s n d p) := by
  have e1 : w1t n d (p.1 - (n - d), p.2 - (d + n)) = w1t n d p + w1T n d := by
    unfold w1t w1T
    ring
  have e2 : w1s n d (p.1 - (n - d), p.2 - (d + n)) = w1s n d p := by
    unfold w1s
    ring
  have e3 : EvenSite (p.1 - (n - d), p.2 - (d + n)) = EvenSite p :=
    propext (by simp only [EvenSite]; omega)
  rw [freeHn_CH, e1, e2, e3]

/-- The right arc `freeV + U`: its grades are shifted by `−T` in `s`. -/
theorem freeVn_right (n d : ℤ) (hno : n % 2 = 1) (hdo : d % 2 = 1) (p : Site) :
    freeVn n d (p.1 - d, p.2 - n) ↔ CV n d (EvenSite p) (w1t n d p) (w1s n d p - w1T n d) := by
  have e1 : w1t n d (p.1 - d, p.2 - n) = w1t n d p := by
    unfold w1t
    ring
  have e2 : w1s n d (p.1 - d, p.2 - n) = w1s n d p - w1T n d := by
    unfold w1s w1T
    ring
  have e3 : EvenSite (p.1 - d, p.2 - n) = EvenSite p :=
    propext (by simp only [EvenSite]; omega)
  rw [freeVn_CV, e1, e2, e3]

/-- A `δ = (0, −1)` neighbour of an even strict site: the violated edge is `A` (the witness is the neighbour on the bottom arc) or `C`
(on the left arc). -/
theorem down_even (n d : ℤ) (hn : 3 ≤ n) (hnd : n + 2 ≤ d) (hno : n % 2 = 1) (hdo : d % 2 = 1)
    (z : Site) (hev : EvenSite z) (hs : StrictInterior n d z)
    (hw : ¬ StrictInterior n d (z.1 + 0, z.2 + -1)) : Collar n d z := by
  have hspar := s_even n d hno hdo z
  have hTe := T_even n d hno hdo
  have hpar := t_even_of n d hno hdo z hev
  rw [strict_even n d z hev] at hs
  obtain ⟨h1, h2, h3, h4⟩ := hs
  rw [strict_grades, tv n d z 0 (-1), sv n d z 0 (-1)] at hw
  have hzp : (z.1 + z.2) % 2 = 0 := hev
  by_cases hA : n ≤ w1t n d z + d
  · refine ⟨(z.1 + 0, z.2 + -1), ?_, ?_, Or.inl ((freeHn_CH n d _).2 ?_)⟩
    · simp
    · simp
    · rw [tv n d z 0 (-1), sv n d z 0 (-1)]
      unfold CH closedTS hSp
      simp only [EvenSite] at hw ⊢
      omega
  · refine ⟨(z.1 + 0, z.2 + -1), ?_, ?_, Or.inr (Or.inl ((freeVn_CV n d _).2 ?_))⟩
    · simp
    · simp
    · rw [tv n d z 0 (-1), sv n d z 0 (-1)]
      unfold CV closedTS vSp
      simp only [EvenSite] at hw ⊢
      omega

/-- `δ = (0, 1)` on an even strict site: `B` (the top arc at the neighbour) or `D` (the right arc at the neighbour). -/
theorem up_even (n d : ℤ) (hn : 3 ≤ n) (hnd : n + 2 ≤ d) (hno : n % 2 = 1) (hdo : d % 2 = 1)
    (z : Site) (hev : EvenSite z) (hs : StrictInterior n d z)
    (hw : ¬ StrictInterior n d (z.1 + 0, z.2 + 1)) : Collar n d z := by
  have hspar := s_even n d hno hdo z
  have hTe := T_even n d hno hdo
  have hpar := t_even_of n d hno hdo z hev
  rw [strict_even n d z hev] at hs
  obtain ⟨h1, h2, h3, h4⟩ := hs
  rw [strict_grades, tv n d z 0 1, sv n d z 0 1] at hw
  have hzp : (z.1 + z.2) % 2 = 0 := hev
  by_cases hB : w1t n d z - d ≤ d - w1T n d
  · refine ⟨(z.1 + 0, z.2 + 1), ?_, ?_, Or.inr (Or.inr (Or.inl ((freeHn_top n d (z.1 + 0, z.2 + 1)).2 ?_)))⟩
    · simp
    · simp
    · rw [tv n d z 0 1, sv n d z 0 1]
      unfold CH closedTS hSp
      simp only [EvenSite] at hw ⊢
      omega
  · refine ⟨(z.1 + 0, z.2 + 1), ?_, ?_, Or.inr (Or.inr (Or.inr ((freeVn_right n d hno hdo (z.1 + 0, z.2 + 1)).2 ?_)))⟩
    · simp
    · simp
    · rw [tv n d z 0 1, sv n d z 0 1]
      unfold CV closedTS vSp
      simp only [EvenSite] at hw ⊢
      omega

/-- `δ = (1, 0)` on an even strict site: `A` (the bottom arc at the neighbour) or `D` (the right arc at the neighbour). -/
theorem right_even (n d : ℤ) (hn : 3 ≤ n) (hnd : n + 2 ≤ d) (hno : n % 2 = 1) (hdo : d % 2 = 1)
    (z : Site) (hev : EvenSite z) (hs : StrictInterior n d z)
    (hw : ¬ StrictInterior n d (z.1 + 1, z.2 + 0)) : Collar n d z := by
  have hspar := s_even n d hno hdo z
  have hTe := T_even n d hno hdo
  have hpar := t_even_of n d hno hdo z hev
  rw [strict_even n d z hev] at hs
  obtain ⟨h1, h2, h3, h4⟩ := hs
  rw [strict_grades, tv n d z 1 0, sv n d z 1 0] at hw
  have hzp : (z.1 + z.2) % 2 = 0 := hev
  by_cases hA : n ≤ w1t n d z + n
  · refine ⟨(z.1 + 1, z.2 + 0), ?_, ?_, Or.inl ((freeHn_CH n d (z.1 + 1, z.2 + 0)).2 ?_)⟩
    · simp
    · simp
    · rw [tv n d z 1 0, sv n d z 1 0]
      unfold CH closedTS hSp
      simp only [EvenSite] at hw ⊢
      omega
  · refine ⟨(z.1 + 1, z.2 + 0), ?_, ?_, Or.inr (Or.inr (Or.inr ((freeVn_right n d hno hdo (z.1 + 1, z.2 + 0)).2 ?_)))⟩
    · simp
    · simp
    · rw [tv n d z 1 0, sv n d z 1 0]
      unfold CV closedTS vSp
      simp only [EvenSite] at hw ⊢
      omega

/-- `δ = (−1, 0)` on an even strict site: `B` (the top arc at the neighbour) or `C` (the left arc at the neighbour). -/
theorem left_even (n d : ℤ) (hn : 3 ≤ n) (hnd : n + 2 ≤ d) (hno : n % 2 = 1) (hdo : d % 2 = 1)
    (z : Site) (hev : EvenSite z) (hs : StrictInterior n d z)
    (hw : ¬ StrictInterior n d (z.1 + -1, z.2 + 0)) : Collar n d z := by
  have hspar := s_even n d hno hdo z
  have hTe := T_even n d hno hdo
  have hpar := t_even_of n d hno hdo z hev
  rw [strict_even n d z hev] at hs
  obtain ⟨h1, h2, h3, h4⟩ := hs
  rw [strict_grades, tv n d z (-1) 0, sv n d z (-1) 0] at hw
  have hzp : (z.1 + z.2) % 2 = 0 := hev
  by_cases hB : w1t n d z - n ≤ d - w1T n d
  · refine ⟨(z.1 + -1, z.2 + 0), ?_, ?_, Or.inr (Or.inr (Or.inl ((freeHn_top n d (z.1 + -1, z.2 + 0)).2 ?_)))⟩
    · simp
    · simp
    · rw [tv n d z (-1) 0, sv n d z (-1) 0]
      unfold CH closedTS hSp
      simp only [EvenSite] at hw ⊢
      omega
  · refine ⟨(z.1 + -1, z.2 + 0), ?_, ?_, Or.inr (Or.inl ((freeVn_CV n d (z.1 + -1, z.2 + 0)).2 ?_))⟩
    · simp
    · simp
    · rw [tv n d z (-1) 0, sv n d z (-1) 0]
      unfold CV closedTS vSp
      simp only [EvenSite] at hw ⊢
      omega

/-- `δ = (0, −1)` on an odd strict site: `A` (bottom arc) or `C` (left arc) at the neighbour. -/
theorem down_odd (n d : ℤ) (hn : 3 ≤ n) (hnd : n + 2 ≤ d) (hno : n % 2 = 1) (hdo : d % 2 = 1)
    (z : Site) (hod : ¬ EvenSite z) (hs : StrictInterior n d z)
    (hw : ¬ StrictInterior n d (z.1 + 0, z.2 + -1)) : Collar n d z := by
  have hspar := s_even n d hno hdo z
  have hTe := T_even n d hno hdo
  have hpar := t_odd_of n d hno hdo z hod
  rw [strict_odd n d z hod] at hs
  obtain ⟨h1, h2, h3, h4⟩ := hs
  rw [strict_grades, tv n d z 0 (-1), sv n d z 0 (-1)] at hw
  have hzp : ¬ (z.1 + z.2) % 2 = 0 := hod
  by_cases hA : 2 ≤ w1t n d z + d
  · refine ⟨(z.1 + 0, z.2 + -1), ?_, ?_, Or.inl ((freeHn_CH n d (z.1 + 0, z.2 + -1)).2 ?_)⟩
    · simp
    · simp
    · rw [tv n d z 0 (-1), sv n d z 0 (-1)]
      unfold CH closedTS hSp
      simp only [EvenSite] at hw ⊢
      omega
  · refine ⟨(z.1 + 0, z.2 + -1), ?_, ?_, Or.inr (Or.inl ((freeVn_CV n d (z.1 + 0, z.2 + -1)).2 ?_))⟩
    · simp
    · simp
    · rw [tv n d z 0 (-1), sv n d z 0 (-1)]
      unfold CV closedTS vSp
      simp only [EvenSite] at hw ⊢
      omega

/-- `δ = (0, 1)` on an odd strict site: `B` (top arc at the neighbour) or `D` (right arc at the neighbour). -/
theorem up_odd (n d : ℤ) (hn : 3 ≤ n) (hnd : n + 2 ≤ d) (hno : n % 2 = 1) (hdo : d % 2 = 1)
    (z : Site) (hod : ¬ EvenSite z) (hs : StrictInterior n d z)
    (hw : ¬ StrictInterior n d (z.1 + 0, z.2 + 1)) : Collar n d z := by
  have hspar := s_even n d hno hdo z
  have hTe := T_even n d hno hdo
  have hpar := t_odd_of n d hno hdo z hod
  rw [strict_odd n d z hod] at hs
  obtain ⟨h1, h2, h3, h4⟩ := hs
  rw [strict_grades, tv n d z 0 1, sv n d z 0 1] at hw
  have hzp : ¬ (z.1 + z.2) % 2 = 0 := hod
  by_cases hB : w1t n d z - d ≤ d + n - 2 - w1T n d
  · refine ⟨(z.1 + 0, z.2 + 1), ?_, ?_, Or.inr (Or.inr (Or.inl ((freeHn_top n d (z.1 + 0, z.2 + 1)).2 ?_)))⟩
    · simp
    · simp
    · rw [tv n d z 0 1, sv n d z 0 1]
      unfold CH closedTS hSp
      simp only [EvenSite] at hw ⊢
      omega
  · refine ⟨(z.1 + 0, z.2 + 1), ?_, ?_, Or.inr (Or.inr (Or.inr ((freeVn_right n d hno hdo (z.1 + 0, z.2 + 1)).2 ?_)))⟩
    · simp
    · simp
    · rw [tv n d z 0 1, sv n d z 0 1]
      unfold CV closedTS vSp
      simp only [EvenSite] at hw ⊢
      omega

/-- `δ = (1, 0)` on an odd strict site: `A` (bottom arc at the neighbour) or `D` (right arc at the neighbour). -/
theorem right_odd (n d : ℤ) (hn : 3 ≤ n) (hnd : n + 2 ≤ d) (hno : n % 2 = 1) (hdo : d % 2 = 1)
    (z : Site) (hod : ¬ EvenSite z) (hs : StrictInterior n d z)
    (hw : ¬ StrictInterior n d (z.1 + 1, z.2 + 0)) : Collar n d z := by
  have hspar := s_even n d hno hdo z
  have hTe := T_even n d hno hdo
  have hpar := t_odd_of n d hno hdo z hod
  rw [strict_odd n d z hod] at hs
  obtain ⟨h1, h2, h3, h4⟩ := hs
  rw [strict_grades, tv n d z 1 0, sv n d z 1 0] at hw
  have hzp : ¬ (z.1 + z.2) % 2 = 0 := hod
  by_cases hA : 2 ≤ w1t n d z + n
  · refine ⟨(z.1 + 1, z.2 + 0), ?_, ?_, Or.inl ((freeHn_CH n d (z.1 + 1, z.2 + 0)).2 ?_)⟩
    · simp
    · simp
    · rw [tv n d z 1 0, sv n d z 1 0]
      unfold CH closedTS hSp
      simp only [EvenSite] at hw ⊢
      omega
  · refine ⟨(z.1 + 1, z.2 + 0), ?_, ?_, Or.inr (Or.inr (Or.inr ((freeVn_right n d hno hdo (z.1 + 1, z.2 + 0)).2 ?_)))⟩
    · simp
    · simp
    · rw [tv n d z 1 0, sv n d z 1 0]
      unfold CV closedTS vSp
      simp only [EvenSite] at hw ⊢
      omega

/-- `δ = (−1, 0)` on an odd strict site: `B` (top arc at the neighbour) or `C` (left arc at the neighbour). -/
theorem left_odd (n d : ℤ) (hn : 3 ≤ n) (hnd : n + 2 ≤ d) (hno : n % 2 = 1) (hdo : d % 2 = 1)
    (z : Site) (hod : ¬ EvenSite z) (hs : StrictInterior n d z)
    (hw : ¬ StrictInterior n d (z.1 + -1, z.2 + 0)) : Collar n d z := by
  have hspar := s_even n d hno hdo z
  have hTe := T_even n d hno hdo
  have hpar := t_odd_of n d hno hdo z hod
  rw [strict_odd n d z hod] at hs
  obtain ⟨h1, h2, h3, h4⟩ := hs
  rw [strict_grades, tv n d z (-1) 0, sv n d z (-1) 0] at hw
  have hzp : ¬ (z.1 + z.2) % 2 = 0 := hod
  by_cases hB : w1t n d z - n ≤ d + n - 2 - w1T n d
  · refine ⟨(z.1 + -1, z.2 + 0), ?_, ?_, Or.inr (Or.inr (Or.inl ((freeHn_top n d (z.1 + -1, z.2 + 0)).2 ?_)))⟩
    · simp
    · simp
    · rw [tv n d z (-1) 0, sv n d z (-1) 0]
      unfold CH closedTS hSp
      simp only [EvenSite] at hw ⊢
      omega
  · refine ⟨(z.1 + -1, z.2 + 0), ?_, ?_, Or.inr (Or.inl ((freeVn_CV n d (z.1 + -1, z.2 + 0)).2 ?_))⟩
    · simp
    · simp
    · rw [tv n d z (-1) 0, sv n d z (-1) 0]
      unfold CV closedTS vSp
      simp only [EvenSite] at hw ⊢
      omega

/-- The `B`-odd exclusion `t = 2d + n − T` (mirror of `t = −d`). -/
theorem excl_B_odd (n d : ℤ) (hn : 1 ≤ n) (hnd : n + 2 ≤ d) (hcop : IsCoprime n d) (hno : n % 2 = 1)
    (hdo : d % 2 = 1) (z : Site) (hod : ¬ EvenSite z) (hz : StrictInterior n d z)
    (ht : w1t n d z = 2 * d + n - w1T n d) : False :=
  no_strict_odd_tnegd n d hn hnd (T_pos' n d hn hnd) hcop (mirror n d z)
    (fun h => hod ((mirror_even n d hno hdo z).1 h)) (mirror_strict n d hno hdo z hz)
    (by rw [mirror_t, ht]; ring)

/-- The `D`-even exclusion `s = T − 2d` (mirror of `s = 2L`). -/
theorem excl_D_even (n d : ℤ) (hn : 3 ≤ n) (hnd : n + 2 ≤ d) (hcop : IsCoprime n d) (hno : n % 2 = 1)
    (hdo : d % 2 = 1) (z : Site) (hev : EvenSite z) (hz : StrictInterior n d z)
    (hs : w1s n d z = w1T n d - 2 * d) : False :=
  no_strict_even_s2L n d hn hnd hcop hno hdo (mirror n d z) ((mirror_even n d hno hdo z).2 hev)
    (mirror_strict n d hno hdo z hz) (by rw [mirror_s, hs]; ring)

/-- The `D`-odd exclusion `s = T + n − d` (mirror of `s = L`). -/
theorem excl_D_odd (n d : ℤ) (hn : 3 ≤ n) (hnd : n + 2 ≤ d) (hcop : IsCoprime n d) (hno : n % 2 = 1)
    (hdo : d % 2 = 1) (z : Site) (hod : ¬ EvenSite z) (hz : StrictInterior n d z)
    (hs : w1s n d z = w1T n d + n - d) : False :=
  no_strict_odd_sL n d hn hnd hcop hno hdo (mirror n d z) (fun h => hod ((mirror_even n d hno hdo z).1 h))
    (mirror_strict n d hno hdo z hz) (by rw [mirror_s, hs]; ring)

/-- The `B`-even exclusion `t = L − T`: the translated point has `t = 0`, `s ∈ (0, T)`. -/
theorem excl_B_even (n d : ℤ) (hn : 3 ≤ n) (hnd : n + 2 ≤ d) (hcop : IsCoprime n d) (hno : n % 2 = 1)
    (hdo : d % 2 = 1) (z : Site) (hev : EvenSite z) (hz : StrictInterior n d z)
    (ht : w1t n d z = d + n - w1T n d) : False := by
  rw [strict_even n d z hev] at hz
  obtain ⟨h1, h2, h3, h4⟩ := hz
  have hT := T_pos n d hn hnd
  have hv := w1t_top n d (z.1 + -1, z.2 + 1)
  have hvs := w1s_top n d (z.1 + -1, z.2 + 1)
  simp only at hv hvs
  rw [tv n d z (-1) 1] at hv
  rw [sv n d z (-1) 1] at hvs
  refine no_t0_s_range n d hcop (by intro h; linarith [hn, hnd]) (z.1 + -1 - (n - d), z.2 + 1 - (d + n)) ?_ ?_ ?_ hT
  · rw [hv]
    omega
  · rw [hvs]
    omega
  · rw [hvs]
    omega


/-- `δ = (−1, −1)` on an even strict site: `A` (witness `z + (0, −1)`) or `C` (witness `z + (−1, 0)`, with `s ≠ 2L`). -/
theorem diag_mm_even (n d : ℤ) (hn : 3 ≤ n) (hnd : n + 2 ≤ d) (hcop : IsCoprime n d) (hno : n % 2 = 1)
    (hdo : d % 2 = 1) (z : Site) (hev : EvenSite z) (hs : StrictInterior n d z)
    (hw : ¬ StrictInterior n d (z.1 + -1, z.2 + -1)) : Collar n d z := by
  have hs0 := hs
  have hspar := s_even n d hno hdo z
  have hTe := T_even n d hno hdo
  have hpar := t_even_of n d hno hdo z hev
  have hzp : (z.1 + z.2) % 2 = 0 := hev
  rw [strict_even n d z hev] at hs
  obtain ⟨h1, h2, h3, h4⟩ := hs
  rw [strict_grades, tv n d z (-1) (-1), sv n d z (-1) (-1)] at hw
  simp only [EvenSite] at hw
  by_cases hA : 2 ≤ w1t n d z + d - n
  · refine ⟨(z.1 + 0, z.2 + -1), ?_, ?_, Or.inl ((freeHn_CH n d (z.1 + 0, z.2 + -1)).2 ?_)⟩
    · simp
    · simp
    · rw [tv n d z 0 (-1), sv n d z 0 (-1)]
      unfold CH closedTS hSp
      simp only [EvenSite]
      omega
  · have hne : w1s n d z ≠ 2 * (d + n) := fun h => no_strict_even_s2L n d hn hnd hcop hno hdo z hev hs0 h
    refine ⟨(z.1 + -1, z.2 + 0), ?_, ?_, Or.inr (Or.inl ((freeVn_CV n d (z.1 + -1, z.2 + 0)).2 ?_))⟩
    · simp
    · simp
    · rw [tv n d z (-1) 0, sv n d z (-1) 0]
      unfold CV closedTS vSp
      simp only [EvenSite]
      omega

/-- `δ = (−1, −1)` on an odd strict site: `A` (witness `z + (0, −1)`) or `C` (witness `z + (−1, −1)`, with `s ≠ L`). -/
theorem diag_mm_odd (n d : ℤ) (hn : 3 ≤ n) (hnd : n + 2 ≤ d) (hcop : IsCoprime n d) (hno : n % 2 = 1)
    (hdo : d % 2 = 1) (z : Site) (hod : ¬ EvenSite z) (hs : StrictInterior n d z)
    (hw : ¬ StrictInterior n d (z.1 + -1, z.2 + -1)) : Collar n d z := by
  have hs0 := hs
  have hspar := s_even n d hno hdo z
  have hTe := T_even n d hno hdo
  have hpar := t_odd_of n d hno hdo z hod
  have hzp : ¬ (z.1 + z.2) % 2 = 0 := hod
  rw [strict_odd n d z hod] at hs
  obtain ⟨h1, h2, h3, h4⟩ := hs
  rw [strict_grades, tv n d z (-1) (-1), sv n d z (-1) (-1)] at hw
  simp only [EvenSite] at hw
  by_cases hA : n ≤ w1t n d z + d - n
  · refine ⟨(z.1 + 0, z.2 + -1), ?_, ?_, Or.inl ((freeHn_CH n d (z.1 + 0, z.2 + -1)).2 ?_)⟩
    · simp
    · simp
    · rw [tv n d z 0 (-1), sv n d z 0 (-1)]
      unfold CH closedTS hSp
      simp only [EvenSite]
      omega
  · have hne : w1s n d z ≠ d + n := fun h => no_strict_odd_sL n d hn hnd hcop hno hdo z hod hs0 h
    refine ⟨(z.1 + -1, z.2 + -1), ?_, ?_, Or.inr (Or.inl ((freeVn_CV n d (z.1 + -1, z.2 + -1)).2 ?_))⟩
    · simp
    · simp
    · rw [tv n d z (-1) (-1), sv n d z (-1) (-1)]
      unfold CV closedTS vSp
      simp only [EvenSite]
      omega

/-- `δ = (1, 1)` on an even strict site: `B` (witness `z + (0, 1)`, top arc) or `D` (witness `z + (1, 0)`, right arc, with `s ≠ T − 2d`). -/
theorem diag_pp_even (n d : ℤ) (hn : 3 ≤ n) (hnd : n + 2 ≤ d) (hcop : IsCoprime n d) (hno : n % 2 = 1)
    (hdo : d % 2 = 1) (z : Site) (hev : EvenSite z) (hs : StrictInterior n d z)
    (hw : ¬ StrictInterior n d (z.1 + 1, z.2 + 1)) : Collar n d z := by
  have hs0 := hs
  have hspar := s_even n d hno hdo z
  have hTe := T_even n d hno hdo
  have hpar := t_even_of n d hno hdo z hev
  have hzp : (z.1 + z.2) % 2 = 0 := hev
  rw [strict_even n d z hev] at hs
  obtain ⟨h1, h2, h3, h4⟩ := hs
  rw [strict_grades, tv n d z 1 1, sv n d z 1 1] at hw
  simp only [EvenSite] at hw
  by_cases hB : w1t n d z + n - d ≤ d + n - 2 - w1T n d
  · refine ⟨(z.1 + 0, z.2 + 1), ?_, ?_, Or.inr (Or.inr (Or.inl ((freeHn_top n d (z.1 + 0, z.2 + 1)).2 ?_)))⟩
    · simp
    · simp
    · rw [tv n d z 0 1, sv n d z 0 1]
      unfold CH closedTS hSp
      simp only [EvenSite]
      omega
  · have hne : w1s n d z ≠ w1T n d - 2 * d := fun h => excl_D_even n d hn hnd hcop hno hdo z hev hs0 h
    refine ⟨(z.1 + 1, z.2 + 0), ?_, ?_, Or.inr (Or.inr (Or.inr ((freeVn_right n d hno hdo (z.1 + 1, z.2 + 0)).2 ?_)))⟩
    · simp
    · simp
    · rw [tv n d z 1 0, sv n d z 1 0]
      unfold CV closedTS vSp
      simp only [EvenSite]
      omega

/-- `δ = (1, 1)` on an odd strict site: `B` (witness `z + (0, 1)`, top arc) or `D` (witness `z + (1, 1)`, right arc, with `s ≠ T + n − d`). -/
theorem diag_pp_odd (n d : ℤ) (hn : 3 ≤ n) (hnd : n + 2 ≤ d) (hcop : IsCoprime n d) (hno : n % 2 = 1)
    (hdo : d % 2 = 1) (z : Site) (hod : ¬ EvenSite z) (hs : StrictInterior n d z)
    (hw : ¬ StrictInterior n d (z.1 + 1, z.2 + 1)) : Collar n d z := by
  have hs0 := hs
  have hspar := s_even n d hno hdo z
  have hTe := T_even n d hno hdo
  have hpar := t_odd_of n d hno hdo z hod
  have hzp : ¬ (z.1 + z.2) % 2 = 0 := hod
  rw [strict_odd n d z hod] at hs
  obtain ⟨h1, h2, h3, h4⟩ := hs
  rw [strict_grades, tv n d z 1 1, sv n d z 1 1] at hw
  simp only [EvenSite] at hw
  by_cases hB : w1t n d z + n - d ≤ d - w1T n d
  · refine ⟨(z.1 + 0, z.2 + 1), ?_, ?_, Or.inr (Or.inr (Or.inl ((freeHn_top n d (z.1 + 0, z.2 + 1)).2 ?_)))⟩
    · simp
    · simp
    · rw [tv n d z 0 1, sv n d z 0 1]
      unfold CH closedTS hSp
      simp only [EvenSite]
      omega
  · have hne : w1s n d z ≠ w1T n d + n - d := fun h => excl_D_odd n d hn hnd hcop hno hdo z hod hs0 h
    refine ⟨(z.1 + 1, z.2 + 1), ?_, ?_, Or.inr (Or.inr (Or.inr ((freeVn_right n d hno hdo (z.1 + 1, z.2 + 1)).2 ?_)))⟩
    · simp
    · simp
    · rw [tv n d z 1 1, sv n d z 1 1]
      unfold CV closedTS vSp
      simp only [EvenSite]
      omega

/-- `δ = (−1, 1)` on an even strict site: `C` (witness `z + (−1, 0)`, left arc) or `B` (witness `z + (−1, 1)`, top arc, with `t ≠ L − T`). -/
theorem diag_mp_even (n d : ℤ) (hn : 3 ≤ n) (hnd : n + 2 ≤ d) (hcop : IsCoprime n d) (hno : n % 2 = 1)
    (hdo : d % 2 = 1) (z : Site) (hev : EvenSite z) (hs : StrictInterior n d z)
    (hw : ¬ StrictInterior n d (z.1 + -1, z.2 + 1)) : Collar n d z := by
  have hs0 := hs
  have hspar := s_even n d hno hdo z
  have hTe := T_even n d hno hdo
  have hpar := t_even_of n d hno hdo z hev
  have hzp : (z.1 + z.2) % 2 = 0 := hev
  rw [strict_even n d z hev] at hs
  obtain ⟨h1, h2, h3, h4⟩ := hs
  rw [strict_grades, tv n d z (-1) 1, sv n d z (-1) 1] at hw
  simp only [EvenSite] at hw
  by_cases hC : w1s n d z - 2 * n ≤ 2 * n
  · refine ⟨(z.1 + -1, z.2 + 0), ?_, ?_, Or.inr (Or.inl ((freeVn_CV n d (z.1 + -1, z.2 + 0)).2 ?_))⟩
    · simp
    · simp
    · rw [tv n d z (-1) 0, sv n d z (-1) 0]
      unfold CV closedTS vSp
      simp only [EvenSite]
      omega
  · have hne : w1t n d z ≠ d + n - w1T n d := fun h => excl_B_even n d hn hnd hcop hno hdo z hev hs0 h
    refine ⟨(z.1 + -1, z.2 + 1), ?_, ?_, Or.inr (Or.inr (Or.inl ((freeHn_top n d (z.1 + -1, z.2 + 1)).2 ?_)))⟩
    · simp
    · simp
    · rw [tv n d z (-1) 1, sv n d z (-1) 1]
      unfold CH closedTS hSp
      simp only [EvenSite]
      omega

/-- `δ = (−1, 1)` on an odd strict site: `C` (witness `z + (−1, 0)`, left arc) or `B` (witness `z + (0, 1)`, top arc, with `t ≠ 2d + n − T`). -/
theorem diag_mp_odd (n d : ℤ) (hn : 3 ≤ n) (hnd : n + 2 ≤ d) (hcop : IsCoprime n d) (hno : n % 2 = 1)
    (hdo : d % 2 = 1) (z : Site) (hod : ¬ EvenSite z) (hs : StrictInterior n d z)
    (hw : ¬ StrictInterior n d (z.1 + -1, z.2 + 1)) : Collar n d z := by
  have hs0 := hs
  have hspar := s_even n d hno hdo z
  have hTe := T_even n d hno hdo
  have hpar := t_odd_of n d hno hdo z hod
  have hzp : ¬ (z.1 + z.2) % 2 = 0 := hod
  rw [strict_odd n d z hod] at hs
  obtain ⟨h1, h2, h3, h4⟩ := hs
  rw [strict_grades, tv n d z (-1) 1, sv n d z (-1) 1] at hw
  simp only [EvenSite] at hw
  by_cases hC : w1s n d z - 2 * n ≤ d + n - 2
  · refine ⟨(z.1 + -1, z.2 + 0), ?_, ?_, Or.inr (Or.inl ((freeVn_CV n d (z.1 + -1, z.2 + 0)).2 ?_))⟩
    · simp
    · simp
    · rw [tv n d z (-1) 0, sv n d z (-1) 0]
      unfold CV closedTS vSp
      simp only [EvenSite]
      omega
  · have hne : w1t n d z ≠ 2 * d + n - w1T n d := fun h => excl_B_odd n d (by omega) hnd hcop hno hdo z hod hs0 h
    refine ⟨(z.1 + 0, z.2 + 1), ?_, ?_, Or.inr (Or.inr (Or.inl ((freeHn_top n d (z.1 + 0, z.2 + 1)).2 ?_)))⟩
    · simp
    · simp
    · rw [tv n d z 0 1, sv n d z 0 1]
      unfold CH closedTS hSp
      simp only [EvenSite]
      omega

/-- `δ = (1, −1)` on an even strict site: `D` (witness `z + (1, 0)`, right arc) or `A` (witness `z + (1, −1)`, bottom arc). -/
theorem diag_pm_even (n d : ℤ) (hn : 3 ≤ n) (hnd : n + 2 ≤ d) (hcop : IsCoprime n d) (hno : n % 2 = 1)
    (hdo : d % 2 = 1) (z : Site) (hev : EvenSite z) (hs : StrictInterior n d z)
    (hw : ¬ StrictInterior n d (z.1 + 1, z.2 + -1)) : Collar n d z := by
  have hs0 := hs
  have hspar := s_even n d hno hdo z
  have hTe := T_even n d hno hdo
  have hpar := t_even_of n d hno hdo z hev
  have hzp : (z.1 + z.2) % 2 = 0 := hev
  rw [strict_even n d z hev] at hs
  obtain ⟨h1, h2, h3, h4⟩ := hs
  rw [strict_grades, tv n d z 1 (-1), sv n d z 1 (-1)] at hw
  simp only [EvenSite] at hw
  by_cases hD : w1T n d ≤ w1s n d z + 2 * n
  · refine ⟨(z.1 + 1, z.2 + 0), ?_, ?_, Or.inr (Or.inr (Or.inr ((freeVn_right n d hno hdo (z.1 + 1, z.2 + 0)).2 ?_)))⟩
    · simp
    · simp
    · rw [tv n d z 1 0, sv n d z 1 0]
      unfold CV closedTS vSp
      simp only [EvenSite]
      omega
  · have hlow : 2 - (n + d) ≤ w1t n d z := by omega
    exact ⟨(z.1 + 1, z.2 - 1), by simp, by simp, Or.inl (witA_even n d hn hnd hcop hno hdo z hev hs0 hlow)⟩

/-- `δ = (1, −1)` on an odd strict site: `D` (witness `z + (1, 0)`, right arc) or `A` (witness `z + (0, −1)`, bottom arc, with `t ≠ −d`). -/
theorem diag_pm_odd (n d : ℤ) (hn : 3 ≤ n) (hnd : n + 2 ≤ d) (hcop : IsCoprime n d) (hno : n % 2 = 1)
    (hdo : d % 2 = 1) (z : Site) (hod : ¬ EvenSite z) (hs : StrictInterior n d z)
    (hw : ¬ StrictInterior n d (z.1 + 1, z.2 + -1)) : Collar n d z := by
  have hs0 := hs
  have hspar := s_even n d hno hdo z
  have hTe := T_even n d hno hdo
  have hpar := t_odd_of n d hno hdo z hod
  have hzp : ¬ (z.1 + z.2) % 2 = 0 := hod
  rw [strict_odd n d z hod] at hs
  obtain ⟨h1, h2, h3, h4⟩ := hs
  rw [strict_grades, tv n d z 1 (-1), sv n d z 1 (-1)] at hw
  simp only [EvenSite] at hw
  by_cases hD : w1T n d + 2 - d + n ≤ w1s n d z + 2 * n
  · refine ⟨(z.1 + 1, z.2 + 0), ?_, ?_, Or.inr (Or.inr (Or.inr ((freeVn_right n d hno hdo (z.1 + 1, z.2 + 0)).2 ?_)))⟩
    · simp
    · simp
    · rw [tv n d z 1 0, sv n d z 1 0]
      unfold CV closedTS vSp
      simp only [EvenSite]
      omega
  · have hne : w1t n d z ≠ -d := fun h => no_strict_odd_tnegd n d (by omega) hnd (T_pos' n d (by omega) hnd) hcop z hod hs0 h
    refine ⟨(z.1 + 0, z.2 + -1), ?_, ?_, Or.inl ((freeHn_CH n d (z.1 + 0, z.2 + -1)).2 ?_)⟩
    · simp
    · simp
    · rw [tv n d z 0 (-1), sv n d z 0 (-1)]
      unfold CH closedTS hSp
      simp only [EvenSite]
      omega

/-- **The off-collar lemma** (task 90, hsq): a strict site outside all collars has every corner of every unit square through it strict. -/
theorem strict_of_not_collar (n d : ℤ) (hn : 3 ≤ n) (hnd : n + 2 ≤ d) (hcop : IsCoprime n d)
    (hno : n % 2 = 1) (hdo : d % 2 = 1) (z : Site) (hs : StrictInterior n d z) (hc : ¬ Collar n d z)
    (w : Site) (hw1 : |w.1 - z.1| ≤ 1) (hw2 : |w.2 - z.2| ≤ 1) : StrictInterior n d w := by
  by_contra hw
  obtain ⟨w1, w2⟩ := w
  obtain ⟨a, rfl⟩ : ∃ a : ℤ, w1 = z.1 + a := ⟨w1 - z.1, by ring⟩
  obtain ⟨b, rfl⟩ : ∃ b : ℤ, w2 = z.2 + b := ⟨w2 - z.2, by ring⟩
  have ha : -1 ≤ a ∧ a ≤ 1 := by
    have := abs_le.mp (by simpa using hw1 : |a| ≤ 1)
    exact this
  have hb : -1 ≤ b ∧ b ≤ 1 := by
    have := abs_le.mp (by simpa using hw2 : |b| ≤ 1)
    exact this
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  by_cases hev : EvenSite z
  · interval_cases a <;> interval_cases b
    · exact absurd (diag_mm_even n d hn hnd hcop hno hdo z hev hs hw) hc
    · exact absurd (left_even n d hn hnd hno hdo z hev hs hw) hc
    · exact absurd (diag_mp_even n d hn hnd hcop hno hdo z hev hs hw) hc
    · exact absurd (down_even n d hn hnd hno hdo z hev hs hw) hc
    · exact (hw (by simpa using hs)).elim
    · exact absurd (up_even n d hn hnd hno hdo z hev hs hw) hc
    · exact absurd (diag_pm_even n d hn hnd hcop hno hdo z hev hs hw) hc
    · exact absurd (right_even n d hn hnd hno hdo z hev hs hw) hc
    · exact absurd (diag_pp_even n d hn hnd hcop hno hdo z hev hs hw) hc
  · interval_cases a <;> interval_cases b
    · exact absurd (diag_mm_odd n d hn hnd hcop hno hdo z hev hs hw) hc
    · exact absurd (left_odd n d hn hnd hno hdo z hev hs hw) hc
    · exact absurd (diag_mp_odd n d hn hnd hcop hno hdo z hev hs hw) hc
    · exact absurd (down_odd n d hn hnd hno hdo z hev hs hw) hc
    · exact (hw (by simpa using hs)).elim
    · exact absurd (up_odd n d hn hnd hno hdo z hev hs hw) hc
    · exact absurd (diag_pm_odd n d hn hnd hcop hno hdo z hev hs hw) hc
    · exact absurd (right_odd n d hn hnd hno hdo z hev hs hw) hc
    · exact absurd (diag_pp_odd n d hn hnd hcop hno hdo z hev hs hw) hc

end FLatticePaper.W1OffCollarCases
