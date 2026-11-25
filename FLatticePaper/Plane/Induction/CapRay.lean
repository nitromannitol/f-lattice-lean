import FLatticePaper.Plane.Induction.CapRecursion
import FLatticePaper.Plane.Induction.CapAnchors
import FLatticePaper.Plane.Induction.PriceDeck
import FLatticePaper.Plane.Induction.Packet
import FLatticePaper.Plane.Induction.SheetMonoChild

/-! The diagonal ray of the all-slope cap on a frame's packet (ALL_SLOPE_STEP, "The uniform quadratic cap", the high-slope case `d > 3n`
with `(N, D, a) = (n, d, 2)`).

Start: integers `p, q` with `N p − D q = 2 − N` (possible since `N, D` are coprime). The ray sites `(p+k, q+k)` are odd, with t-grade
`2 − N − kC`, `C = D − N`; the even sites `(p+j+1, q+j)` have t-grade `2 − jC`. The strips and anchors come from the packet
(`zero_value`, `anchor_value`, `anchor_value_odd`); the sheet monotonicities are derived from the signed comparison `hsig` (Q26). -/

namespace FLatticePaper.CapRay

open FLatticePaper FLatticePaper.Induction FLatticePaper.CapAnchors FLatticePaper.CapRecursion
open FLatticePaper.SheetMonoChild

/-- The numerator and denominator of a proper child are odd (the child is even: `n + d` even, and coprime). -/
theorem child_num_den_odd (frame : ChildFrame) :
    ∃ α β : ℤ, frame.child.num = 2 * α + 1 ∧ frame.child.den = 2 * β + 1 :=
  FLatticePaper.PriceDeck.child_odd_witness frame

/-- **The start of the ray.** Integers `p, q` with `N p − D q = 2 − N`, from the coprimality of the child. -/
theorem ray_start (frame : ChildFrame) : ∃ p q : ℤ,
    frame.child.num * p - frame.child.den * q = 2 - frame.child.num := by
  obtain ⟨u, v, h⟩ := frame.child_reduced
  refine ⟨(2 - frame.child.num) * u, -((2 - frame.child.num) * v), ?_⟩
  linear_combination (2 - frame.child.num) * h

/-- The parity of the start: `p + q` is odd when `N p − D q = 2 − N` with `N, D` odd. -/
theorem start_parity (frame : ChildFrame) {p q : ℤ} (hs : frame.child.num * p - frame.child.den * q = 2 - frame.child.num) :
    (p + q) % 2 = 1 := by
  obtain ⟨α, β, hα, hβ⟩ := child_num_den_odd frame
  rw [hα, hβ] at hs
  have h : p + q = 2 * (-α - α * p + β * q + q) + 1 := by linear_combination hs
  omega

/-- **The diagonal cap of the high-slope ray.** With `p, q` the start (`ray_start`), the even ray sites, the odd ray sites and their anchors
satisfy `m(k) ≤ F(p+k, q+k)` for all `k ≤ K`. The zero strip and the harmonic anchors come from `frame.Packet` (`hP`); the sheet
monotonicities come from `hsig` (Q26). The bounds `J, K` are the integer ranges of the anchors:
`2N J ≤ N + D − 2 < 2N (J+1)` and `2N K ≤ 3D + 3N − 1`. Hypotheses `3 ≤ N`, `4 ≤ D − N` are the proper nonbase conditions. -/
theorem ray_cap (frame : ChildFrame) {F : Field} (hP : frame.Packet F)
    (hsig : ∀ w ∈ frame.closedPolygon, F w - F (w - frame.shortShift) ≤ 0)
    (hN3 : 3 ≤ frame.child.num) (hND : 4 ≤ frame.child.den - frame.child.num)
    {p q : ℤ} (hs : frame.child.num * p - frame.child.den * q = 2 - frame.child.num)
    (J K : ℕ)
    (hJ1 : 2 * frame.child.num * (J : ℤ) ≤ frame.child.num + frame.child.den - 2)
    (hJ2 : frame.child.num + frame.child.den - 2 < 2 * frame.child.num * ((J : ℤ) + 1))
    (hK : 2 * frame.child.num * (K : ℤ) ≤ 3 * frame.child.den + 3 * frame.child.num - 1) :
    ∀ k : ℕ, k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ F (p + (k : ℤ), q + (k : ℤ)) := by
  have hodd := sheetMono_odd_of_signed frame hP hsig
  have heven := sheetMono_even_of_signed frame hP hsig
  obtain ⟨N, hN⟩ : ∃ N, frame.child.num = N := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, frame.child.den = D := ⟨_, rfl⟩
  have tg : ∀ x y : ℤ, frame.tGrade (x, y) = N * x - D * y := fun x y => by
    simp only [ChildFrame.tGrade, hN, hD]
  simp only [hN, hD] at hs hJ1 hJ2 hK hN3 hND
  have hpq := start_parity frame (p := p) (q := q) (by rw [hN, hD]; exact hs)
  have hbin := hP.binary
  have hN0 : 0 < N := by omega
  have hND' : N < D := by omega
  -- the diagonal monotonicity of the odd sheet on the ray (from `hsig`)
  have hmono : ∀ n : ℕ, n ≤ J → F (p + (n : ℤ), q + ((n : ℤ) + 2)) ≤ F (p + ((n : ℤ) + 2), q + ((n : ℤ) + 2)) := by
    intro n hn
    have hn0 : (0 : ℤ) ≤ (n : ℤ) := by positivity
    apply hodd
    · unfold EvenSite; simp only; omega
    · unfold EvenSite; simp only; omega
    · rw [tg, tg]; nlinarith
    · rw [tg]; nlinarith
  -- the zero strip values
  have hA0 : 0 ≤ F (p, q) := by
    have h := zero_value hP.strips (z := (p, q)) (by rw [tg, hD]; nlinarith) (by rw [tg, hN, hD]; nlinarith)
    rw [h]
  have hA1 : 0 ≤ F (p + 1, q + 1) := by
    have h := zero_value hP.strips (z := (p + 1, q + 1)) (by rw [tg, hD]; nlinarith) (by rw [tg, hN, hD]; nlinarith)
    rw [h]
  -- the even anchors: B_0, B_1 by the zero strip, B_j for j ≥ 2 by the even monotonicity and the harmonic anchor
  have hB : ∀ j : ℕ, j ≤ J → F (p + (j : ℤ) + 1, q + (j : ℤ)) ≤ FLatticePaper.QuadraticCap.capMin j := by
    intro j hj
    rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · interval_cases j
      · have h := zero_value hP.strips (z := (p + 0 + 1, q + 0)) (by simp only [tg]; nlinarith) (by simp only [tg]; nlinarith)
        simp only [Nat.cast_zero, add_zero] at h ⊢
        rw [h, FLatticePaper.QuadraticCap.capMin_zero]
      · have h := zero_value hP.strips (z := (p + ((1 : ℕ) : ℤ) + 1, q + ((1 : ℕ) : ℤ))) (by simp only [tg, Nat.cast_one]; nlinarith) (by simp only [tg, Nat.cast_one]; nlinarith)
        simp only [Nat.cast_one] at h ⊢
        rw [h, FLatticePaper.QuadraticCap.capMin_one]
    · have hjz : (2 : ℤ) ≤ (j : ℤ) := by exact_mod_cast hj2
      have hjJ : (j : ℤ) ≤ J := by exact_mod_cast hj
      have hj1 : (1 : ℤ) ≤ (j : ℤ) := by omega
      have hu : EvenSite (p + (j : ℤ) + 1, q + (j : ℤ)) := by unfold EvenSite; simp only; omega
      have hv : EvenSite (1 - (j : ℤ), (j : ℤ) - 1) := by unfold EvenSite; simp only; omega
      have hle := heven (p + (j : ℤ) + 1, q + (j : ℤ)) (1 - (j : ℤ), (j : ℤ) - 1) hu hv
        (by rw [tg, tg]; nlinarith) (by rw [tg]; nlinarith)
      have hlo : 1 - 2 * frame.child.den ≤ 2 * frame.child.num * (1 - (j : ℤ)) := by
        rw [hN, hD]; nlinarith
      have hhi : 2 * frame.child.num * (1 - (j : ℤ)) ≤ 2 * (frame.child.den + frame.child.num) - 1 := by
        rw [hN, hD]; nlinarith
      have hanc := anchor_value hP.strips (j : ℤ) hlo hhi
      rw [hanc] at hle
      exact hle
  -- the odd anchors: m(k) ≤ F(p+k, q+k) for J+2 < k ≤ K
  have hanchor : ∀ k : ℕ, J + 2 < k → k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ F (p + (k : ℤ), q + (k : ℤ)) := by
    intro k hk1 hk2
    have hkJ : (J : ℤ) + 3 ≤ (k : ℤ) := by exact_mod_cast hk1
    have hkK : (k : ℤ) ≤ (K : ℤ) := by exact_mod_cast hk2
    have hk0 : (0 : ℤ) ≤ (k : ℤ) := by positivity
    have hlo : 1 - 2 * frame.child.den ≤ frame.child.den + 3 * frame.child.num - 2 * frame.child.num * (k : ℤ) := by
      rw [hN, hD]; nlinarith
    have hhi : frame.child.den + 3 * frame.child.num - 2 * frame.child.num * (k : ℤ) ≤ 2 * (frame.child.den + frame.child.num) - 1 := by
      rw [hN, hD]; nlinarith
    have hanc := anchor_value_odd hP.strips (k : ℤ) hlo hhi
    have hle := hodd (2 - (k : ℤ), (k : ℤ) - 1) (p + (k : ℤ), q + (k : ℤ))
      (by unfold EvenSite; simp only; omega) (by unfold EvenSite; simp only; omega)
      (by rw [tg, tg]; nlinarith) (by rw [tg]; nlinarith)
    rw [hanc] at hle
    exact hle
  exact diag_cap F p q hpq hbin J K hmono hA0 hA1 hB hanchor

/-- **The odd halo cap** (ALL_SLOPE_STEP, "Why this scalar cap kills all long forks", the odd inputs of the fan): an odd site `z` whose
t'-grade is at least the odd threshold `2 − N − kC` (the grade of the ray point of height `k`) and at most the top of the zero strip
satisfies `m(k) ≤ F z`. Negative grades: the odd sheet monotonicity (`hsig`, Q26) against the ray point, whose cap is the
hypothesis `hcap` (`ray_cap`). Nonnegative grades: the zero strip, and `m(k) ≤ 0`. -/
theorem odd_halo (frame : ChildFrame) {F : Field} (hP : frame.Packet F)
    (hsig : ∀ w ∈ frame.closedPolygon, F w - F (w - frame.shortShift) ≤ 0)
    {p q : ℤ} (hs : frame.child.num * p - frame.child.den * q = 2 - frame.child.num) (K : ℕ)
    (hcap : ∀ k : ℕ, k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ F (p + (k : ℤ), q + (k : ℤ)))
    (k : ℕ) (hk : k ≤ K) (z : Site) (hz : ¬ EvenSite z)
    (hlo : 2 - frame.child.num - (k : ℤ) * (frame.child.den - frame.child.num) ≤ frame.tGrade z)
    (hup : frame.tGrade z ≤ frame.child.num + 2 * frame.child.den - 1) :
    FLatticePaper.QuadraticCap.capMin k ≤ F z := by
  have hodd := sheetMono_odd_of_signed frame hP hsig
  have hpq := start_parity frame hs
  have hr : ¬ EvenSite (p + (k : ℤ), q + (k : ℤ)) := by unfold EvenSite; simp only; omega
  have hrt : frame.tGrade (p + (k : ℤ), q + (k : ℤ))
      = 2 - frame.child.num - (k : ℤ) * (frame.child.den - frame.child.num) := by
    simp only [ChildFrame.tGrade]; linear_combination hs
  have hcapk := hcap k hk
  by_cases hz0 : frame.tGrade z ≤ 0
  · have hF := hodd (p + (k : ℤ), q + (k : ℤ)) z hr hz (by rw [hrt]; exact hlo) hz0
    exact hcapk.trans hF
  · have hz0' : 0 < frame.tGrade z := lt_of_not_ge hz0
    obtain ⟨hn1, hn2, -⟩ := frame.child_facts
    have hF0 : F z = 0 := zero_value hP.strips (by omega) hup
    rw [hF0]
    have hk1 : (0 : ℤ) ≤ (k : ℤ) * ((k : ℤ) - 1) := by
      rcases Nat.eq_zero_or_pos k with h | h
      · subst h; simp
      · have h1 : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast h
        nlinarith
    have h2 : 0 ≤ (k : ℤ) * ((k : ℤ) - 1) / 2 := Int.ediv_nonneg hk1 (by norm_num)
    unfold FLatticePaper.QuadraticCap.capMin
    linarith

/-- The cross term `k (D − N)` is nonnegative (`k ≥ 0`, `N < D`). -/
theorem kC_nonneg (frame : ChildFrame) (k : ℕ) : 0 ≤ (k : ℤ) * (frame.child.den - frame.child.num) := by
  obtain ⟨h1, h2, -⟩ := frame.child_facts
  exact mul_nonneg (by positivity) (by omega)

/-- **The even ray value** (ALL_SLOPE_STEP, the even centres `B_k`: "both odd inputs have heights at least `A_k`, admission gives
`B_k ≥ m(k)`"). The even ray point `(p+k+1, q+k)` has the odd west input `(p+k, q+k)` (on the ray, `ray_cap`) and the odd east input of
grade `2+N−kC`, which the odd halo (`odd_halo`) bounds below by `m(k)`. The binary laplacian gives `2 F c ≥ F(west) + F(east)`. -/
theorem even_ray_lower (frame : ChildFrame) {F : Field} (hP : frame.Packet F) (hsig : ∀ w ∈ frame.closedPolygon, F w - F (w - frame.shortShift) ≤ 0)
    {p q : ℤ} (hs : frame.child.num * p - frame.child.den * q = 2 - frame.child.num) (K : ℕ)
    (hcap : ∀ k : ℕ, k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ F (p + (k : ℤ), q + (k : ℤ)))
    (k : ℕ) (hk : k ≤ K) :
    FLatticePaper.QuadraticCap.capMin k ≤ F (p + (k : ℤ) + 1, q + (k : ℤ)) := by
  have hpq := start_parity frame hs
  obtain ⟨hn1, hn2, -⟩ := frame.child_facts
  have hkC := kC_nonneg frame k
  have hev : EvenSite (p + (k : ℤ) + 1, q + (k : ℤ)) := by unfold EvenSite; simp only; omega
  have hinN : incomingNeg (p + (k : ℤ) + 1, q + (k : ℤ)) = (p + (k : ℤ), q + (k : ℤ)) := by
    unfold incomingNeg; rw [if_pos hev]; congr 1; ring
  have hinP : incomingPos (p + (k : ℤ) + 1, q + (k : ℤ)) = (p + (k : ℤ) + 2, q + (k : ℤ)) := by
    unfold incomingPos; rw [if_pos hev]; congr 1; ring
  have hb := hP.binary (p + (k : ℤ) + 1, q + (k : ℤ))
  unfold laplacian at hb
  rw [hinN, hinP] at hb
  have hW := hcap k hk
  have hzo : ¬ EvenSite (p + (k : ℤ) + 2, q + (k : ℤ)) := by unfold EvenSite; simp only; omega
  have hrtE : frame.tGrade (p + (k : ℤ) + 2, q + (k : ℤ))
      = 2 + frame.child.num - (k : ℤ) * (frame.child.den - frame.child.num) := by
    simp only [ChildFrame.tGrade]; linear_combination hs
  have hE := odd_halo frame hP hsig hs K hcap k hk (p + (k : ℤ) + 2, q + (k : ℤ)) hzo
    (by rw [hrtE]; linarith)
    (by rw [hrtE]; nlinarith)
  rcases hb with h | h <;> linarith

/-- **The even halo cap** (ALL_SLOPE_STEP, the even inputs of the fan): an even site `z` whose t'-grade is at least `2 − kC` (the grade of
the even ray point of height `k`) and at most the top of the zero strip satisfies `m(k) ≤ F z`. Negative grades: the even sheet
monotonicity (`hsig`, Q26) against the even ray point, whose value is `even_ray_lower`. Nonnegative grades: the zero strip. -/
theorem even_halo (frame : ChildFrame) {F : Field} (hP : frame.Packet F)
    (hsig : ∀ w ∈ frame.closedPolygon, F w - F (w - frame.shortShift) ≤ 0)
    {p q : ℤ} (hs : frame.child.num * p - frame.child.den * q = 2 - frame.child.num) (K : ℕ)
    (hcap : ∀ k : ℕ, k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ F (p + (k : ℤ), q + (k : ℤ)))
    (k : ℕ) (hk : k ≤ K) (z : Site) (hz : EvenSite z)
    (hlo : 2 - (k : ℤ) * (frame.child.den - frame.child.num) ≤ frame.tGrade z)
    (hup : frame.tGrade z ≤ frame.child.num + 2 * frame.child.den - 1) :
    FLatticePaper.QuadraticCap.capMin k ≤ F z := by
  have heven := sheetMono_even_of_signed frame hP hsig
  have hpq := start_parity frame hs
  have hr : EvenSite (p + (k : ℤ) + 1, q + (k : ℤ)) := by unfold EvenSite; simp only; omega
  have hrt : frame.tGrade (p + (k : ℤ) + 1, q + (k : ℤ))
      = 2 - (k : ℤ) * (frame.child.den - frame.child.num) := by
    simp only [ChildFrame.tGrade]; linear_combination hs
  have hR := even_ray_lower frame hP hsig hs K hcap k hk
  by_cases hz0 : frame.tGrade z ≤ 0
  · have hF := heven (p + (k : ℤ) + 1, q + (k : ℤ)) z hr hz (by rw [hrt]; exact hlo) hz0
    exact hR.trans hF
  · have hz0' : 0 < frame.tGrade z := lt_of_not_ge hz0
    obtain ⟨hn1, hn2, -⟩ := frame.child_facts
    have hF0 : F z = 0 := zero_value hP.strips (by omega) hup
    rw [hF0]
    have hk1 : (0 : ℤ) ≤ (k : ℤ) * ((k : ℤ) - 1) := by
      rcases Nat.eq_zero_or_pos k with h | h
      · subst h; simp
      · have h1 : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast h
        nlinarith
    have h2 : 0 ≤ (k : ℤ) * ((k : ℤ) - 1) / 2 := Int.ediv_nonneg hk1 (by norm_num)
    unfold FLatticePaper.QuadraticCap.capMin
    linarith

end FLatticePaper.CapRay
