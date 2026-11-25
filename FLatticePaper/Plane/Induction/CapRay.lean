import FLatticePaper.Plane.Induction.CapRecursion
import FLatticePaper.Plane.Induction.CapAnchors
import FLatticePaper.Plane.Induction.PriceDeck
import FLatticePaper.Plane.Induction.Packet
import FLatticePaper.Plane.Induction.SheetMonoChild
import FLatticePaper.Plane.Induction.FanPropagation
import FLatticePaper.Plane.Induction.W1Exit
import FLatticePaper.Plane.Induction.ConeRoot

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

/-! ### The star-restricted window (ALL_SLOPE_STEP, "Propagation"; the replacement of `hwin`)

From the start `b` (odd, `t b ≥ N + 2`, the condition `t'(b) ≥ N + a` with `a = 2`), a root `x` of the cone has height `k = x_y − b_y`
in `[1, K−1]`, with `ℓ = x_x − b_x ≥ k − 1` on even roots and `ℓ ≥ k` on odd roots. Its two inputs are then in `InCone`, and the
halo bounds (`even_halo`, `odd_halo`) give `m(k) ≤ F` on each input, where `m i = capMin (i_y − b_y)`. -/

/-- The inputs of a cone root are cone inputs. -/
theorem cone_input_of_root (b : Site) (K : ℕ) (x : Site) (hR : ConeRoot b K x) (i : Site)
    (hi : i = incomingNeg x ∨ i = incomingPos x) : InCone b K i := by
  obtain ⟨h1, h2, hev, hodd⟩ := hR
  by_cases hx : EvenSite x
  · have hn : incomingNeg x = (x.1 - 1, x.2) := by unfold incomingNeg; rw [if_pos hx]
    have hp : incomingPos x = (x.1 + 1, x.2) := by unfold incomingPos; rw [if_pos hx]
    have hxu : (x.1 + x.2) % 2 = 0 := hx
    rcases hi with rfl | rfl
    · rw [hn]
      refine ⟨by dsimp only; omega, by dsimp only; omega, fun h => ?_, fun _ => ?_⟩
      · exfalso
        unfold EvenSite at h
        dsimp only at h
        omega
      · dsimp only
        have := hev hx
        omega
    · rw [hp]
      refine ⟨by dsimp only; omega, by dsimp only; omega, fun h => ?_, fun _ => ?_⟩
      · exfalso
        unfold EvenSite at h
        dsimp only at h
        omega
      · dsimp only
        have := hev hx
        omega
  · have hn : incomingNeg x = (x.1, x.2 - 1) := by unfold incomingNeg; rw [if_neg hx]
    have hp : incomingPos x = (x.1, x.2 + 1) := by unfold incomingPos; rw [if_neg hx]
    have hxo : ¬ (x.1 + x.2) % 2 = 0 := hx
    have hl := hodd hx
    rcases hi with rfl | rfl
    · rw [hn]
      refine ⟨by dsimp only; omega, by dsimp only; omega, fun _ => ?_, fun h => ?_⟩
      · dsimp only
        omega
      · exfalso
        exact h (by unfold EvenSite; dsimp only; omega)
    · rw [hp]
      refine ⟨by dsimp only; omega, by dsimp only; omega, fun _ => ?_, fun h => ?_⟩
      · dsimp only
        omega
      · exfalso
        exact h (by unfold EvenSite; dsimp only; omega)

/-- **The cone input bound.** For a cone input `i` of the start `b` (`t b ≥ N + 2`) lying in the closed polygon, `m(k) ≤ F i` with
`k = i_y − b_y`: the grade of `i` is at least the halo threshold (`even_halo`, `odd_halo`), by the cone inequalities on `ℓ`. -/
theorem cone_input {F : Field} (frame : ChildFrame) (hP : frame.Packet F)
    (hsig : ∀ w ∈ frame.closedPolygon, F w - F (w - frame.shortShift) ≤ 0)
    {p q : ℤ} (hs : frame.child.num * p - frame.child.den * q = 2 - frame.child.num) (K : ℕ)
    (hcap : ∀ k : ℕ, k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ F (p + (k : ℤ), q + (k : ℤ)))
    (b : Site) (hb : frame.child.num + 2 ≤ frame.tGrade b)
    (i : Site) (hI : InCone b K i) (hpoly : i ∈ frame.closedPolygon) :
    FLatticePaper.QuadraticCap.capMin (i.2 - b.2) ≤ F i := by
  obtain ⟨hk0, hkK, hev, hodd⟩ := hI
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = i.2 - b.2 := ⟨(i.2 - b.2).toNat, Int.toNat_of_nonneg hk0⟩
  have hkK' : k ≤ K := by omega
  rw [← hk]
  obtain ⟨hn1, -, -, hd3, -⟩ := frame.child_facts
  have htb : frame.tGrade i
      = frame.tGrade b + frame.child.num * (i.1 - b.1) - frame.child.den * (i.2 - b.2) := by
    unfold ChildFrame.tGrade
    ring
  have hup : frame.tGrade i ≤ frame.child.num + 2 * frame.child.den - 1 := by
    unfold ChildFrame.closedPolygon at hpoly
    simp only [Set.mem_setOf_eq] at hpoly
    split_ifs at hpoly with he
    · omega
    · omega
  by_cases hz : EvenSite i
  · have hl := hev hz
    have hlo : 2 - (k : ℤ) * (frame.child.den - frame.child.num) ≤ frame.tGrade i := by
      rw [htb, ← hk]
      rw [← hk] at hl
      have hm := mul_le_mul_of_nonneg_left (show (k : ℤ) - 1 ≤ i.1 - b.1 by omega)
        (show (0 : ℤ) ≤ frame.child.num by omega)
      nlinarith
    exact even_halo frame hP hsig hs K hcap k hkK' i hz hlo hup
  · have hl := hodd hz
    have hlo : 2 - frame.child.num - (k : ℤ) * (frame.child.den - frame.child.num) ≤ frame.tGrade i := by
      rw [htb, ← hk]
      rw [← hk] at hl
      have hm := mul_le_mul_of_nonneg_left (show (k : ℤ) - 2 ≤ i.1 - b.1 by omega)
        (show (0 : ℤ) ≤ frame.child.num by omega)
      nlinarith
    exact odd_halo frame hP hsig hs K hcap k hkK' i hz hlo hup

/-- **The star-restricted window** (the replacement of `hwin`): the cap `m i = capMin (i_y − b_y)` lies below `F` on the inputs of every
open-rectangle root of the cone from `b`. The inputs are in the closed polygon by `rectInputs`. -/
theorem cone_window {F : Field} (frame : ChildFrame) (hP : frame.Packet F)
    (hsig : ∀ w ∈ frame.closedPolygon, F w - F (w - frame.shortShift) ≤ 0)
    {p q : ℤ} (hs : frame.child.num * p - frame.child.den * q = 2 - frame.child.num) (K : ℕ)
    (hcap : ∀ k : ℕ, k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ F (p + (k : ℤ), q + (k : ℤ)))
    (b : Site) (hb : frame.child.num + 2 ≤ frame.tGrade b) :
    FLatticePaper.FanPropagation.WindowOn (fun x => frame.openRect x ∧ ConeRoot b K x) F
      (fun i => FLatticePaper.QuadraticCap.capMin (i.2 - b.2)) := by
  intro x hx i hi
  obtain ⟨hopen, hR⟩ := hx
  exact cone_input frame hP hsig hs K hcap b hb i (cone_input_of_root b K x hR i hi)
    (FLatticePaper.W1Exit.rectInputs frame x hopen i hi)

/-- **One fan step keeps the cone** (ALL_SLOPE_STEP, "Propagation"). An even root moves east (`fan_step`), which keeps the cone. An odd
root moves north or south: north keeps the cone when the height is at most `K−2`, south when it is at least `2`. These two boundary
facts are the hypotheses `hdown`, `hup`; they are the lower and upper arcs of the fan, not yet proved here. -/
theorem cone_next_root (b : Site) (K : ℕ) (x w : Site) (hR : ConeRoot b K x)
    (hw : w = incomingNeg x ∨ w = incomingPos x)
    (hEven : EvenSite x → w = incomingPos x)
    (hdown : ¬ EvenSite x → w = incomingNeg x → 2 ≤ x.2 - b.2)
    (hup : ¬ EvenSite x → w = incomingPos x → x.2 - b.2 ≤ (K : ℤ) - 2) :
    ConeRoot b K w := by
  obtain ⟨h1, h2, hev, hodd⟩ := hR
  by_cases hx : EvenSite x
  · have hwp := hEven hx
    subst hwp
    have hp : incomingPos x = (x.1 + 1, x.2) := by unfold incomingPos; rw [if_pos hx]
    rw [hp]
    have hxu : (x.1 + x.2) % 2 = 0 := hx
    have hl := hev hx
    refine ⟨by dsimp only; omega, by dsimp only; omega, fun h => ?_, fun _ => ?_⟩
    · exfalso
      unfold EvenSite at h
      dsimp only at h
      omega
    · dsimp only
      omega
  · have hxo : ¬ (x.1 + x.2) % 2 = 0 := hx
    have hl := hodd hx
    rcases hw with hw | hw
    · have hn : incomingNeg x = (x.1, x.2 - 1) := by unfold incomingNeg; rw [if_neg hx]
      have hd := hdown hx hw
      rw [hw, hn]
      refine ⟨by dsimp only; omega, by dsimp only; omega, fun _ => ?_, fun h => ?_⟩
      · dsimp only
        omega
      · exfalso
        exact h (by unfold EvenSite; dsimp only; omega)
    · have hp : incomingPos x = (x.1, x.2 + 1) := by unfold incomingPos; rw [if_neg hx]
      have hu := hup hx hw
      rw [hw, hp]
      refine ⟨by dsimp only; omega, by dsimp only; omega, fun _ => ?_, fun h => ?_⟩
      · dsimp only
        omega
      · exfalso
        exact h (by unfold EvenSite; dsimp only; omega)

/-! ### The strict top of the cap (ALL_SLOPE_STEP: "Strictness excludes height K*"; the upper arc of the cone)

The odd anchor `(3−k, k−2)` has harmonic value `m(k−1)` (`h0 = −y(y+1)/2` at `x + y = 1`), which is above `m(k)`. Monotonicity of the
odd sheet then makes the ray point of height `K` strictly above `m(K)`; the even ray point and every cone input at height `K` follow. A
fan contact cannot sit at height `K`, which is the upper arc. -/

/-- The harmonic value at the odd anchor `(3−k, k−2)`: `m(k−1)`. -/
theorem anchor3_value {frame : ChildFrame} {F : Field} (hS : frame.HasStrips F) (k : ℤ)
    (hlo : 1 - 2 * frame.child.den ≤ frame.child.den + 5 * frame.child.num - 2 * frame.child.num * k)
    (hhi : frame.child.den + 5 * frame.child.num - 2 * frame.child.num * k ≤ 2 * (frame.child.den + frame.child.num) - 1) :
    F (3 - k, k - 2) = FLatticePaper.QuadraticCap.capMin (k - 1) := by
  have hs : 1 - 2 * frame.child.den ≤ frame.sGrade (3 - k, k - 2) ∧
      frame.sGrade (3 - k, k - 2) ≤ 2 * (frame.child.den + frame.child.num) - 1 := by
    have e : frame.sGrade (3 - k, k - 2)
        = frame.child.den + 5 * frame.child.num - 2 * frame.child.num * k := by
      unfold ChildFrame.sGrade
      ring
    rw [e]
    exact ⟨hlo, hhi⟩
  rw [hS.2 (3 - k, k - 2) hs.1 hs.2]
  unfold FLatticePaper.Induction.harmonicGrid FLatticePaper.QuadraticCap.capMin
  have e : (3 - k) ^ 2 + 2 * (3 - k) * (k - 2) - (k - 2) ^ 2 - 2 * (k - 2) - ((3 - k) + (k - 2)) % 2
      = -2 * ((k - 1) * (k - 2)) := by
    have h1 : ((3 - k) + (k - 2)) % 2 = 1 := by omega
    rw [h1]
    ring
  rw [e, show k - 1 - 1 = k - 2 by ring]
  obtain ⟨t, ht⟩ := Int.even_mul_pred_self (k - 1)
  rw [show k - 1 - 1 = k - 2 by ring] at ht
  rw [ht]
  omega

/-- **The strict ray value at height `K`** (ALL_SLOPE_STEP, "Strictness excludes height K*"): `m(K−1) ≤ F(p+K, q+K)`. The anchor is
`(3−K, K−2)`, with `t(anchor) ≤ t(ray)` when `NK ≥ D + 2N − 1`; the odd sheet monotonicity (from `hsig`) compares them. -/
theorem ray_strict {F : Field} (frame : ChildFrame) (hP : frame.Packet F)
    (hsig : ∀ w ∈ frame.closedPolygon, F w - F (w - frame.shortShift) ≤ 0)
    {p q : ℤ} (hs : frame.child.num * p - frame.child.den * q = 2 - frame.child.num) (K : ℕ)
    (hK2 : 2 ≤ K)
    (hKs : frame.child.den + 2 * frame.child.num - 1 ≤ frame.child.num * (K : ℤ))
    (hKr : 2 * frame.child.num * (K : ℤ) ≤ 3 * frame.child.den + 5 * frame.child.num - 1) :
    FLatticePaper.QuadraticCap.capMin ((K : ℤ) - 1) ≤ F (p + (K : ℤ), q + (K : ℤ)) := by
  have hpq := start_parity frame hs
  obtain ⟨hn1, hn2, -, hd3, -⟩ := frame.child_facts
  have hK2' : (2 : ℤ) ≤ (K : ℤ) := by exact_mod_cast hK2
  have hanc := anchor3_value hP.strips (K : ℤ) (by nlinarith) (by nlinarith)
  have htA : frame.tGrade (3 - (K : ℤ), (K : ℤ) - 2)
      = frame.child.num * (3 - (K : ℤ)) - frame.child.den * ((K : ℤ) - 2) := by
    unfold ChildFrame.tGrade
    rfl
  have htR : frame.tGrade (p + (K : ℤ), q + (K : ℤ))
      = 2 - frame.child.num - (K : ℤ) * (frame.child.den - frame.child.num) := by
    unfold ChildFrame.tGrade
    linear_combination hs
  have hK3 : (0 : ℤ) ≤ (K : ℤ) - 2 := by omega
  have hD1 : (0 : ℤ) ≤ frame.child.den - frame.child.num - 1 := by omega
  have hprod := mul_nonneg hK3 hD1
  have hmono := sheetMono_odd_of_signed frame hP hsig (3 - (K : ℤ), (K : ℤ) - 2) (p + (K : ℤ), q + (K : ℤ))
    (by unfold EvenSite; simp only; omega) (by unfold EvenSite; simp only; omega)
    (by rw [htA, htR]; nlinarith) (by rw [htR]; nlinarith)
  rw [hanc] at hmono
  exact hmono

/-- The even ray point at height `K` is strictly above `m(K)`: `2 F c ≥ F(west) + F(east)` with `F(west) ≥ m(K−1)`, `F(east) ≥ m(K)`. -/
theorem even_ray_strict {F : Field} (frame : ChildFrame) (hP : frame.Packet F)
    (hsig : ∀ w ∈ frame.closedPolygon, F w - F (w - frame.shortShift) ≤ 0)
    {p q : ℤ} (hs : frame.child.num * p - frame.child.den * q = 2 - frame.child.num) (K : ℕ)
    (hK2 : 2 ≤ K)
    (hKs : frame.child.den + 2 * frame.child.num - 1 ≤ frame.child.num * (K : ℤ))
    (hKr : 2 * frame.child.num * (K : ℤ) ≤ 3 * frame.child.den + 5 * frame.child.num - 1)
    (hcap : ∀ k : ℕ, k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ F (p + (k : ℤ), q + (k : ℤ))) :
    FLatticePaper.QuadraticCap.capMin (K : ℤ) < F (p + (K : ℤ) + 1, q + (K : ℤ)) := by
  have hpq := start_parity frame hs
  obtain ⟨hn1, hn2, -, hd3, -⟩ := frame.child_facts
  have hK2' : (2 : ℤ) ≤ (K : ℤ) := by exact_mod_cast hK2
  have hW := ray_strict frame hP hsig hs K hK2 hKs hKr
  have hkC := kC_nonneg frame K
  have hev : EvenSite (p + (K : ℤ) + 1, q + (K : ℤ)) := by unfold EvenSite; simp only; omega
  have hinN : incomingNeg (p + (K : ℤ) + 1, q + (K : ℤ)) = (p + (K : ℤ), q + (K : ℤ)) := by
    unfold incomingNeg; rw [if_pos hev]; congr 1; ring
  have hinP : incomingPos (p + (K : ℤ) + 1, q + (K : ℤ)) = (p + (K : ℤ) + 2, q + (K : ℤ)) := by
    unfold incomingPos; rw [if_pos hev]; congr 1; ring
  have hb := hP.binary (p + (K : ℤ) + 1, q + (K : ℤ))
  unfold laplacian at hb
  rw [hinN, hinP] at hb
  have hzo : ¬ EvenSite (p + (K : ℤ) + 2, q + (K : ℤ)) := by unfold EvenSite; simp only; omega
  have hrtE : frame.tGrade (p + (K : ℤ) + 2, q + (K : ℤ))
      = 2 + frame.child.num - (K : ℤ) * (frame.child.den - frame.child.num) := by
    simp only [ChildFrame.tGrade]; linear_combination hs
  have hE := odd_halo frame hP hsig hs K hcap K le_rfl (p + (K : ℤ) + 2, q + (K : ℤ)) hzo
    (by rw [hrtE]; linarith)
    (by rw [hrtE]; nlinarith)
  have h2 : FLatticePaper.QuadraticCap.capMin ((K : ℤ) - 1) - FLatticePaper.QuadraticCap.capMin (K : ℤ) = (K : ℤ) - 1 := by
    have h1 := FLatticePaper.QuadraticCap.two_capMin ((K : ℤ) - 1)
    have h2' := FLatticePaper.QuadraticCap.two_capMin (K : ℤ)
    have h3 : 2 * (FLatticePaper.QuadraticCap.capMin ((K : ℤ) - 1) - FLatticePaper.QuadraticCap.capMin (K : ℤ))
        = 2 * ((K : ℤ) - 1) := by linear_combination h1 - h2'
    linarith
  rcases hb with h | h <;> linarith


/-- `m(K−1) − m(K) = K − 1`. -/
theorem capMin_pred_sub (K : ℤ) :
    FLatticePaper.QuadraticCap.capMin (K - 1) - FLatticePaper.QuadraticCap.capMin K = K - 1 := by
  have h1 := FLatticePaper.QuadraticCap.two_capMin (K - 1)
  have h2 := FLatticePaper.QuadraticCap.two_capMin K
  have h3 : 2 * (FLatticePaper.QuadraticCap.capMin (K - 1) - FLatticePaper.QuadraticCap.capMin K)
      = 2 * (K - 1) := by linear_combination h1 - h2
  linarith

/-- **The cone strict top** (the upper arc): every cone input `w` at height `K` lies strictly above `m(K)`. The even case compares with the
even ray point (`even_ray_strict`), the odd case with the ray point (`ray_strict`); the zero strip covers `t w > 0`. -/
theorem cone_strict_top {F : Field} (frame : ChildFrame) (hP : frame.Packet F)
    (hsig : ∀ w ∈ frame.closedPolygon, F w - F (w - frame.shortShift) ≤ 0)
    {p q : ℤ} (hs : frame.child.num * p - frame.child.den * q = 2 - frame.child.num) (K : ℕ)
    (hK2 : 2 ≤ K)
    (hKs : frame.child.den + 2 * frame.child.num - 1 ≤ frame.child.num * (K : ℤ))
    (hKr : 2 * frame.child.num * (K : ℤ) ≤ 3 * frame.child.den + 5 * frame.child.num - 1)
    (hcap : ∀ k : ℕ, k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ F (p + (k : ℤ), q + (k : ℤ)))
    (b : Site) (hb : frame.child.num + 2 ≤ frame.tGrade b)
    (w : Site) (hwK : w.2 - b.2 = (K : ℤ))
    (hevw : EvenSite w → w.1 - b.1 ≥ (K : ℤ) - 1) (hoddw : ¬ EvenSite w → w.1 - b.1 ≥ (K : ℤ) - 2)
    (hpoly : w ∈ frame.closedPolygon) :
    FLatticePaper.QuadraticCap.capMin (K : ℤ) < F w := by
  have hpq := start_parity frame hs
  obtain ⟨hn1, hn2, -, hd3, -⟩ := frame.child_facts
  have hK2' : (2 : ℤ) ≤ (K : ℤ) := by exact_mod_cast hK2
  have htw : frame.tGrade w
      = frame.tGrade b + frame.child.num * (w.1 - b.1) - frame.child.den * (K : ℤ) := by
    unfold ChildFrame.tGrade
    rw [← hwK]
    ring
  have hup : frame.tGrade w ≤ frame.child.num + 2 * frame.child.den - 1 := by
    unfold ChildFrame.closedPolygon at hpoly
    simp only [Set.mem_setOf_eq] at hpoly
    split_ifs at hpoly with he
    · omega
    · omega
  have hcapK : FLatticePaper.QuadraticCap.capMin (K : ℤ) ≤ -1 := by
    have h := FLatticePaper.QuadraticCap.two_capMin (K : ℤ)
    nlinarith
  have hpar : frame.tGrade (p + (K : ℤ) + 1, q + (K : ℤ))
      = 2 - (K : ℤ) * (frame.child.den - frame.child.num) := by
    unfold ChildFrame.tGrade
    linear_combination hs
  have hrayt : frame.tGrade (p + (K : ℤ), q + (K : ℤ))
      = 2 - frame.child.num - (K : ℤ) * (frame.child.den - frame.child.num) := by
    unfold ChildFrame.tGrade
    linear_combination hs
  by_cases hz : EvenSite w
  · have hl := hevw hz
    have hc := even_ray_strict frame hP hsig hs K hK2 hKs hKr hcap
    have hm := mul_le_mul_of_nonneg_left (show (K : ℤ) - 1 ≤ w.1 - b.1 by linarith)
      (show (0 : ℤ) ≤ frame.child.num by omega)
    by_cases ht0 : frame.tGrade w ≤ 0
    · have hevc : EvenSite (p + (K : ℤ) + 1, q + (K : ℤ)) := by unfold EvenSite; simp only; omega
      have hF := sheetMono_even_of_signed frame hP hsig (p + (K : ℤ) + 1, q + (K : ℤ)) w hevc hz
        (by rw [hpar, htw]; nlinarith) ht0
      linarith
    · have hF0 : F w = 0 := hP.strips.1 w (by omega) hup
      rw [hF0]
      linarith
  · have hl := hoddw hz
    have hc := ray_strict frame hP hsig hs K hK2 hKs hKr
    have hdiff := capMin_pred_sub (K : ℤ)
    have hm := mul_le_mul_of_nonneg_left (show (K : ℤ) - 2 ≤ w.1 - b.1 by linarith)
      (show (0 : ℤ) ≤ frame.child.num by omega)
    by_cases ht0 : frame.tGrade w ≤ 0
    · have hodr : ¬ EvenSite (p + (K : ℤ), q + (K : ℤ)) := by unfold EvenSite; simp only; omega
      have hF := sheetMono_odd_of_signed frame hP hsig (p + (K : ℤ), q + (K : ℤ)) w hodr hz
        (by rw [hrayt, htw]; nlinarith) ht0
      linarith
    · have hF0 : F w = 0 := hP.strips.1 w (by omega) hup
      rw [hF0]
      linarith

/-- **The lower arc**: a height-`b_y` even site with `x ≥ b_x` is not in the open rectangle (its `t` is at least `N+2 ≥ 2`). -/
theorem lower_arc (frame : ChildFrame) (b : Site) (hb : frame.child.num + 2 ≤ frame.tGrade b)
    (w : Site) (hz : EvenSite w) (hh : w.2 = b.2) (hl : b.1 ≤ w.1) : ¬ frame.openRect w := by
  intro ho
  unfold ChildFrame.openRect at ho
  rw [if_pos hz] at ho
  have htw : frame.tGrade w = frame.tGrade b + frame.child.num * (w.1 - b.1) - frame.child.den * (w.2 - b.2) := by
    unfold ChildFrame.tGrade
    ring
  rw [hh, sub_self, mul_zero, sub_zero] at htw
  obtain ⟨hn1, -, -, -, -⟩ := frame.child_facts
  have hm := mul_nonneg (show (0 : ℤ) ≤ frame.child.num by omega) (show (0 : ℤ) ≤ w.1 - b.1 by omega)
  have ht2 := ho.2.1
  linarith

/-- **A fan step stays in the window** (the two height bounds of the cone, ALL_SLOPE_STEP "Propagation"). Let `x` be a window root
(open rectangle and cone) and `w` its fan successor (`fan_step`: east from an even root; north or south from an odd root), with `w`
open and a contact (`F w = m w`). Then `w` is again a window root. The south step from height `1` lands on the lower arc, which is not
open (`lower_arc`); the north step to height `K` is a contact strictly above `m(K)` (`cone_strict_top`), so it cannot occur. -/
theorem fan_next_P {F : Field} (frame : ChildFrame) (hP : frame.Packet F)
    (hsig : ∀ w ∈ frame.closedPolygon, F w - F (w - frame.shortShift) ≤ 0)
    {p q : ℤ} (hs : frame.child.num * p - frame.child.den * q = 2 - frame.child.num) (K : ℕ)
    (hK2 : 2 ≤ K)
    (hKs : frame.child.den + 2 * frame.child.num - 1 ≤ frame.child.num * (K : ℤ))
    (hKr : 2 * frame.child.num * (K : ℤ) ≤ 3 * frame.child.den + 5 * frame.child.num - 1)
    (hcap : ∀ k : ℕ, k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ F (p + (k : ℤ), q + (k : ℤ)))
    (b : Site) (hb : frame.child.num + 2 ≤ frame.tGrade b) (x w : Site)
    (hx : frame.openRect x ∧ ConeRoot b K x)
    (hw : w = incomingNeg x ∨ w = incomingPos x)
    (hEven : EvenSite x → w = incomingPos x)
    (hopen : frame.openRect w)
    (hcontact : F w = FLatticePaper.QuadraticCap.capMin (w.2 - b.2)) :
    frame.openRect w ∧ ConeRoot b K w := by
  refine ⟨hopen, ?_⟩
  obtain ⟨hxo, hR⟩ := hx
  obtain ⟨h1, h2, hevx, hoddx⟩ := hR
  have hpoly : w ∈ frame.closedPolygon := FLatticePaper.W1Exit.rectInputs frame x hxo w hw
  have hpq := start_parity frame hs
  obtain ⟨hn1, -, -, hd3, -⟩ := frame.child_facts
  by_cases hxe : EvenSite x
  · -- an even root moves east to an odd root of the same height
    have hwe := hEven hxe
    subst hwe
    have hp : incomingPos x = (x.1 + 1, x.2) := by unfold incomingPos; rw [if_pos hxe]
    rw [hp]
    have hxu : (x.1 + x.2) % 2 = 0 := hxe
    unfold ConeRoot
    refine ⟨?_, ?_, fun h => ?_, fun _ => ?_⟩
    · dsimp only; omega
    · dsimp only; omega
    · exfalso; unfold EvenSite at h; dsimp only at h; omega
    · dsimp only; have := hevx hxe; omega
  · have hxo' : ¬ (x.1 + x.2) % 2 = 0 := hxe
    have hl := hoddx hxe
    rcases hw with hw | hw
    · -- south: the even root at height `k − 1`; height `1` is the lower arc
      have hpw : w = (x.1, x.2 - 1) := by rw [hw]; unfold incomingNeg; rw [if_neg hxe]
      subst hpw
      have hk2 : 2 ≤ x.2 - b.2 := by
        by_contra hc
        have hk1 : x.2 - b.2 = 1 := by omega
        exact lower_arc frame b hb (x.1, x.2 - 1) (by unfold EvenSite; dsimp only; omega)
          (by dsimp only; omega) (by dsimp only; omega) hopen
      unfold ConeRoot
      refine ⟨?_, ?_, fun _ => ?_, fun h => ?_⟩
      · dsimp only; omega
      · dsimp only; omega
      · dsimp only; omega
      · exfalso; exact h (by unfold EvenSite; dsimp only; omega)
    · -- north: the even root at height `k + 1`; height `K` is a contact strictly above `m(K)`
      have hpw : w = (x.1, x.2 + 1) := by rw [hw]; unfold incomingPos; rw [if_neg hxe]
      subst hpw
      have hne : x.2 - b.2 + 1 ≠ (K : ℤ) := by
        intro heq
        have hlt := cone_strict_top frame hP hsig hs K hK2 hKs hKr hcap b hb (x.1, x.2 + 1)
          (by dsimp only; omega)
          (fun _ => by dsimp only; omega)
          (fun h => absurd (by unfold EvenSite; dsimp only; omega) h)
          hpoly
        rw [hcontact] at hlt
        dsimp only at hlt
        rw [show x.2 + 1 - b.2 = (K : ℤ) by omega] at hlt
        exact lt_irrefl _ hlt
      unfold ConeRoot
      refine ⟨?_, ?_, fun _ => ?_, fun h => ?_⟩
      · dsimp only; omega
      · dsimp only; omega
      · dsimp only; omega
      · exfalso; exact h (by unfold EvenSite; dsimp only; omega)

end FLatticePaper.CapRay
