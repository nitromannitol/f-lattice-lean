import FLatticePaper.Plane.Induction.CapRayGrades
import FLatticePaper.Plane.Induction.ConeRoot
import FLatticePaper.Plane.Induction.FanPropagation
import FLatticePaper.Plane.Induction.CapRecursion
import FLatticePaper.Plane.Induction.FanRegion
import FLatticePaper.Plane.Induction.ContactCone

/-! # The cone window in (N, D)-grades (the abstract form of `CapRay.odd_halo`, `even_ray_lower`, `even_halo`, `cone_input`, `cone_window`)

The halo lemmas of the H cap use the frame's grades `tGrade = num x − den y`, the zero strip, the odd and even sheet monotonicities, and
the ray start `num p − den q = 2 − num`. Here they are stated for integers `N, D` and an offset `a` (`a = 2` in the H long case, `a = 1`
in the rotated long V case): the start is `N p − D q = a − N`, the halo thresholds are `a − N − kC` (odd) and `a − kC` (even), with
`C = D − N`, and the apex bound of the cone is `N + a ≤ t'(b)`. The two inputs of an open-rectangle root are bounded by the zero strip
by arithmetic on the open-rectangle inequalities (no closed polygon is needed). -/

namespace FLatticePaper.CapConeGrades

open FLatticePaper FLatticePaper.CapRecursion FLatticePaper.CapRay FLatticePaper.FanPropagation

/-- The grades and the cap data of the residual: the binary laplacian, the zero strip, and the two same-sheet monotonicities. -/
structure NLCap (N D : ℤ) (F : Field) : Prop where
  binary : ∀ x : Site, laplacian F x = -1 ∨ laplacian F x = 0
  zero : ∀ w : Site, 1 - D ≤ N * w.1 - D * w.2 → N * w.1 - D * w.2 ≤ N + 2 * D - 1 → F w = 0
  odd : ∀ u v : Site, ¬ EvenSite u → ¬ EvenSite v → N * u.1 - D * u.2 ≤ N * v.1 - D * v.2 →
    N * v.1 - D * v.2 ≤ 0 → F u ≤ F v
  even : ∀ u v : Site, EvenSite u → EvenSite v → N * u.1 - D * u.2 ≤ N * v.1 - D * v.2 →
    N * v.1 - D * v.2 ≤ 0 → F u ≤ F v
  harm : ∀ w : Site, 1 - 2 * D ≤ (D + N) * w.1 + (D - N) * w.2 → (D + N) * w.1 + (D - N) * w.2 ≤ 2 * (D + N) - 1 →
    F w = FLatticePaper.Induction.harmonicGrid w

/-- The open rectangle in the residual grades (the strict interior of the child frame with `(num, den) = (N, D)`, and the period `T`). -/
def ropenNL (N D T : ℤ) (z : Site) : Prop :=
  if EvenSite z then
    D + N - 2 - T < N * z.1 - D * z.2 ∧ N * z.1 - D * z.2 < 2 ∧ 2 * N < (D + N) * z.1 + (D - N) * z.2 ∧
      (D + N) * z.1 + (D - N) * z.2 < T
  else
    D - T < N * z.1 - D * z.2 ∧ N * z.1 - D * z.2 < N ∧ D + N - 2 < (D + N) * z.1 + (D - N) * z.2 ∧
      (D + N) * z.1 + (D - N) * z.2 < T + 2 - D + N

theorem kC_nonneg_NL {N D : ℤ} (hND : N < D) (k : ℕ) : 0 ≤ (k : ℤ) * (D - N) :=
  mul_nonneg (by positivity) (by omega)

/-- The inputs of a cone root are cone inputs (the combinatorial part of the cone, copied from `CapRay.cone_input_of_root`). -/
theorem cone_input_of_root_NL (b : Site) (K : ℕ) (x : Site) (hR : ConeRoot b K x) (i : Site)
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

/-- **The odd halo** (the odd inputs of the cone): an odd site with residual grade in `[a − N − kC, N + 2D − 1]` has `m(k) ≤ F z`. -/
theorem odd_halo_NL {N D a : ℤ} {F : Field} (H : NLCap N D F) (hND : N < D)
    {p q : ℤ} (hs : N * p - D * q = a - N) (hpq : (p + q) % 2 = 1)
    (K : ℕ) (hcap : ∀ k : ℕ, k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ F (p + (k : ℤ), q + (k : ℤ)))
    (k : ℕ) (hk : k ≤ K) (z : Site) (hz : ¬ EvenSite z)
    (hlo : a - N - (k : ℤ) * (D - N) ≤ N * z.1 - D * z.2)
    (hup : N * z.1 - D * z.2 ≤ N + 2 * D - 1) :
    FLatticePaper.QuadraticCap.capMin k ≤ F z := by
  have hr : ¬ EvenSite (p + (k : ℤ), q + (k : ℤ)) := by
    unfold EvenSite
    simp only
    omega
  have hrt : N * (p + (k : ℤ)) - D * (q + (k : ℤ)) = a - N - (k : ℤ) * (D - N) := by
    linear_combination hs
  have hcapk := hcap k hk
  by_cases hz0 : N * z.1 - D * z.2 ≤ 0
  · have hF := H.odd (p + (k : ℤ), q + (k : ℤ)) z hr hz (by rw [hrt]; exact hlo) hz0
    exact hcapk.trans hF
  · have hz0' : 0 < N * z.1 - D * z.2 := lt_of_not_ge hz0
    have hF0 : F z = 0 := H.zero z (by linarith) hup
    rw [hF0]
    have hk1 : (0 : ℤ) ≤ (k : ℤ) * ((k : ℤ) - 1) := by
      rcases Nat.eq_zero_or_pos k with h | h
      · subst h
        simp
      · have h1 : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast h
        nlinarith
    have h2 : 0 ≤ (k : ℤ) * ((k : ℤ) - 1) / 2 := Int.ediv_nonneg hk1 (by norm_num)
    unfold FLatticePaper.QuadraticCap.capMin
    linarith

/-- **The even ray value** (the even neighbour of the ray point): the even site `(p+k+1, q+k)` is at least `m(k)`, from its west input
on the ray and its east input (`odd_halo_NL`). -/
theorem even_ray_lower_NL {N D a : ℤ} {F : Field} (H : NLCap N D F) (hN0 : 0 < N) (hND : N < D) (ha2 : a ≤ 2)
    {p q : ℤ} (hs : N * p - D * q = a - N) (hpq : (p + q) % 2 = 1)
    (K : ℕ) (hcap : ∀ k : ℕ, k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ F (p + (k : ℤ), q + (k : ℤ)))
    (k : ℕ) (hk : k ≤ K) :
    FLatticePaper.QuadraticCap.capMin k ≤ F (p + (k : ℤ) + 1, q + (k : ℤ)) := by
  have hkC := kC_nonneg_NL hND k
  have hev : EvenSite (p + (k : ℤ) + 1, q + (k : ℤ)) := by
    unfold EvenSite
    simp only
    omega
  have hinN : incomingNeg (p + (k : ℤ) + 1, q + (k : ℤ)) = (p + (k : ℤ), q + (k : ℤ)) := by
    unfold incomingNeg
    rw [if_pos hev]
    congr 1
    ring
  have hinP : incomingPos (p + (k : ℤ) + 1, q + (k : ℤ)) = (p + (k : ℤ) + 2, q + (k : ℤ)) := by
    unfold incomingPos
    rw [if_pos hev]
    congr 1
    ring
  have hb := H.binary (p + (k : ℤ) + 1, q + (k : ℤ))
  unfold laplacian at hb
  rw [hinN, hinP] at hb
  have hW := hcap k hk
  have hzo : ¬ EvenSite (p + (k : ℤ) + 2, q + (k : ℤ)) := by
    unfold EvenSite
    simp only
    omega
  have hrtE : N * (p + (k : ℤ) + 2) - D * (q + (k : ℤ)) = a + N - (k : ℤ) * (D - N) := by
    linear_combination hs
  have hE := odd_halo_NL H hND hs hpq K hcap k hk (p + (k : ℤ) + 2, q + (k : ℤ)) hzo
    (by dsimp only; linarith [hrtE, hN0])
    (by dsimp only; nlinarith [hrtE, kC_nonneg_NL hND k, hN0])
  rcases hb with h | h <;> linarith

/-- **The even halo** (the even inputs of the cone): an even site with residual grade in `[a − kC, N + 2D − 1]` has `m(k) ≤ F z`. -/
theorem even_halo_NL {N D a : ℤ} {F : Field} (H : NLCap N D F) (hN0 : 0 < N) (hND : N < D) (ha2 : a ≤ 2)
    {p q : ℤ} (hs : N * p - D * q = a - N) (hpq : (p + q) % 2 = 1)
    (K : ℕ) (hcap : ∀ k : ℕ, k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ F (p + (k : ℤ), q + (k : ℤ)))
    (k : ℕ) (hk : k ≤ K) (z : Site) (hz : EvenSite z)
    (hlo : a - (k : ℤ) * (D - N) ≤ N * z.1 - D * z.2)
    (hup : N * z.1 - D * z.2 ≤ N + 2 * D - 1) :
    FLatticePaper.QuadraticCap.capMin k ≤ F z := by
  have hr : EvenSite (p + (k : ℤ) + 1, q + (k : ℤ)) := by
    unfold EvenSite
    simp only
    omega
  have hrt : N * (p + (k : ℤ) + 1) - D * (q + (k : ℤ)) = a - (k : ℤ) * (D - N) := by
    linear_combination hs
  have hR := even_ray_lower_NL H hN0 hND ha2 hs hpq K hcap k hk
  by_cases hz0 : N * z.1 - D * z.2 ≤ 0
  · have hF := H.even (p + (k : ℤ) + 1, q + (k : ℤ)) z hr hz (by rw [hrt]; exact hlo) hz0
    exact hR.trans hF
  · have hz0' : 0 < N * z.1 - D * z.2 := lt_of_not_ge hz0
    have hF0 : F z = 0 := H.zero z (by linarith) hup
    rw [hF0]
    have hk1 : (0 : ℤ) ≤ (k : ℤ) * ((k : ℤ) - 1) := by
      rcases Nat.eq_zero_or_pos k with h | h
      · subst h
        simp
      · have h1 : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast h
        nlinarith
    have h2 : 0 ≤ (k : ℤ) * ((k : ℤ) - 1) / 2 := Int.ediv_nonneg hk1 (by norm_num)
    unfold FLatticePaper.QuadraticCap.capMin
    linarith

/-- **The cone input bound.** An input `i` of the cone of base `b` (apex bound `N + a ≤ t'(b)`) with the zero-strip upper bound satisfies
`m(k) ≤ F i`, `k = i_y − b_y`: the lower bound of the residual grade is the halo threshold, by the cone inequalities. -/
theorem cone_input_NL {N D a : ℤ} {F : Field} (H : NLCap N D F) (hN0 : 0 < N) (hND : N < D) (ha2 : a ≤ 2)
    {p q : ℤ} (hs : N * p - D * q = a - N) (hpq : (p + q) % 2 = 1)
    (K : ℕ) (hcap : ∀ k : ℕ, k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ F (p + (k : ℤ), q + (k : ℤ)))
    (b : Site) (hb : N + a ≤ N * b.1 - D * b.2)
    (i : Site) (hI : InCone b K i) (hup : N * i.1 - D * i.2 ≤ N + 2 * D - 1) :
    FLatticePaper.QuadraticCap.capMin (i.2 - b.2) ≤ F i := by
  obtain ⟨hk0, hkK, hev, hodd⟩ := hI
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = i.2 - b.2 := ⟨(i.2 - b.2).toNat, Int.toNat_of_nonneg hk0⟩
  have hkK' : k ≤ K := by omega
  rw [← hk]
  have htb : N * i.1 - D * i.2 = (N * b.1 - D * b.2) + N * (i.1 - b.1) - D * (i.2 - b.2) := by ring
  have hDk : D * (i.2 - b.2) = D * (k : ℤ) := by rw [hk]
  by_cases hz : EvenSite i
  · have hl := hev hz
    have hm : (k : ℤ) - 1 ≤ i.1 - b.1 := by omega
    have hmul : N * ((k : ℤ) - 1) ≤ N * (i.1 - b.1) := mul_le_mul_of_nonneg_left hm (by linarith)
    have hlo : a - (k : ℤ) * (D - N) ≤ N * i.1 - D * i.2 := by
      have : N * ((k : ℤ) - 1) = N * (k : ℤ) - N := by ring
      nlinarith
    exact even_halo_NL H hN0 hND ha2 hs hpq K hcap k hkK' i hz hlo hup
  · have hl := hodd hz
    have hm : (k : ℤ) - 2 ≤ i.1 - b.1 := by omega
    have hmul : N * ((k : ℤ) - 2) ≤ N * (i.1 - b.1) := mul_le_mul_of_nonneg_left hm (by linarith)
    have hlo : a - N - (k : ℤ) * (D - N) ≤ N * i.1 - D * i.2 := by
      have : N * ((k : ℤ) - 2) = N * (k : ℤ) - 2 * N := by ring
      nlinarith
    exact odd_halo_NL H hND hs hpq K hcap k hkK' i hz hlo hup

/-- **The inputs of an open-rectangle root satisfy the zero-strip upper bound** (arithmetic on the open-rectangle inequalities). -/
theorem input_bound_NL {N D T : ℤ} (hN0 : 0 < N) (hND : N < D) (x : Site) (hx : ropenNL N D T x)
    (i : Site) (hi : i = incomingNeg x ∨ i = incomingPos x) : N * i.1 - D * i.2 ≤ N + 2 * D - 1 := by
  by_cases he : EvenSite x
  · have hxp : incomingPos x = (x.1 + 1, x.2) := by
      unfold incomingPos
      rw [if_pos he]
    have hxn : incomingNeg x = (x.1 - 1, x.2) := by
      unfold incomingNeg
      rw [if_pos he]
    unfold ropenNL at hx
    rw [if_pos he] at hx
    obtain ⟨-, h1, -, -⟩ := hx
    rcases hi with rfl | rfl
    · rw [hxn]
      dsimp only
      linarith
    · rw [hxp]
      dsimp only
      linarith
  · have hxp : incomingPos x = (x.1, x.2 + 1) := by
      unfold incomingPos
      rw [if_neg he]
    have hxn : incomingNeg x = (x.1, x.2 - 1) := by
      unfold incomingNeg
      rw [if_neg he]
    unfold ropenNL at hx
    rw [if_neg he] at hx
    obtain ⟨-, h1, -, -⟩ := hx
    rcases hi with rfl | rfl
    · rw [hxn]
      dsimp only
      linarith
    · rw [hxp]
      dsimp only
      linarith

/-- **The cone window in (N, D)-grades** (the abstract `CapRay.cone_window`): on the open rectangle `ropenNL N D T` and the cone of base
`b` (apex bound `N + a ≤ t'(b)`), every input `i` of a root `x` satisfies `m(i) ≤ F i`, with `m i = capMin (i_y − b_y)`. -/
theorem cone_window_NL {N D a : ℤ} {F : Field} (H : NLCap N D F) (T : ℤ) (hN0 : 0 < N) (hND : N < D) (ha2 : a ≤ 2)
    {p q : ℤ} (hs : N * p - D * q = a - N) (hpq : (p + q) % 2 = 1)
    (K : ℕ) (hcap : ∀ k : ℕ, k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ F (p + (k : ℤ), q + (k : ℤ)))
    (b : Site) (hb : N + a ≤ N * b.1 - D * b.2) :
    WindowOn (fun x => ropenNL N D T x ∧ ConeRoot b K x) F (fun i => FLatticePaper.QuadraticCap.capMin (i.2 - b.2)) := by
  intro x hx i hi
  obtain ⟨hopen, hR⟩ := hx
  exact cone_input_NL H hN0 hND ha2 hs hpq K hcap b hb i (cone_input_of_root_NL b K x hR i hi)
    (input_bound_NL hN0 hND x hopen i hi)

theorem capMin_pred_sub_NL (K : ℤ) :
    FLatticePaper.QuadraticCap.capMin (K - 1) - FLatticePaper.QuadraticCap.capMin K = K - 1 := by
  have h1 := FLatticePaper.QuadraticCap.two_capMin (K - 1)
  have h2 := FLatticePaper.QuadraticCap.two_capMin K
  have h3 : 2 * (FLatticePaper.QuadraticCap.capMin (K - 1) - FLatticePaper.QuadraticCap.capMin K)
      = 2 * (K - 1) := by linear_combination h1 - h2
  linarith

/-- The third anchor `F(3−k, k−2) = m(k−1)` on the harmonic window. -/
theorem anchor3_NL {N D : ℤ} {F : Field} (H : NLCap N D F) (k : ℤ)
    (hlo : 1 - 2 * D ≤ D + 5 * N - 2 * N * k) (hhi : D + 5 * N - 2 * N * k ≤ 2 * (D + N) - 1) :
    F (3 - k, k - 2) = FLatticePaper.QuadraticCap.capMin (k - 1) := by
  have e : (D + N) * (3 - k) + (D - N) * (k - 2) = D + 5 * N - 2 * N * k := by ring
  rw [H.harm (3 - k, k - 2) (by dsimp only; rw [e]; exact hlo) (by dsimp only; rw [e]; exact hhi)]
  unfold FLatticePaper.Induction.harmonicGrid FLatticePaper.QuadraticCap.capMin
  have e2 : (3 - k) ^ 2 + 2 * (3 - k) * (k - 2) - (k - 2) ^ 2 - 2 * (k - 2) - ((3 - k) + (k - 2)) % 2
      = -2 * ((k - 1) * (k - 2)) := by
    have h1 : ((3 - k) + (k - 2)) % 2 = 1 := by omega
    rw [h1]
    ring
  dsimp only
  rw [e2, show k - 1 - 1 = k - 2 by ring]
  obtain ⟨t, ht⟩ := Int.even_mul_pred_self (k - 1)
  rw [show k - 1 - 1 = k - 2 by ring] at ht
  rw [ht]
  omega

/-- The strict ray value at height `K`: `m(K−1) ≤ F(p+K, q+K)` (the anchor `(3−K, K−2)`, compared on the odd sheet). -/
theorem ray_strict_NL {N D a : ℤ} {F : Field} (H : NLCap N D F) (hN0 : 0 < N) (hND : N < D) (ha2 : a ≤ 2)
    {p q : ℤ} (hs : N * p - D * q = a - N) (hpq : (p + q) % 2 = 1)
    (K : ℕ) (hK2 : 2 ≤ K)
    (hKs : 4 * N + 2 * D - a ≤ 2 * N * (K : ℤ))
    (hKr : 2 * N * (K : ℤ) ≤ 3 * D + 5 * N - 1) :
    FLatticePaper.QuadraticCap.capMin ((K : ℤ) - 1) ≤ F (p + (K : ℤ), q + (K : ℤ)) := by
  have hK2' : (2 : ℤ) ≤ (K : ℤ) := by exact_mod_cast hK2
  have hanc := anchor3_NL H (K : ℤ) (by nlinarith) (by nlinarith)
  have htA : N * (3 - (K : ℤ)) - D * ((K : ℤ) - 2) = N * (3 - (K : ℤ)) - D * ((K : ℤ) - 2) := rfl
  have htR : N * (p + (K : ℤ)) - D * (q + (K : ℤ)) = a - N - (K : ℤ) * (D - N) := by
    linear_combination hs
  have hK3 : (0 : ℤ) ≤ (K : ℤ) - 2 := by omega
  have hD1 : (0 : ℤ) ≤ D - N - 1 := by omega
  have hprod := mul_nonneg hK3 hD1
  have hmono := H.odd (3 - (K : ℤ), (K : ℤ) - 2) (p + (K : ℤ), q + (K : ℤ))
    (by unfold EvenSite; simp only; omega) (by unfold EvenSite; simp only; omega)
    (by dsimp only; nlinarith) (by rw [htR]; nlinarith)
  rw [hanc] at hmono
  exact hmono

/-- The even ray point at height `K` is strictly above `m(K)`. -/
theorem even_ray_strict_NL {N D a : ℤ} {F : Field} (H : NLCap N D F) (hN0 : 0 < N) (hND : N < D) (ha2 : a ≤ 2)
    {p q : ℤ} (hs : N * p - D * q = a - N) (hpq : (p + q) % 2 = 1)
    (K : ℕ) (hK2 : 2 ≤ K)
    (hKs : 4 * N + 2 * D - a ≤ 2 * N * (K : ℤ))
    (hKr : 2 * N * (K : ℤ) ≤ 3 * D + 5 * N - 1)
    (hcap : ∀ k : ℕ, k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ F (p + (k : ℤ), q + (k : ℤ))) :
    FLatticePaper.QuadraticCap.capMin (K : ℤ) < F (p + (K : ℤ) + 1, q + (K : ℤ)) := by
  have hK2' : (2 : ℤ) ≤ (K : ℤ) := by exact_mod_cast hK2
  have hW := ray_strict_NL H hN0 hND ha2 hs hpq K hK2 hKs hKr
  have hkC := kC_nonneg_NL hND K
  have hev : EvenSite (p + (K : ℤ) + 1, q + (K : ℤ)) := by
    unfold EvenSite
    simp only
    omega
  have hinN : incomingNeg (p + (K : ℤ) + 1, q + (K : ℤ)) = (p + (K : ℤ), q + (K : ℤ)) := by
    unfold incomingNeg
    rw [if_pos hev]
    congr 1
    ring
  have hinP : incomingPos (p + (K : ℤ) + 1, q + (K : ℤ)) = (p + (K : ℤ) + 2, q + (K : ℤ)) := by
    unfold incomingPos
    rw [if_pos hev]
    congr 1
    ring
  have hb := H.binary (p + (K : ℤ) + 1, q + (K : ℤ))
  unfold laplacian at hb
  rw [hinN, hinP] at hb
  have hzo : ¬ EvenSite (p + (K : ℤ) + 2, q + (K : ℤ)) := by
    unfold EvenSite
    simp only
    omega
  have hrtE : N * (p + (K : ℤ) + 2) - D * (q + (K : ℤ)) = a + N - (K : ℤ) * (D - N) := by
    linear_combination hs
  have hE := odd_halo_NL H hND hs hpq K hcap K le_rfl (p + (K : ℤ) + 2, q + (K : ℤ)) hzo
    (by dsimp only; linarith [hrtE, hN0])
    (by dsimp only; nlinarith [hrtE, kC_nonneg_NL hND K, hN0, hND])
  have h2 := capMin_pred_sub_NL (K : ℤ)
  rcases hb with h | h <;> linarith

/-- **The cone strict top** (in (N, D)-grades): a cone input at height `K` lies strictly above `m(K)`. -/
theorem cone_strict_top_NL {N D a : ℤ} {F : Field} (H : NLCap N D F) (hN0 : 0 < N) (hND : N < D) (ha2 : a ≤ 2)
    {p q : ℤ} (hs : N * p - D * q = a - N) (hpq : (p + q) % 2 = 1)
    (K : ℕ) (hK2 : 2 ≤ K)
    (hKs : 4 * N + 2 * D - a ≤ 2 * N * (K : ℤ))
    (hKr : 2 * N * (K : ℤ) ≤ 3 * D + 5 * N - 1)
    (hcap : ∀ k : ℕ, k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ F (p + (k : ℤ), q + (k : ℤ)))
    (b : Site) (hb : N + a ≤ N * b.1 - D * b.2)
    (w : Site) (hwK : w.2 - b.2 = (K : ℤ))
    (hevw : EvenSite w → w.1 - b.1 ≥ (K : ℤ) - 1) (hoddw : ¬ EvenSite w → w.1 - b.1 ≥ (K : ℤ) - 2)
    (hup : N * w.1 - D * w.2 ≤ N + 2 * D - 1) :
    FLatticePaper.QuadraticCap.capMin (K : ℤ) < F w := by
  have hK2' : (2 : ℤ) ≤ (K : ℤ) := by exact_mod_cast hK2
  have htw : N * w.1 - D * w.2 = (N * b.1 - D * b.2) + N * (w.1 - b.1) - D * (K : ℤ) := by
    have : w.2 = b.2 + (K : ℤ) := by linarith
    rw [this]
    ring
  have hcapK : FLatticePaper.QuadraticCap.capMin (K : ℤ) ≤ -1 := by
    have h := FLatticePaper.QuadraticCap.two_capMin (K : ℤ)
    nlinarith
  have hpar : N * (p + (K : ℤ) + 1) - D * (q + (K : ℤ)) = a - (K : ℤ) * (D - N) := by
    linear_combination hs
  have hrayt : N * (p + (K : ℤ)) - D * (q + (K : ℤ)) = a - N - (K : ℤ) * (D - N) := by
    linear_combination hs
  by_cases hz : EvenSite w
  · have hl := hevw hz
    have hc := even_ray_strict_NL H hN0 hND ha2 hs hpq K hK2 hKs hKr hcap
    have hm := mul_le_mul_of_nonneg_left (show (K : ℤ) - 1 ≤ w.1 - b.1 by linarith)
      (show (0 : ℤ) ≤ N by linarith)
    by_cases ht0 : N * w.1 - D * w.2 ≤ 0
    · have hevc : EvenSite (p + (K : ℤ) + 1, q + (K : ℤ)) := by
        unfold EvenSite
        simp only
        omega
      have hF := H.even (p + (K : ℤ) + 1, q + (K : ℤ)) w hevc hz
        (by dsimp only; rw [hpar, htw]; nlinarith) ht0
      linarith
    · have hF0 : F w = 0 := H.zero w (by linarith) hup
      rw [hF0]
      linarith
  · have hl := hoddw hz
    have hc := ray_strict_NL H hN0 hND ha2 hs hpq K hK2 hKs hKr
    have hdiff := capMin_pred_sub_NL (K : ℤ)
    have hm := mul_le_mul_of_nonneg_left (show (K : ℤ) - 2 ≤ w.1 - b.1 by linarith)
      (show (0 : ℤ) ≤ N by linarith)
    by_cases ht0 : N * w.1 - D * w.2 ≤ 0
    · have hodr : ¬ EvenSite (p + (K : ℤ), q + (K : ℤ)) := by
        unfold EvenSite
        simp only
        omega
      have hF := H.odd (p + (K : ℤ), q + (K : ℤ)) w hodr hz
        (by dsimp only; rw [hrayt, htw]; nlinarith) ht0
      linarith
    · have hF0 : F w = 0 := H.zero w (by linarith) hup
      rw [hF0]
      linarith

/-- The lower arc: an even site at the height of the apex, to its east, is not in the open rectangle. -/
theorem lower_arc_NL {N D a T : ℤ} (hN1 : 1 ≤ N) (ha1 : 1 ≤ a) (b : Site)
    (hb : N + a ≤ N * b.1 - D * b.2) (w : Site) (hz : EvenSite w) (hh : w.2 = b.2) (hl : b.1 ≤ w.1) :
    ¬ ropenNL N D T w := by
  intro ho
  unfold ropenNL at ho
  rw [if_pos hz] at ho
  obtain ⟨-, h2, -, -⟩ := ho
  have htw : N * w.1 - D * w.2 = (N * b.1 - D * b.2) + N * (w.1 - b.1) := by
    rw [hh]
    ring
  have hm : 0 ≤ N * (w.1 - b.1) := mul_nonneg (by linarith) (by linarith)
  linarith

/-- **A fan step stays in the window** (in (N, D)-grades; the abstract `CapRay.fan_next_P`). The successor of a window root that is a
contact is again a window root; the upper arc is excluded by `cone_strict_top_NL`, the lower arc by `lower_arc_NL`. -/
theorem fan_next_NL {N D a T : ℤ} {F : Field} (H : NLCap N D F) (hN0 : 0 < N) (hND : N < D) (ha1 : 1 ≤ a) (ha2 : a ≤ 2)
    {p q : ℤ} (hs : N * p - D * q = a - N) (hpq : (p + q) % 2 = 1)
    (K : ℕ) (hK2 : 2 ≤ K)
    (hKs : 4 * N + 2 * D - a ≤ 2 * N * (K : ℤ))
    (hKr : 2 * N * (K : ℤ) ≤ 3 * D + 5 * N - 1)
    (hcap : ∀ k : ℕ, k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ F (p + (k : ℤ), q + (k : ℤ)))
    (b : Site) (hb : N + a ≤ N * b.1 - D * b.2) (x w : Site)
    (hx : ropenNL N D T x ∧ ConeRoot b K x)
    (hw : w = incomingNeg x ∨ w = incomingPos x)
    (hEven : EvenSite x → w = incomingPos x)
    (hopen : ropenNL N D T w)
    (hcontact : F w = FLatticePaper.QuadraticCap.capMin (w.2 - b.2)) :
    ropenNL N D T w ∧ ConeRoot b K w := by
  refine ⟨hopen, ?_⟩
  obtain ⟨hxo, hR⟩ := hx
  obtain ⟨h1, h2, hevx, hoddx⟩ := hR
  have hupw := input_bound_NL hN0 hND x hxo w hw
  by_cases hxe : EvenSite x
  · have hwe := hEven hxe
    subst hwe
    have hp : incomingPos x = (x.1 + 1, x.2) := by
      unfold incomingPos
      rw [if_pos hxe]
    rw [hp]
    have hxu : (x.1 + x.2) % 2 = 0 := hxe
    unfold ConeRoot
    refine ⟨?_, ?_, fun h => ?_, fun _ => ?_⟩
    · dsimp only
      omega
    · dsimp only
      omega
    · exfalso
      unfold EvenSite at h
      dsimp only at h
      omega
    · dsimp only
      have := hevx hxe
      omega
  · have hxo' : ¬ (x.1 + x.2) % 2 = 0 := hxe
    have hl := hoddx hxe
    rcases hw with hw | hw
    · have hpw : w = (x.1, x.2 - 1) := by
        rw [hw]
        unfold incomingNeg
        rw [if_neg hxe]
      subst hpw
      have hk2 : 2 ≤ x.2 - b.2 := by
        by_contra hc
        have hk1 : x.2 - b.2 = 1 := by omega
        exact lower_arc_NL (by linarith) ha1 b hb (x.1, x.2 - 1) (by unfold EvenSite; dsimp only; omega)
          (by dsimp only; omega) (by dsimp only; omega) hopen
      unfold ConeRoot
      refine ⟨?_, ?_, fun _ => ?_, fun h => ?_⟩
      · dsimp only
        omega
      · dsimp only
        omega
      · dsimp only
        omega
      · exfalso
        exact h (by unfold EvenSite; dsimp only; omega)
    · have hpw : w = (x.1, x.2 + 1) := by
        rw [hw]
        unfold incomingPos
        rw [if_neg hxe]
      subst hpw
      have hne : x.2 - b.2 + 1 ≠ (K : ℤ) := by
        intro heq
        have hlt := cone_strict_top_NL H hN0 hND ha2 hs hpq K hK2 hKs hKr hcap b hb (x.1, x.2 + 1)
          (by dsimp only; omega)
          (fun _ => by dsimp only; omega)
          (fun h => absurd (by unfold EvenSite; dsimp only; omega) h)
          hupw
        rw [hcontact] at hlt
        dsimp only at hlt
        rw [show x.2 + 1 - b.2 = (K : ℤ) by omega] at hlt
        exact lt_irrefl _ hlt
      unfold ConeRoot
      refine ⟨?_, ?_, fun _ => ?_, fun h => ?_⟩
      · dsimp only
        omega
      · dsimp only
        omega
      · dsimp only
        omega
      · exfalso
        exact h (by unfold EvenSite; dsimp only; omega)

/-- **The fan is closed under its contact inputs** (in (N, D)-grades): a contact input of a fan site is in the fan. -/
theorem fan_closed_NL {N D a T : ℤ} {F : Field} (H : NLCap N D F) (hN0 : 0 < N) (hND : N < D) (ha1 : 1 ≤ a) (ha2 : a ≤ 2)
    {p q : ℤ} (hs : N * p - D * q = a - N) (hpq : (p + q) % 2 = 1)
    (K : ℕ) (hK2 : 2 ≤ K)
    (hKs : 4 * N + 2 * D - a ≤ 2 * N * (K : ℤ))
    (hKr : 2 * N * (K : ℤ) ≤ 3 * D + 5 * N - 1)
    (hcap : ∀ k : ℕ, k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ F (p + (k : ℤ), q + (k : ℤ)))
    (b : Site) (hb : N + a ≤ N * b.1 - D * b.2) :
    ∀ x ∈ FLatticePaper.FanRegion.fanSet (ropenNL N D T) F b K, ∀ u : Site,
      (u = incomingNeg x ∨ u = incomingPos x) → (EvenSite x → u = incomingPos x) →
      ropenNL N D T u → F u = ContactCone.parabolaField b.2 u →
      u ∈ FLatticePaper.FanRegion.fanSet (ropenNL N D T) F b K := by
  intro x hx u hu he hR hc
  obtain ⟨⟨hxo, hcone⟩, -⟩ := hx
  exact ⟨⟨hR, (fan_next_NL H hN0 hND ha1 ha2 hs hpq K hK2 hKs hKr hcap b hb x u ⟨hxo, hcone⟩ hu he hR hc).2⟩, hc⟩

/-- **The fan start is forced east (in (N, D)-grades).** The contact fan of the cone of base `b` in the residual open rectangle: a
forced edge out of an even fan start is its east edge (`FanRegion.fan_start_forced_R` with the window `cone_window_NL` and the
closure `fan_closed_NL`). -/
theorem fan_start_forced_NL {N D a T : ℤ} {F : Field} (H : NLCap N D F) (hN0 : 0 < N) (hND : N < D) (ha1 : 1 ≤ a) (ha2 : a ≤ 2)
    {p q : ℤ} (hs : N * p - D * q = a - N) (hpq : (p + q) % 2 = 1)
    (K : ℕ) (hK2 : 2 ≤ K)
    (hKs : 4 * N + 2 * D - a ≤ 2 * N * (K : ℤ))
    (hKr : 2 * N * (K : ℤ) ≤ 3 * D + 5 * N - 1)
    (hcap : ∀ k : ℕ, k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ F (p + (k : ℤ), q + (k : ℤ)))
    (b start : Site) (hb : N + a ≤ N * b.1 - D * b.2)
    (hstart : start ∈ FLatticePaper.FanRegion.fanSet (ropenNL N D T) F b K) (heven : EvenSite start) {o : Site}
    (ho : FLatticePaper.W1.ForcedEdgeIn F (ropenNL N D T) (fun _ _ => False) start o) :
    o = incomingPos start :=
  FLatticePaper.FanRegion.fan_start_forced_R H.binary
    (cone_window_NL H T hN0 hND ha2 hs hpq K hcap b hb)
    (fan_closed_NL H hN0 hND ha1 ha2 hs hpq K hK2 hKs hKr hcap b hb) hstart heven ho

end FLatticePaper.CapConeGrades
