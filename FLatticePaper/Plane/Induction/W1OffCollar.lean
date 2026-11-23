import FLatticePaper.Plane.Induction.W1Exit

/-! # Task 90 (hsq): the off-collar lemma of W1_CONSTRUCTOR §1, in the child's own coordinates

For a child `n/d` (n, d odd, coprime, `d ≥ n + 2`): grades `t = n x − d y`, `s = (d + n) x + (d − n) y`, `T = d² + 2dn − n²`, `L = d + n`.
The strict interior `E°` is `StrictInterior n d` (W1Constructor). A free H vertex is a point of the closed rectangle whose lower neighbour is
outside it, with `t` in the H spectrum; a free V vertex is the analogue with the left neighbour and `s` in the V spectrum. The collar of a
site `z` is the set of strict sites within Chebyshev distance one of a vertex of the bottom H arc, the left V arc, the top arc (`freeH + V`)
or the right arc (`freeV + U`), with `U = (d, n)`, `V = (n − d, d + n)`.

The off-collar lemma: a unit square through a site outside all collars is strictly interior. Its proof: a corner outside `E°` has a
violated inequality (A: `t ≥ a`, B: `t ≤ b − T`, C: `s ≤ h`, D: `s ≥ T + c`), and a fixed offset of the centre (depending on the violated
inequality and the parity of the centre) is a vertex of the matching arc. The witnesses use the lattice exclusions of `W1OffCollar`
(`s_of_t_zero`, `s_of_t_negd`). -/

namespace FLatticePaper.W1OffCollar

open FLatticePaper FLatticePaper.W1

/-- The lattice point with `t = 0` has `s` a multiple of `T`. -/
theorem s_of_t_zero (n d : ℤ) (hcop : IsCoprime n d) (hd : d ≠ 0) (z : Site)
    (ht : w1t n d z = 0) : ∃ k : ℤ, w1s n d z = k * w1T n d := by
  unfold w1t at ht
  have hdvd : d ∣ n * z.1 := ⟨z.2, by linarith⟩
  have hz1 : d ∣ z.1 := (hcop.symm).dvd_of_dvd_mul_left hdvd
  obtain ⟨k, hk⟩ := hz1
  have hz2 : z.2 = n * k := by
    have h1 : d * (n * k - z.2) = 0 := by
      have : n * z.1 = d * z.2 := by linarith
      rw [hk] at this
      linarith
    have := (mul_eq_zero.mp h1).resolve_left hd
    linarith
  refine ⟨k, ?_⟩
  unfold w1s w1T
  rw [hk, hz2]
  ring

/-- The lattice point with `t = −d` has `s = k T + (d − n)`. -/
theorem s_of_t_negd (n d : ℤ) (hcop : IsCoprime n d) (hd : d ≠ 0) (z : Site)
    (ht : w1t n d z = -d) : ∃ k : ℤ, w1s n d z = k * w1T n d + (d - n) := by
  unfold w1t at ht
  have hdvd : d ∣ n * z.1 := ⟨z.2 - 1, by linarith⟩
  have hz1 : d ∣ z.1 := (hcop.symm).dvd_of_dvd_mul_left hdvd
  obtain ⟨k, hk⟩ := hz1
  have hz2 : z.2 = n * k + 1 := by
    have h1 : d * (n * k - z.2 + 1) = 0 := by
      have : n * z.1 = d * z.2 - d := by linarith
      rw [hk] at this
      linarith
    have := (mul_eq_zero.mp h1).resolve_left hd
    linarith
  refine ⟨k, ?_⟩
  unfold w1s w1T
  rw [hk, hz2]
  ring

/-- The H spectrum in the child's coordinates. -/
def hSp (n d t : ℤ) : Prop := (t % 2 = 0 ∧ 2 ≤ t ∧ t ≤ d + n - 2) ∨ (t % 2 = 1 ∧ n ≤ t ∧ t ≤ d)

/-- The V spectrum in the child's coordinates. -/
def vSp (n d s : ℤ) : Prop := s % 2 = 0 ∧ ((0 ≤ s ∧ s ≤ 2 * n) ∨ (2 - d + n ≤ s ∧ s ≤ d + n - 2))

/-- A free H vertex: the bottom arc of the closed rectangle. -/
def freeHn (n d : ℤ) (v : Site) : Prop :=
  closedRect n d v ∧ ¬ closedRect n d (v.1, v.2 - 1) ∧ hSp n d (w1t n d v)

/-- A free V vertex: the left arc of the closed rectangle. -/
def freeVn (n d : ℤ) (v : Site) : Prop :=
  closedRect n d v ∧ ¬ closedRect n d (v.1 - 1, v.2) ∧ vSp n d (w1s n d v)

/-- The closed rectangle at a site, by parity. -/
theorem closedRect_iff (n d : ℤ) (z : Site) :
    closedRect n d z ↔
      (EvenSite z ∧ (2 - w1T n d ≤ w1t n d z ∧ w1t n d z ≤ d + n - 2 ∧ 0 ≤ w1s n d z ∧ w1s n d z ≤ w1T n d + 2 * n)) ∨
      (¬ EvenSite z ∧ (n - w1T n d ≤ w1t n d z ∧ w1t n d z ≤ d ∧ 2 - d + n ≤ w1s n d z ∧
        w1s n d z ≤ w1T n d + d + n - 2)) := by
  unfold closedRect
  by_cases h : EvenSite z <;> simp [h]

/-- The strict interior at an even site. -/
theorem strict_even (n d : ℤ) (z : Site) (hz : EvenSite z) :
    StrictInterior n d z ↔
      (d + n - 2 - w1T n d < w1t n d z ∧ w1t n d z < 2 ∧ 2 * n < w1s n d z ∧ w1s n d z < w1T n d) := by
  unfold StrictInterior w1b w1a w1h w1c
  simp [hz]

/-- The strict interior at an odd site. -/
theorem strict_odd (n d : ℤ) (z : Site) (hz : ¬ EvenSite z) :
    StrictInterior n d z ↔
      (d - w1T n d < w1t n d z ∧ w1t n d z < n ∧ d + n - 2 < w1s n d z ∧
        w1s n d z < w1T n d + (2 - d + n)) := by
  unfold StrictInterior w1b w1a w1h w1c
  simp [hz]

theorem tv (n d : ℤ) (z : Site) (a b : ℤ) :
    w1t n d (z.1 + a, z.2 + b) = w1t n d z + n * a - d * b := by
  unfold w1t
  ring

theorem sv (n d : ℤ) (z : Site) (a b : ℤ) :
    w1s n d (z.1 + a, z.2 + b) = w1s n d z + (d + n) * a + (d - n) * b := by
  unfold w1s
  ring

/-- The witness of the `A` edge at an even centre: `z + (1, −1)` is a free H vertex. -/
theorem witA_even (n d : ℤ) (hn : 3 ≤ n) (hnd : n + 2 ≤ d) (hcop : IsCoprime n d)
    (hno : n % 2 = 1) (hdo : d % 2 = 1) (z : Site) (hev : EvenSite z) (hz : StrictInterior n d z)
    (hlow : 2 - (n + d) ≤ w1t n d z) : freeHn n d (z.1 + 1, z.2 - 1) := by
  have hT : 0 < w1T n d := by unfold w1T; nlinarith
  rw [strict_even n d z hev] at hz
  obtain ⟨h1, h2, h3, h4⟩ := hz
  have hpar : w1t n d z % 2 = 0 := by
    have := FLatticePaper.W1Exit.parity_t n d z.1 z.2 hno hdo
    unfold w1t
    simp only [EvenSite] at hev
    omega
  have ht0 : w1t n d z ≠ 0 := by
    intro h
    obtain ⟨k, hk⟩ := s_of_t_zero n d hcop (by omega) z h
    rw [hk] at h3 h4
    have : k ≤ 0 ∨ 1 ≤ k := by omega
    rcases this with h5 | h5 <;> nlinarith
  have hle : w1t n d z ≤ -2 := by omega
  have hvE : EvenSite (z.1 + 1, z.2 - 1) := by
    simp only [EvenSite] at hev ⊢
    omega
  have hvt : w1t n d (z.1 + 1, z.2 - 1) = w1t n d z + (n + d) := by
    unfold w1t
    ring
  have hvs : w1s n d (z.1 + 1, z.2 - 1) = w1s n d z + 2 * n := by
    unfold w1s
    ring
  unfold freeHn
  refine ⟨?_, ?_, ?_⟩
  · rw [closedRect_iff]
    left
    refine ⟨hvE, ?_, ?_, ?_, ?_⟩
    · rw [hvt]; omega
    · rw [hvt]; omega
    · rw [hvs]; omega
    · rw [hvs]; omega
  · intro hc
    rw [closedRect_iff] at hc
    have hodd : ¬ EvenSite (z.1 + 1, z.2 - 1 - 1) := by
      simp only [EvenSite] at hev ⊢
      omega
    have hd' : w1t n d (z.1 + 1, z.2 - 1 - 1) = w1t n d (z.1 + 1, z.2 - 1) + d := by
      unfold w1t
      ring
    rcases hc with hc | hc
    · exact hodd hc.1
    · have hle' := hc.2.2.1
      rw [hd', hvt] at hle'
      omega
  · rw [hvt]
    unfold hSp
    left
    exact ⟨by omega, by omega, by omega⟩

end FLatticePaper.W1OffCollar

namespace FLatticePaper.W1OffCollar

open FLatticePaper FLatticePaper.W1

theorem t_even_of (n d : ℤ) (hno : n % 2 = 1) (hdo : d % 2 = 1) (z : Site) (hev : EvenSite z) :
    w1t n d z % 2 = 0 := by
  have := FLatticePaper.W1Exit.parity_t n d z.1 z.2 hno hdo
  unfold w1t
  simp only [EvenSite] at hev
  omega

theorem t_odd_of (n d : ℤ) (hno : n % 2 = 1) (hdo : d % 2 = 1) (z : Site) (hev : ¬ EvenSite z) :
    w1t n d z % 2 = 1 := by
  have := FLatticePaper.W1Exit.parity_t n d z.1 z.2 hno hdo
  unfold w1t
  simp only [EvenSite] at hev
  omega

/-- The identity `n · s − (d + n) · t = T · y` on the lattice. -/
theorem lattice_id (n d : ℤ) (z : Site) :
    n * w1s n d z - (d + n) * w1t n d z = w1T n d * z.2 := by
  unfold w1s w1t w1T
  ring

/-- `T` is `(2L')² − 2n²` with `L = d + n = 2L'`: `T = 2 (2L'² − n²)`. -/
theorem T_half (n d L' : ℤ) (hL : d + n = 2 * L') :
    w1T n d = 2 * (2 * L' * L' - n * n) := by
  have h : w1T n d = (d + n) ^ 2 - 2 * n ^ 2 := by
    unfold w1T
    ring
  rw [h, hL]
  ring

/-- Coprimality of `L'` and `T' = 2L'² − n²` from the coprimality of `n` and `d`. -/
theorem coprime_half (n d L' : ℤ) (hcop : IsCoprime n d) (hL : d + n = 2 * L') :
    IsCoprime L' (2 * L' * L' - n * n) := by
  have hnL : IsCoprime n (2 * L') := by
    obtain ⟨u, v, huv⟩ := hcop
    refine ⟨u - v, v, ?_⟩
    have hd : d = 2 * L' - n := by omega
    rw [hd] at huv
    linear_combination huv
  have hnL' : IsCoprime n L' := hnL.of_mul_right_right
  have hLn : IsCoprime L' n := hnL'.symm
  have hLnn : IsCoprime L' (n * n) := hLn.mul_right hLn
  have hTn : IsCoprime L' (2 * L' * L' - n * n) := by
    have e : 2 * L' * L' - n * n = -(n * n) + L' * (2 * L') := by ring
    rw [e]
    exact (hLnn.neg_right).add_mul_left_right _
  exact hTn

/-- A strict even site has `s ≠ 2L`: the lattice forces `t = 2n − T' m` with `T'` odd, and the strict range leaves `m = 1`. -/
theorem no_strict_even_s2L (n d : ℤ) (hn : 3 ≤ n) (hnd : n + 2 ≤ d) (hcop : IsCoprime n d)
    (hno : n % 2 = 1) (hdo : d % 2 = 1) (z : Site) (hev : EvenSite z) (hz : StrictInterior n d z)
    (hs : w1s n d z = 2 * (d + n)) : False := by
  rw [strict_even n d z hev] at hz
  obtain ⟨h1, h2, h3, h4⟩ := hz
  have ht := t_even_of n d hno hdo z hev
  obtain ⟨L', hL⟩ : ∃ L' : ℤ, d + n = 2 * L' := ⟨(d + n) / 2, by omega⟩
  have hT := T_half n d L' hL
  have hid := lattice_id n d z
  rw [hs, hT, hL] at hid
  have key : L' * (2 * n - w1t n d z) = (2 * L' * L' - n * n) * z.2 := by
    have h2' : (2 : ℤ) * (L' * (2 * n - w1t n d z)) = 2 * ((2 * L' * L' - n * n) * z.2) := by
      linear_combination hid
    exact mul_left_cancel₀ (two_ne_zero) h2'
  have hcL := coprime_half n d L' hcop hL
  have hdvd : (2 * L' * L' - n * n) ∣ L' * (2 * n - w1t n d z) := ⟨z.2, by linear_combination key⟩
  obtain ⟨m, hm⟩ := (hcL.symm).dvd_of_dvd_mul_left hdvd
  have hnn : (n * n) % 2 = 1 := by
    rw [Int.mul_emod, hno]
    norm_num
  have hTodd : (2 * L' * L' - n * n) % 2 = 1 := by
    have : 2 * L' * L' - n * n = 2 * (L' * L') - n * n := by ring
    rw [this]
    omega
  have hL' : n + 1 ≤ L' := by omega
  have hT0 : 0 < 2 * L' * L' - n * n := by nlinarith
  have hm1 : 1 ≤ m := by
    by_contra hc
    have hc' : m < 1 := not_le.mp hc
    nlinarith
  have hm2 : m ≤ 1 := by
    by_contra hc
    have hc' : 1 < m := not_le.mp hc
    nlinarith
  have hm1' : m = 1 := by omega
  subst hm1'
  omega

/-- A strict odd site has `s ≠ L`: the lattice forces `n − t = T' m` with `T'` odd, and the strict range leaves `m = 1`, while `n − t` is even. -/
theorem no_strict_odd_sL (n d : ℤ) (hn : 3 ≤ n) (hnd : n + 2 ≤ d) (hcop : IsCoprime n d)
    (hno : n % 2 = 1) (hdo : d % 2 = 1) (z : Site) (hod : ¬ EvenSite z) (hz : StrictInterior n d z)
    (hs : w1s n d z = d + n) : False := by
  rw [strict_odd n d z hod] at hz
  obtain ⟨h1, h2, h3, h4⟩ := hz
  have ht := t_odd_of n d hno hdo z hod
  obtain ⟨L', hL⟩ : ∃ L' : ℤ, d + n = 2 * L' := ⟨(d + n) / 2, by omega⟩
  have hT := T_half n d L' hL
  have hid := lattice_id n d z
  rw [hs, hT, hL] at hid
  have key : L' * (n - w1t n d z) = (2 * L' * L' - n * n) * z.2 := by
    have h2' : (2 : ℤ) * (L' * (n - w1t n d z)) = 2 * ((2 * L' * L' - n * n) * z.2) := by
      linear_combination hid
    exact mul_left_cancel₀ (two_ne_zero) h2'
  have hcL := coprime_half n d L' hcop hL
  have hdvd : (2 * L' * L' - n * n) ∣ L' * (n - w1t n d z) := ⟨z.2, by linear_combination key⟩
  obtain ⟨m, hm⟩ := (hcL.symm).dvd_of_dvd_mul_left hdvd
  have hnn : (n * n) % 2 = 1 := by
    rw [Int.mul_emod, hno]
    norm_num
  have hTodd : (2 * L' * L' - n * n) % 2 = 1 := by
    have : 2 * L' * L' - n * n = 2 * (L' * L') - n * n := by ring
    rw [this]
    omega
  have hL' : n + 1 ≤ L' := by omega
  have hT0 : 0 < 2 * L' * L' - n * n := by nlinarith
  have hm1 : 1 ≤ m := by
    by_contra hc
    have hc' : m < 1 := not_le.mp hc
    nlinarith
  have hm2 : m ≤ 1 := by
    by_contra hc
    have hc' : 1 < m := not_le.mp hc
    nlinarith
  have hm1' : m = 1 := by omega
  subst hm1'
  omega

end FLatticePaper.W1OffCollar
