import FLatticePaper.Plane.Induction.CapRecursion
import FLatticePaper.Plane.Induction.CapConeGrades
import FLatticePaper.Plane.Induction.ConeRoot

/-! # The cap with a base at k = 2 (the a = 0 variants of the cap lemmas)

For the rotated fan at apex `(1,0)` (`a = 0`), the cap is available from `k = 2` on, not from the anchors at `k = 0, 1`. The induction of
`QuadraticCap.cap_induction` starts at `k = 2`: its step at `k = n + 2` uses the value at `n + 1` and the bound `B n` with `n ≥ 1`. -/

namespace FLatticePaper.CapZero

open FLatticePaper FLatticePaper.QuadraticCap FLatticePaper.Induction FLatticePaper.CapConeGrades FLatticePaper.CapRay
  FLatticePaper.FanPropagation

/-- **The cap from the base `A 2`.** -/
theorem cap_induction_from2 (A B : ℕ → ℤ) (J : ℕ) (hA2 : capMin 2 ≤ A 2)
    (hB : ∀ j : ℕ, 1 ≤ j → j ≤ J → B j ≤ capMin j)
    (hrec : ∀ k : ℕ, 3 ≤ k → k ≤ J + 2 → 2 * A (k - 1) - 1 - B (k - 2) ≤ A k) :
    ∀ k : ℕ, 2 ≤ k → k ≤ J + 2 → capMin k ≤ A k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk2 hk
    by_cases h2 : k = 2
    · subst h2
      exact hA2
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = n + 2 := ⟨k - 2, by omega⟩
      have hn1 : 1 ≤ n := by omega
      have hprev : capMin ((n + 1 : ℕ) : ℤ) ≤ A (n + 1) := ih (n + 1) (by omega) (by omega) (by omega)
      have hBn : B n ≤ capMin (n : ℤ) := hB n hn1 (by omega)
      have hr := hrec (n + 2) (by omega) hk
      have hsub1 : n + 2 - 1 = n + 1 := by omega
      have hsub2 : n + 2 - 2 = n := by omega
      rw [hsub1, hsub2] at hr
      have hcap := capMin_rec ((n : ℤ) + 2)
      have e1 : (n : ℤ) + 2 - 1 = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
      have e2 : (n : ℤ) + 2 - 2 = (n : ℤ) := by ring
      rw [e1, e2] at hcap
      have e3 : ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 := by push_cast; ring
      rw [e3]
      nlinarith [hcap, hr, hprev, hBn]


/-- **The diagonal cap at apex `(1,0)` (`a = 0`).** The diagonal values `F(p+k, q+k)` satisfy the cap from `k = 2` on, from the
base `capMin 2 ≤ F(p+2, q+2)` (the NLCap odd value, not the cap at `0, 1`), the recursion `CapRecursion.diag_hrec`, and the lower bound
`hB` on the bottom row for `j ≥ 1`; beyond `J + 2` the cap is the anchor `hanchor`. -/
theorem diag_cap_zero (F : Field) (p q : ℤ) (hpq : (p + q) % 2 = 1)
    (hbin : ∀ x : Site, laplacian F x = -1 ∨ laplacian F x = 0)
    (J K : ℕ)
    (hmono : ∀ n : ℕ, n ≤ J → F (p + (n : ℤ), q + ((n : ℤ) + 2)) ≤ F (p + ((n : ℤ) + 2), q + ((n : ℤ) + 2)))
    (hA2 : capMin 2 ≤ F (p + 2, q + 2))
    (hB : ∀ j : ℕ, 1 ≤ j → j ≤ J → F (p + (j : ℤ) + 1, q + (j : ℤ)) ≤ capMin j)
    (hanchor : ∀ k : ℕ, J + 2 < k → k ≤ K → capMin k ≤ F (p + (k : ℤ), q + (k : ℤ))) :
    ∀ k : ℕ, 2 ≤ k → k ≤ K → capMin k ≤ F (p + (k : ℤ), q + (k : ℤ)) := by
  have hA2' : capMin 2 ≤ F (p + ((2 : ℕ) : ℤ), q + ((2 : ℕ) : ℤ)) := by
    simpa using hA2
  have key := cap_induction_from2 (fun k : ℕ => F (p + (k : ℤ), q + (k : ℤ)))
    (fun j : ℕ => F (p + (j : ℤ) + 1, q + (j : ℤ))) J hA2' hB
    (fun k hk3 hkJ => FLatticePaper.CapRecursion.diag_hrec F p q hpq hbin J hmono k (by omega) hkJ)
  intro k hk2 hkK
  by_cases h : k ≤ J + 2
  · exact key k hk2 h
  · exact hanchor k (by omega) hkK

theorem odd_halo_zero {N D a : ℤ} {F : Field} (H : NLCap N D F) (hND : N < D)
    {p q : ℤ} (hs : N * p - D * q = a - N) (hpq : (p + q) % 2 = 1)
    (K : ℕ) (hcap : ∀ k : ℕ, 2 ≤ k → k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ F (p + (k : ℤ), q + (k : ℤ)))
    (k : ℕ) (hk2 : 2 ≤ k) (hk : k ≤ K) (z : Site) (hz : ¬ EvenSite z)
    (hlo : a - N - (k : ℤ) * (D - N) ≤ N * z.1 - D * z.2)
    (hup : N * z.1 - D * z.2 ≤ N + 2 * D - 1) :
    FLatticePaper.QuadraticCap.capMin k ≤ F z := by
  have hr : ¬ EvenSite (p + (k : ℤ), q + (k : ℤ)) := by
    unfold EvenSite
    simp only
    omega
  have hrt : N * (p + (k : ℤ)) - D * (q + (k : ℤ)) = a - N - (k : ℤ) * (D - N) := by
    linear_combination hs
  have hcapk := hcap k hk2 hk
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

theorem even_ray_lower_zero {N D a : ℤ} {F : Field} (H : NLCap N D F) (hN0 : 0 < N) (hND : N < D) (ha2 : a ≤ 2)
    {p q : ℤ} (hs : N * p - D * q = a - N) (hpq : (p + q) % 2 = 1)
    (K : ℕ) (hcap : ∀ k : ℕ, 2 ≤ k → k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ F (p + (k : ℤ), q + (k : ℤ)))
    (k : ℕ) (hk2 : 2 ≤ k) (hk : k ≤ K) :
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
  have hW := hcap k hk2 hk
  have hzo : ¬ EvenSite (p + (k : ℤ) + 2, q + (k : ℤ)) := by
    unfold EvenSite
    simp only
    omega
  have hrtE : N * (p + (k : ℤ) + 2) - D * (q + (k : ℤ)) = a + N - (k : ℤ) * (D - N) := by
    linear_combination hs
  have hE := odd_halo_zero H hND hs hpq K hcap k hk2 hk (p + (k : ℤ) + 2, q + (k : ℤ)) hzo
    (by dsimp only; linarith [hrtE, hN0])
    (by dsimp only; nlinarith [hrtE, kC_nonneg_NL hND k, hN0])
  rcases hb with h | h <;> linarith

theorem even_halo_zero {N D a : ℤ} {F : Field} (H : NLCap N D F) (hN0 : 0 < N) (hND : N < D) (ha2 : a ≤ 2)
    {p q : ℤ} (hs : N * p - D * q = a - N) (hpq : (p + q) % 2 = 1)
    (K : ℕ) (hcap : ∀ k : ℕ, 2 ≤ k → k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ F (p + (k : ℤ), q + (k : ℤ)))
    (k : ℕ) (hk2 : 2 ≤ k) (hk : k ≤ K) (z : Site) (hz : EvenSite z)
    (hlo : a - (k : ℤ) * (D - N) ≤ N * z.1 - D * z.2)
    (hup : N * z.1 - D * z.2 ≤ N + 2 * D - 1) :
    FLatticePaper.QuadraticCap.capMin k ≤ F z := by
  have hr : EvenSite (p + (k : ℤ) + 1, q + (k : ℤ)) := by
    unfold EvenSite
    simp only
    omega
  have hrt : N * (p + (k : ℤ) + 1) - D * (q + (k : ℤ)) = a - (k : ℤ) * (D - N) := by
    linear_combination hs
  have hR := even_ray_lower_zero H hN0 hND ha2 hs hpq K hcap k hk2 hk
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


/-- **The cone input at apex `(1,0)`, `a = 0`.** Rows `0` and `1` are forced to `0` by `NLCap.zero` (the input has `i₁ ≥ 1`, `i₂ ≤ 1`);
rows `k ≥ 2` are the halos with the cap for `2 ≤ k ≤ K`. -/
theorem cone_input_zero {N D a : ℤ} {F : Field} (H : NLCap N D F) (hN0 : 0 < N) (hND : N < D) (ha0 : a = 0)
    {p q : ℤ} (hs : N * p - D * q = a - N) (hpq : (p + q) % 2 = 1)
    (K : ℕ) (hcap : ∀ k : ℕ, 2 ≤ k → k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ F (p + (k : ℤ), q + (k : ℤ)))
    (i : Site) (hI : InCone (1, 0) K i) (hi1 : 1 ≤ i.1)
    (hup : N * i.1 - D * i.2 ≤ N + 2 * D - 1) :
    FLatticePaper.QuadraticCap.capMin (i.2 - (1, 0).2) ≤ F i := by
  obtain ⟨hk0, hkK, hev, hodd⟩ := hI
  dsimp only at hk0 hkK hev hodd ⊢
  by_cases hsmall : i.2 ≤ 1
  · have h01 : i.2 = 0 ∨ i.2 = 1 := by omega
    have hlow : 1 - D ≤ N * i.1 - D * i.2 := by
      rcases h01 with h | h
      · rw [h]
        nlinarith
      · rw [h]
        nlinarith
    rw [H.zero i hlow hup]
    rcases h01 with h | h
    · rw [h]
      simp [FLatticePaper.QuadraticCap.capMin_zero]
    · rw [h]
      simp [FLatticePaper.QuadraticCap.capMin_one]
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = i.2 - 0 := ⟨i.2.toNat, by omega⟩
    have hk2 : 2 ≤ k := by omega
    have hkK' : k ≤ K := by omega
    have hi2 : i.2 = (k : ℤ) := by omega
    rw [← hk]
    by_cases hz : EvenSite i
    · have hl := hev hz
      have hm : (k : ℤ) - 1 ≤ i.1 - 1 := by omega
      have hmul : N * ((k : ℤ) - 1) ≤ N * (i.1 - 1) := mul_le_mul_of_nonneg_left hm (by linarith)
      have hlo : a - (k : ℤ) * (D - N) ≤ N * i.1 - D * i.2 := by
        have : N * ((k : ℤ) - 1) = N * (k : ℤ) - N := by ring
        rw [hi2]
        nlinarith
      exact even_halo_zero H hN0 hND (by linarith) hs hpq K hcap k hk2 hkK' i hz hlo hup
    · have hl := hodd hz
      have hm : (k : ℤ) - 2 ≤ i.1 - 1 := by omega
      have hmul : N * ((k : ℤ) - 2) ≤ N * (i.1 - 1) := mul_le_mul_of_nonneg_left hm (by linarith)
      have hlo : a - N - (k : ℤ) * (D - N) ≤ N * i.1 - D * i.2 := by
        have : N * ((k : ℤ) - 2) = N * (k : ℤ) - 2 * N := by ring
        rw [hi2]
        nlinarith
      exact odd_halo_zero H hND hs hpq K hcap k hk2 hkK' i hz hlo hup

/-- **The cone window at apex `(1,0)`, `a = 0`.** On the sites `x` with `ropenNL`, the cone root condition and `x₁ ≥ 2`, the fan
satisfies `capMin(i₂) ≤ F i` at every input `i`. -/
theorem cone_window_zero {N D a : ℤ} {F : Field} (H : NLCap N D F) (T : ℤ) (hN0 : 0 < N) (hND : N < D) (ha0 : a = 0)
    {p q : ℤ} (hs : N * p - D * q = a - N) (hpq : (p + q) % 2 = 1)
    (K : ℕ) (hcap : ∀ k : ℕ, 2 ≤ k → k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ F (p + (k : ℤ), q + (k : ℤ))) :
    WindowOn (fun x => ropenNL N D T x ∧ ConeRoot (1, 0) K x ∧ 2 ≤ x.1) F
      (fun i => FLatticePaper.QuadraticCap.capMin (i.2 - (1, 0).2)) := by
  intro x hx i hi
  obtain ⟨hopen, hR, h2⟩ := hx
  have hI := cone_input_of_root_NL (1, 0) K x hR i hi
  have hup := input_bound_NL hN0 hND x hopen i hi
  have hi1 : 1 ≤ i.1 := by
    rcases hi with rfl | rfl
    · unfold incomingNeg
      split_ifs <;> simp <;> omega
    · unfold incomingPos
      split_ifs <;> simp <;> omega
  exact cone_input_zero H hN0 hND ha0 hs hpq K hcap i hI hi1 hup


/-- **The lower arc at apex `(1,0)`, `a = 0`.** An even site on the bottom row of the cone, with `w₁ ≥ b₁ + 1` (the south step of an
odd point with `x₁ ≥ 2`), is not in the open rectangle: its grade is at least `2N ≥ 2`. -/
theorem lower_arc_zero {N D a T : ℤ} (hN1 : 1 ≤ N) (ha0 : a = 0) (b : Site)
    (hb : N + a ≤ N * b.1 - D * b.2) (w : Site) (hz : EvenSite w) (hh : w.2 = b.2) (hl : b.1 + 1 ≤ w.1) :
    ¬ ropenNL N D T w := by
  intro ho
  unfold ropenNL at ho
  rw [if_pos hz] at ho
  obtain ⟨-, h2, -, -⟩ := ho
  have htw : N * w.1 - D * w.2 = (N * b.1 - D * b.2) + N * (w.1 - b.1) := by
    rw [hh]
    ring
  have hm : N ≤ N * (w.1 - b.1) := by nlinarith
  linarith

theorem even_ray_strict_zero {N D a : ℤ} {F : Field} (H : NLCap N D F) (hN0 : 0 < N) (hND : N < D) (ha2 : a ≤ 2)
    {p q : ℤ} (hs : N * p - D * q = a - N) (hpq : (p + q) % 2 = 1)
    (K : ℕ) (hK2 : 2 ≤ K)
    (hKs : 4 * N + 2 * D - a ≤ 2 * N * (K : ℤ))
    (hKr : 2 * N * (K : ℤ) ≤ 3 * D + 5 * N - 1)
    (hcap : ∀ k : ℕ, 2 ≤ k → k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ F (p + (k : ℤ), q + (k : ℤ))) :
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
  have hE := odd_halo_zero H hND hs hpq K hcap K hK2 le_rfl (p + (K : ℤ) + 2, q + (K : ℤ)) hzo
    (by dsimp only; linarith [hrtE, hN0])
    (by dsimp only; nlinarith [hrtE, kC_nonneg_NL hND K, hN0, hND])
  have h2 := capMin_pred_sub_NL (K : ℤ)
  rcases hb with h | h <;> linarith

theorem cone_strict_top_zero {N D a : ℤ} {F : Field} (H : NLCap N D F) (hN0 : 0 < N) (hND : N < D) (ha2 : a ≤ 2)
    {p q : ℤ} (hs : N * p - D * q = a - N) (hpq : (p + q) % 2 = 1)
    (K : ℕ) (hK2 : 2 ≤ K)
    (hKs : 4 * N + 2 * D - a ≤ 2 * N * (K : ℤ))
    (hKr : 2 * N * (K : ℤ) ≤ 3 * D + 5 * N - 1)
    (hcap : ∀ k : ℕ, 2 ≤ k → k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ F (p + (k : ℤ), q + (k : ℤ)))
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
    have hc := even_ray_strict_zero H hN0 hND ha2 hs hpq K hK2 hKs hKr hcap
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

theorem fan_next_zero {N D a T : ℤ} {F : Field} (H : NLCap N D F) (hN0 : 0 < N) (hND : N < D) (ha0 : a = 0) (ha2 : a ≤ 2)
    {p q : ℤ} (hs : N * p - D * q = a - N) (hpq : (p + q) % 2 = 1)
    (K : ℕ) (hK2 : 2 ≤ K)
    (hKs : 4 * N + 2 * D - a ≤ 2 * N * (K : ℤ))
    (hKr : 2 * N * (K : ℤ) ≤ 3 * D + 5 * N - 1)
    (hcap : ∀ k : ℕ, 2 ≤ k → k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ F (p + (k : ℤ), q + (k : ℤ)))
    (b : Site) (hb : N + a ≤ N * b.1 - D * b.2) (x w : Site)
    (hx : ropenNL N D T x ∧ ConeRoot b K x) (hx1 : 2 ≤ x.1) (hb1 : b.1 = 1) (hb2 : b.2 = 0)
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
        exact lower_arc_zero (by linarith) ha0 b hb (x.1, x.2 - 1) (by unfold EvenSite; dsimp only; omega)
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
        have hlt := cone_strict_top_zero H hN0 hND ha2 hs hpq K hK2 hKs hKr hcap b hb (x.1, x.2 + 1)
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

end FLatticePaper.CapZero
