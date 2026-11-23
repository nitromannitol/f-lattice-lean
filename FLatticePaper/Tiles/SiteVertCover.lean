import FLatticePaper.Tiles.SiteVertLink
import FLatticePaper.Tiles.SiteRot
import FLatticePaper.Tiles.SiteFwdCover

/-! Task 53, item 4 (the vertical cover): the lower vertical band is covered by the vertical string.

For a vertical word `ℓ = q :: ℓ''` with `CursorV ℓ n d` (the ceiling bounds of slope `n/d`, length `d`), the cursor error
`E_k = d·qPrefix ℓ k − n·k` lies in `[0, d)`, the letter `k` is `q` exactly when `E_k < n`, and the cursor value is determined by `E_k`.
For a site `(x, y)` of `H` in the lower vertical band the three cases are: `y − x` even (offset `(0,0)` or `(0,1)` by `s < N`); `y − x`
odd with `C ≤ s` (offset `(0,1)` on a `q`); `y − x` odd with `s < C` (offset `(0,0)` on a `p`). -/

namespace FLatticePaper.Tiles.SiteVertCover

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.SiteStrings FLatticePaper.Tiles.CeilWords
  FLatticePaper.Tiles.SiteMarksCursor FLatticePaper.Tiles.SiteFwdLink FLatticePaper.Tiles.SiteVertLink
  FLatticePaper.Tiles.SiteFwdCover

/-- The vertical cursor bounds: `d·qPrefix ℓ j − d < n·j ≤ d·qPrefix ℓ j` for `j ≤ |ℓ|`. -/
def CursorV (ℓ : BinaryWord) (n d : ℤ) : Prop :=
  ∀ j : ℕ, j ≤ ℓ.length → d * qPrefix ℓ j - d < n * (j : ℤ) ∧ n * (j : ℤ) ≤ d * qPrefix ℓ j

theorem vEps_bounds (ℓ : BinaryWord) (n d : ℤ) (hV : CursorV ℓ n d) (j : ℕ) (hj : j ≤ ℓ.length) :
    0 ≤ d * qPrefix ℓ j - n * (j : ℤ) ∧ d * qPrefix ℓ j - n * (j : ℤ) < d := by
  obtain ⟨h1, h2⟩ := hV j hj
  constructor <;> linarith

theorem vErr_step (ℓ : BinaryWord) (n d : ℤ) (k : ℕ) (hk : k < ℓ.length) :
    d * qPrefix ℓ (k + 1) - n * ((k : ℤ) + 1) =
      (d * qPrefix ℓ k - n * (k : ℤ)) + (if ℓ.getD k Letter.p = Letter.q then d else 0) - n := by
  rw [getD_eq_getElem_p ℓ k hk, qPrefix_succ ℓ k hk]
  split_ifs <;> ring

/-- **The vertical letter rule.** The letter `k` is `q` exactly when its cursor error is below `n`. -/
theorem vletter_q_iff (ℓ : BinaryWord) (n d : ℤ) (hV : CursorV ℓ n d) (k : ℕ) (hk : k < ℓ.length) :
    ℓ.getD k Letter.p = Letter.q ↔ d * qPrefix ℓ k - n * (k : ℤ) < n := by
  have hs := vErr_step ℓ n d k hk
  obtain ⟨a1, a2⟩ := vEps_bounds ℓ n d hV (k + 1) (by omega)
  obtain ⟨b1, b2⟩ := vEps_bounds ℓ n d hV k (by omega)
  push_cast at a1 a2
  constructor
  · intro hq
    rw [if_pos hq] at hs
    linarith
  · intro hlt
    by_contra hne
    rw [if_neg hne] at hs
    linarith

/-- The cursor value is determined by its error. -/
theorem qPrefix_eq_of_vErr (ℓ : BinaryWord) (n d : ℤ) (hV : CursorV ℓ n d) (hd : 0 < d) (j : ℕ) (hj : j ≤ ℓ.length)
    (B : ℤ) (h0 : 0 ≤ d * B - n * (j : ℤ)) (h1 : d * B - n * (j : ℤ) < d) :
    qPrefix ℓ j = B := by
  obtain ⟨e0, e1⟩ := vEps_bounds ℓ n d hV j hj
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have : d * qPrefix ℓ j ≤ d * (B - 1) := mul_le_mul_of_nonneg_left (by omega) hd.le
    nlinarith
  · have : d * (B + 1) ≤ d * qPrefix ℓ j := mul_le_mul_of_nonneg_left (by omega) hd.le
    nlinarith

/-- **A site of the vertical string.** The site `(x + 1, y + 1)` is a site of the vertical string of `q :: ℓ''` when the cursor
index `k` and value `B = qPrefix (q :: ℓ'') k` give the origin and the offset admissible for the error `E = dB − nk`. -/
theorem mem_of_vcursor (ℓ'' : BinaryWord) (n d : ℤ) (hV : CursorV (Letter.q :: ℓ'') n d) (k : ℕ)
    (hk : k < (Letter.q :: ℓ'').length) (B x y b1 b2 : ℤ)
    (hB : qPrefix (Letter.q :: ℓ'') k = B)
    (hqcase : d * B - n * (k : ℤ) < n → x + 1 = 1 - (k : ℤ) + B + b1 ∧ y + 1 = (k : ℤ) + (B + 1) + b2 ∧
      0 ≤ b1 ∧ b1 ≤ 1 ∧ 0 ≤ b2 ∧ b2 ≤ 1)
    (hpcase : n ≤ d * B - n * (k : ℤ) → x + 1 = 1 - (k : ℤ) + B + b1 ∧ y + 1 = (k : ℤ) + B + b2 ∧
      0 ≤ b1 ∧ b1 ≤ 1 ∧ 0 ≤ b2 ∧ b2 ≤ 2) :
    (x + 1, y + 1) ∈ stringSites true true (Letter.q :: ℓ'') := by
  rw [stringSites_vert_iff_cons]
  by_cases hq : d * B - n * (k : ℤ) < n
  · obtain ⟨e1, e2, e3, e4, e5, e6⟩ := hqcase hq
    have hletter : (Letter.q :: ℓ'').getD k Letter.p = Letter.q :=
      (vletter_q_iff (Letter.q :: ℓ'') n d hV k hk).mpr (by rw [hB]; exact hq)
    have hletter' : (Letter.q :: ℓ'')[k] = Letter.q := by
      rw [← getD_eq_getElem_p _ k hk]
      exact hletter
    have hq1 : qPrefix (Letter.q :: ℓ'') (k + 1) = B + 1 := by
      rw [qPrefix_succ _ k hk, if_pos hletter', hB]
    refine ⟨k, hk, (b1, b2), Or.inr ⟨hletter, e3, e4, e5, e6⟩, ?_⟩
    rw [hB, hq1]
    refine Prod.ext ?_ ?_
    · dsimp only
      linarith
    · dsimp only
      linarith
  · obtain ⟨e1, e2, e3, e4, e5, e6⟩ := hpcase (not_lt.mp hq)
    have hpl : (Letter.q :: ℓ'').getD k Letter.p = Letter.p := by
      cases hx : (Letter.q :: ℓ'').getD k Letter.p with
      | p => rfl
      | q =>
        exfalso
        exact hq ((vletter_q_iff (Letter.q :: ℓ'') n d hV k hk).mp hx |> fun h' => by rw [hB] at h'; exact h')
    have hpl' : (Letter.q :: ℓ'')[k] ≠ Letter.q := by
      rw [← getD_eq_getElem_p _ k hk, hpl]
      decide
    have hq1 : qPrefix (Letter.q :: ℓ'') (k + 1) = B := by
      rw [qPrefix_succ _ k hk, if_neg hpl', hB]
      ring
    refine ⟨k, hk, (b1, b2), Or.inl ⟨hpl, e3, e4, e5, e6⟩, ?_⟩
    rw [hB, hq1]
    refine Prod.ext ?_ ?_
    · dsimp only
      linarith
    · dsimp only
      linarith

/-- **The lower vertical band is covered.** A site `(x, y)` of the odd standard hull with `s ≤ N − l` has `(x + 1, y + 1)` in the
vertical string of `q :: ℓ''`. -/
theorem vband_stringSites (n d x y t s a l : ℤ) (ℓ'' : BinaryWord) (hn : 0 < n) (hnd : n < d) (hodd : (d + n) % 2 = 1)
    (hV : CursorV (Letter.q :: ℓ'') n d) (hlen : ((Letter.q :: ℓ'').length : ℤ) = d)
    (ht : t = n * x - d * y) (hs : s = (d + n) * x + (d - n) * y)
    (hsite : ((x + y) % 2 = 1 → a = n ∧ l = min (d - n) (3 * n - d)) ∧
      ((x + y) % 2 = 0 → a = min (2 * n) (d - n) ∧ l = 0))
    (hH1 : a - (d ^ 2 + 2 * d * n - n ^ 2) ≤ t) (hH2 : t ≤ d + n - a) (hH3 : l ≤ s)
    (hsband : s ≤ 2 * n - l) :
    (x + 1, y + 1) ∈ stringSites true true (Letter.q :: ℓ'') := by
  obtain ⟨hM0, hM1⟩ := SiteRot.vband_M_bounds n d x y t s a l hn hnd hodd ht hs hsite hH1 hH2 hH3 hsband
  have hd : 0 < d := by omega
  rcases (show (x + y) % 2 = 0 ∨ (x + y) % 2 = 1 by omega) with hz | hz
  · -- even site: `l = 0`, the index is `k = (y − x)/2`, the cursor value `B = y − k`
    obtain ⟨-, hl⟩ := hsite.2 hz
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = (y - x) / 2 := ⟨((y - x) / 2).toNat, Int.toNat_of_nonneg (by omega)⟩
    have hk2 : (2 * k : ℤ) = y - x := by omega
    have hx : x = y - 2 * k := by omega
    have hEs : 2 * (d * (y - k) - n * k) = s := by
      rw [hs, hx]; ring
    have hkl : k < (Letter.q :: ℓ'').length := by omega
    have hB : qPrefix (Letter.q :: ℓ'') k = y - k := by
      apply qPrefix_eq_of_vErr (Letter.q :: ℓ'') n d hV hd k (by omega) (y - k)
      · linarith [hEs, hH3, hl]
      · linarith [hEs, hsband, hl]
    by_cases hEn : d * (y - k) - n * k < n
    · exact mem_of_vcursor ℓ'' n d hV k hkl (y - k) x y 0 0 hB
        (fun _ => ⟨by omega, by omega, by norm_num, by norm_num, by norm_num, by norm_num⟩)
        (fun h => absurd hEn (not_lt.mpr h))
    · exact mem_of_vcursor ℓ'' n d hV k hkl (y - k) x y 0 1 hB
        (fun h => absurd h hEn)
        (fun _ => ⟨by omega, by omega, by norm_num, by norm_num, by norm_num, by norm_num⟩)
  · -- odd site: `a = n`, `l = min(d − n, 3n − d)`
    obtain ⟨-, hl⟩ := hsite.1 hz
    by_cases hsC : d - n ≤ s
    · -- `C ≤ s`: the index `k = (y − x − 1)/2`, the cursor value `B = y − k − 1`, and a `q` with offset `(0,1)`
      obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = (y - x - 1) / 2 := ⟨((y - x - 1) / 2).toNat, Int.toNat_of_nonneg (by omega)⟩
      have hk2 : (2 * k : ℤ) = y - x - 1 := by omega
      have hx : x = y - 2 * k - 1 := by omega
      have hEs : 2 * (d * (y - k - 1) - n * k) = s - (d - n) := by
        rw [hs, hx]; ring
      have hkl : k < (Letter.q :: ℓ'').length := by omega
      have hsC2 : s - (d - n) < 2 * d := by omega
      have hsL : s < d + n := by omega
      have hB : qPrefix (Letter.q :: ℓ'') k = y - k - 1 := by
        apply qPrefix_eq_of_vErr (Letter.q :: ℓ'') n d hV hd k (by omega) (y - k - 1)
        · linarith [hEs, hsC]
        · linarith [hEs, hsC2]
      have hElt : d * (y - k - 1) - n * k < n := by linarith [hEs, hsL]
      exact mem_of_vcursor ℓ'' n d hV k hkl (y - k - 1) x y 0 1 hB
        (fun _ => ⟨by omega, by omega, by norm_num, by norm_num, by norm_num, by norm_num⟩)
        (fun h => absurd hElt (not_lt.mpr h))
    · -- `s < C`: then `3n − d ≤ s`; the index `k = (y − x + 1)/2`, `B = y − k + 1`, and a `p` with offset `(0,0)`
      have hsC' : s < d - n := by omega
      have hs3 : 3 * n - d ≤ s := by omega
      obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = (y - x + 1) / 2 := ⟨((y - x + 1) / 2).toNat, Int.toNat_of_nonneg (by omega)⟩
      have hk2 : (2 * k : ℤ) = y - x + 1 := by omega
      have hx : x = y - 2 * k + 1 := by omega
      have hEs : 2 * (d * (y - k + 1) - n * k) = s + (d - n) := by
        rw [hs, hx]; ring
      have hkl : k < (Letter.q :: ℓ'').length := by omega
      have hB : qPrefix (Letter.q :: ℓ'') k = y - k + 1 := by
        apply qPrefix_eq_of_vErr (Letter.q :: ℓ'') n d hV hd k (by omega) (y - k + 1)
        · linarith [hEs, hs3]
        · linarith [hEs, hsC']
      exact mem_of_vcursor ℓ'' n d hV k hkl (y - k + 1) x y 0 0 hB
        (fun h => absurd h (not_lt.mpr (by linarith [hEs, hs3] : n ≤ d * (y - k + 1) - n * k)))
        (fun _ => ⟨by omega, by omega, by norm_num, by norm_num, by norm_num, by norm_num⟩)

/-- **The lower vertical band, with the index bound as a hypothesis** (the even tile uses it). A site `(x, y)` with
`s ≤ N − l` has `(x + 1, y + 1)` in the vertical string of `q :: ℓ''`. -/
theorem vband_stringSites_M (n d x y _t s a l : ℤ) (ℓ'' : BinaryWord) (hn : 0 < n) (hnd : n < d) (hM : 0 ≤ y - x ∧ y - x ≤ 2 * d - 2)
    (hV : CursorV (Letter.q :: ℓ'') n d) (hlen : ((Letter.q :: ℓ'').length : ℤ) = d)
    (hs : s = (d + n) * x + (d - n) * y)
    (hsite : ((x + y) % 2 = 1 → a = n ∧ l = min (d - n) (3 * n - d)) ∧
      ((x + y) % 2 = 0 → a = min (2 * n) (d - n) ∧ l = 0))
    (hH3 : l ≤ s)
    (hsband : s ≤ 2 * n - l) :
    (x + 1, y + 1) ∈ stringSites true true (Letter.q :: ℓ'') := by
  obtain ⟨hM0, hM1⟩ := hM
  have hd : 0 < d := by omega
  rcases (show (x + y) % 2 = 0 ∨ (x + y) % 2 = 1 by omega) with hz | hz
  · -- even site: `l = 0`, the index is `k = (y − x)/2`, the cursor value `B = y − k`
    obtain ⟨-, hl⟩ := hsite.2 hz
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = (y - x) / 2 := ⟨((y - x) / 2).toNat, Int.toNat_of_nonneg (by omega)⟩
    have hk2 : (2 * k : ℤ) = y - x := by omega
    have hx : x = y - 2 * k := by omega
    have hEs : 2 * (d * (y - k) - n * k) = s := by
      rw [hs, hx]; ring
    have hkl : k < (Letter.q :: ℓ'').length := by omega
    have hB : qPrefix (Letter.q :: ℓ'') k = y - k := by
      apply qPrefix_eq_of_vErr (Letter.q :: ℓ'') n d hV hd k (by omega) (y - k)
      · linarith [hEs, hH3, hl]
      · linarith [hEs, hsband, hl]
    by_cases hEn : d * (y - k) - n * k < n
    · exact mem_of_vcursor ℓ'' n d hV k hkl (y - k) x y 0 0 hB
        (fun _ => ⟨by omega, by omega, by norm_num, by norm_num, by norm_num, by norm_num⟩)
        (fun h => absurd hEn (not_lt.mpr h))
    · exact mem_of_vcursor ℓ'' n d hV k hkl (y - k) x y 0 1 hB
        (fun h => absurd h hEn)
        (fun _ => ⟨by omega, by omega, by norm_num, by norm_num, by norm_num, by norm_num⟩)
  · -- odd site: `a = n`, `l = min(d − n, 3n − d)`
    obtain ⟨-, hl⟩ := hsite.1 hz
    by_cases hsC : d - n ≤ s
    · -- `C ≤ s`: the index `k = (y − x − 1)/2`, the cursor value `B = y − k − 1`, and a `q` with offset `(0,1)`
      obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = (y - x - 1) / 2 := ⟨((y - x - 1) / 2).toNat, Int.toNat_of_nonneg (by omega)⟩
      have hk2 : (2 * k : ℤ) = y - x - 1 := by omega
      have hx : x = y - 2 * k - 1 := by omega
      have hEs : 2 * (d * (y - k - 1) - n * k) = s - (d - n) := by
        rw [hs, hx]; ring
      have hkl : k < (Letter.q :: ℓ'').length := by omega
      have hsC2 : s - (d - n) < 2 * d := by omega
      have hsL : s < d + n := by omega
      have hB : qPrefix (Letter.q :: ℓ'') k = y - k - 1 := by
        apply qPrefix_eq_of_vErr (Letter.q :: ℓ'') n d hV hd k (by omega) (y - k - 1)
        · linarith [hEs, hsC]
        · linarith [hEs, hsC2]
      have hElt : d * (y - k - 1) - n * k < n := by linarith [hEs, hsL]
      exact mem_of_vcursor ℓ'' n d hV k hkl (y - k - 1) x y 0 1 hB
        (fun _ => ⟨by omega, by omega, by norm_num, by norm_num, by norm_num, by norm_num⟩)
        (fun h => absurd hElt (not_lt.mpr h))
    · -- `s < C`: then `3n − d ≤ s`; the index `k = (y − x + 1)/2`, `B = y − k + 1`, and a `p` with offset `(0,0)`
      have hsC' : s < d - n := by omega
      have hs3 : 3 * n - d ≤ s := by omega
      obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = (y - x + 1) / 2 := ⟨((y - x + 1) / 2).toNat, Int.toNat_of_nonneg (by omega)⟩
      have hk2 : (2 * k : ℤ) = y - x + 1 := by omega
      have hx : x = y - 2 * k + 1 := by omega
      have hEs : 2 * (d * (y - k + 1) - n * k) = s + (d - n) := by
        rw [hs, hx]; ring
      have hkl : k < (Letter.q :: ℓ'').length := by omega
      have hB : qPrefix (Letter.q :: ℓ'') k = y - k + 1 := by
        apply qPrefix_eq_of_vErr (Letter.q :: ℓ'') n d hV hd k (by omega) (y - k + 1)
        · linarith [hEs, hs3]
        · linarith [hEs, hsC']
      exact mem_of_vcursor ℓ'' n d hV k hkl (y - k + 1) x y 0 0 hB
        (fun h => absurd h (not_lt.mpr (by linarith [hEs, hs3] : n ≤ d * (y - k + 1) - n * k)))
        (fun _ => ⟨by omega, by omega, by norm_num, by norm_num, by norm_num, by norm_num⟩)


theorem vband_stringSites_ext (n d x y _t s a l : ℤ) (ℓ'' : BinaryWord) (hn : 0 < n) (hnd : n < d) (hM : 0 ≤ y - x ∧ y - x ≤ 2 * d - 2)
    (hV : CursorV (Letter.q :: ℓ'') n d) (hlen : ((Letter.q :: ℓ'').length : ℤ) = d)
    (hs : s = (d + n) * x + (d - n) * y)
    (hsite : ((x + y) % 2 = 1 → a = n ∧ l = min (d - n) (3 * n - d)) ∧
      ((x + y) % 2 = 0 → a = min (2 * n) (d - n) ∧ l = 0))
    (hH3 : l ≤ s)
    (hsodd : (x + y) % 2 = 1 → s < d + n) (heven : (x + y) % 2 = 0 → s < 2 * d) :
    (x + 1, y + 1) ∈ stringSites true true (Letter.q :: ℓ'') := by
  obtain ⟨hM0, hM1⟩ := hM
  have hd : 0 < d := by omega
  rcases (show (x + y) % 2 = 0 ∨ (x + y) % 2 = 1 by omega) with hz | hz
  · -- even site: `l = 0`, the index is `k = (y − x)/2`, the cursor value `B = y − k`
    obtain ⟨-, hl⟩ := hsite.2 hz
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = (y - x) / 2 := ⟨((y - x) / 2).toNat, Int.toNat_of_nonneg (by omega)⟩
    have hk2 : (2 * k : ℤ) = y - x := by omega
    have hx : x = y - 2 * k := by omega
    have hEs : 2 * (d * (y - k) - n * k) = s := by
      rw [hs, hx]; ring
    have hkl : k < (Letter.q :: ℓ'').length := by omega
    have hB : qPrefix (Letter.q :: ℓ'') k = y - k := by
      apply qPrefix_eq_of_vErr (Letter.q :: ℓ'') n d hV hd k (by omega) (y - k)
      · linarith [hEs, hH3, hl]
      · linarith [hEs, heven hz, hl]
    by_cases hEn : d * (y - k) - n * k < n
    · exact mem_of_vcursor ℓ'' n d hV k hkl (y - k) x y 0 0 hB
        (fun _ => ⟨by omega, by omega, by norm_num, by norm_num, by norm_num, by norm_num⟩)
        (fun h => absurd hEn (not_lt.mpr h))
    · exact mem_of_vcursor ℓ'' n d hV k hkl (y - k) x y 0 1 hB
        (fun h => absurd h hEn)
        (fun _ => ⟨by omega, by omega, by norm_num, by norm_num, by norm_num, by norm_num⟩)
  · -- odd site: `a = n`, `l = min(d − n, 3n − d)`
    obtain ⟨-, hl⟩ := hsite.1 hz
    by_cases hsC : d - n ≤ s
    · -- `C ≤ s`: the index `k = (y − x − 1)/2`, the cursor value `B = y − k − 1`, and a `q` with offset `(0,1)`
      obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = (y - x - 1) / 2 := ⟨((y - x - 1) / 2).toNat, Int.toNat_of_nonneg (by omega)⟩
      have hk2 : (2 * k : ℤ) = y - x - 1 := by omega
      have hx : x = y - 2 * k - 1 := by omega
      have hEs : 2 * (d * (y - k - 1) - n * k) = s - (d - n) := by
        rw [hs, hx]; ring
      have hkl : k < (Letter.q :: ℓ'').length := by omega
      have hsL : s < d + n := hsodd hz
      have hsC2 : s - (d - n) < 2 * d := by omega
      have hB : qPrefix (Letter.q :: ℓ'') k = y - k - 1 := by
        apply qPrefix_eq_of_vErr (Letter.q :: ℓ'') n d hV hd k (by omega) (y - k - 1)
        · linarith [hEs, hsC]
        · linarith [hEs, hsC2]
      have hElt : d * (y - k - 1) - n * k < n := by linarith [hEs, hsL]
      exact mem_of_vcursor ℓ'' n d hV k hkl (y - k - 1) x y 0 1 hB
        (fun _ => ⟨by omega, by omega, by norm_num, by norm_num, by norm_num, by norm_num⟩)
        (fun h => absurd hElt (not_lt.mpr h))
    · -- `s < C`: then `3n − d ≤ s`; the index `k = (y − x + 1)/2`, `B = y − k + 1`, and a `p` with offset `(0,0)`
      have hsC' : s < d - n := by omega
      have hs3 : 3 * n - d ≤ s := by omega
      obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = (y - x + 1) / 2 := ⟨((y - x + 1) / 2).toNat, Int.toNat_of_nonneg (by omega)⟩
      have hk2 : (2 * k : ℤ) = y - x + 1 := by omega
      have hx : x = y - 2 * k + 1 := by omega
      have hEs : 2 * (d * (y - k + 1) - n * k) = s + (d - n) := by
        rw [hs, hx]; ring
      have hkl : k < (Letter.q :: ℓ'').length := by omega
      have hB : qPrefix (Letter.q :: ℓ'') k = y - k + 1 := by
        apply qPrefix_eq_of_vErr (Letter.q :: ℓ'') n d hV hd k (by omega) (y - k + 1)
        · linarith [hEs, hs3]
        · linarith [hEs, hsC']
      exact mem_of_vcursor ℓ'' n d hV k hkl (y - k + 1) x y 0 0 hB
        (fun h => absurd h (not_lt.mpr (by linarith [hEs, hs3] : n ≤ d * (y - k + 1) - n * k)))
        (fun _ => ⟨by omega, by omega, by norm_num, by norm_num, by norm_num, by norm_num⟩)



end FLatticePaper.Tiles.SiteVertCover
