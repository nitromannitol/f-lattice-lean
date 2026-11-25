import FLatticePaper.Plane.Induction.FreeTraceBox
import FLatticePaper.Plane.Induction.PriceInputs
import FLatticePaper.Plane.Induction.FreePolicy
import FLatticePaper.Plane.Induction.W1MSheet
import FLatticePaper.Plane.Induction.W1ZeroStrip

/-! The first offer at the prescribed H neighbour (phase one), the grade core (i).

Parent coordinates `t_p(x) = N x₁ − D x₂` for the odd parent `(N, D)` (phase one: `N d − n D = 1`, `n, d` the child grades). For a free H root
`r` with child grade `t = n r₁ − d r₂` in the H spectrum and the H box `1 ≤ r₁ ≤ d`, `0 ≤ r₂ ≤ n − 1`:
* the identities `r₁ = d t_p − D t`, `r₂ = n t_p − N t` (from `N d − n D = 1`);
* even roots: `1 − 2N ≤ t_p ≤ D + N`; odd roots: `1 ≤ t_p ≤ D + 1`.
Then the prescribed input (east at even roots, north at odd roots) has `t_p` in the zero band `[1 − D, N + 2D − 1]`. -/

namespace FLatticePaper.FirstOfferGrade

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.PriceInputs FLatticePaper.PsiCalibration FLatticePaper.W1MSheet

theorem tp_even (n d N D x1 x2 t : ℤ) (hn0 : 0 < n) (hN1 : 1 ≤ N) (hrel : N * d - n * D = 1)
    (ht : t = n * x1 - d * x2) (hx2 : 0 ≤ x2) (hx2n : x2 ≤ n - 1) (ht2 : 2 ≤ t) (htL : t ≤ d + n - 2) :
    1 - 2 * N ≤ N * x1 - D * x2 ∧ N * x1 - D * x2 ≤ D + N := by
  have e2 : x2 = n * (N * x1 - D * x2) - N * t := by rw [ht]; linear_combination (-x2) * hrel
  constructor
  · nlinarith
  · have h1 : n * (N * x1 - D * x2) ≤ n * (D + N + 1) - 2 * N := by nlinarith
    have h2 : N * x1 - D * x2 < D + N + 1 := by nlinarith
    omega

theorem tp_odd (n d N D x1 x2 t : ℤ) (hn0 : 0 < n) (hN1 : 1 ≤ N)
    (hrel : N * d - n * D = 1) (ht : t = n * x1 - d * x2) (hx2 : 0 ≤ x2) (hx2n : x2 ≤ n - 1)
    (htn : n ≤ t) (htd : t ≤ d) :
    1 ≤ N * x1 - D * x2 ∧ N * x1 - D * x2 ≤ D + 1 := by
  have e1 : x1 = d * (N * x1 - D * x2) - D * t := by rw [ht]; linear_combination (-x1) * hrel
  have e2 : x2 = n * (N * x1 - D * x2) - N * t := by rw [ht]; linear_combination (-x2) * hrel
  constructor
  · nlinarith
  · nlinarith

/-- **The zero-band window of the prescribed H neighbour (phase one, frame level).** For a free H root `r`, the input
`r + prescribedH η r` has parent grade in `[1 − D, N + 2D − 1]`. -/
theorem neighbour_window_W1 (frame : ChildFrame)
    (hrel : frame.parents.odd.num * frame.child.den - frame.child.num * frame.parents.odd.den = 1)
    (hN1 : 1 ≤ frame.parents.odd.num) (hND : frame.parents.odd.num < frame.parents.odd.den)
    {r : Site} (hr : r ∈ frame.freeH) {η : ℤ} (hη : η = 1 ∨ η = -1) :
    1 - frame.parents.odd.den ≤ frame.parents.odd.num * (r + frame.prescribedH η r).1 - frame.parents.odd.den * (r + frame.prescribedH η r).2 ∧
      frame.parents.odd.num * (r + frame.prescribedH η r).1 - frame.parents.odd.den * (r + frame.prescribedH η r).2 ≤
        frame.parents.odd.num + 2 * frame.parents.odd.den - 1 := by
  obtain ⟨hn0, -, -, -, -⟩ := frame.child_facts
  obtain ⟨hco1, hco2⟩ := frame.child_odd
  obtain ⟨hb1, hb2, hb3, hb4⟩ := FLatticePaper.Induction.FreeTraceBox.freeH_box frame hr
  have hsp := hr.2.2
  unfold ChildFrame.hSpectrum at hsp
  unfold ChildFrame.tGrade at hsp
  obtain ⟨t, ht⟩ : ∃ t, t = frame.child.num * r.1 - frame.child.den * r.2 := ⟨_, rfl⟩
  rw [← ht] at hsp
  have hpar : t % 2 = (r.1 + r.2) % 2 := by
    rw [ht, Int.sub_emod, Int.mul_emod, Int.mul_emod frame.child.den, hco1, hco2]
    omega
  by_cases h1 : r = hFirst
  · subst h1
    rw [ChildFrame.prescribedH_hFirst]
    rcases hη with rfl | rfl
    · have e : hFirst + (0, -1) = ((1 : ℤ), (-1 : ℤ)) := by ext <;> simp [hFirst]
      rw [e]
      constructor <;> norm_num <;> omega
    · have e : hFirst + (0, -(-1)) = ((1 : ℤ), (1 : ℤ)) := by ext <;> simp [hFirst]
      rw [e]
      constructor <;> norm_num <;> omega
  · by_cases he : EvenSite r
    · unfold EvenSite at he
      rw [FLatticePaper.FreePolicy.pH_even frame η he]
      have hT := FLatticePaper.FirstOfferGrade.tp_even frame.child.num frame.child.den frame.parents.odd.num
        frame.parents.odd.den r.1 r.2 t hn0 hN1 hrel ht hb3 hb4
        (by rcases hsp with ⟨he', h2, h3⟩ | ⟨ho', h2, h3⟩ <;> omega) (by rcases hsp with ⟨he', h2, h3⟩ | ⟨ho', h2, h3⟩ <;> omega)
      have hsh : frame.parents.odd.num * (r + (1, 0)).1 - frame.parents.odd.den * (r + (1, 0)).2 =
          (frame.parents.odd.num * r.1 - frame.parents.odd.den * r.2) + frame.parents.odd.num := by
        simp only [Prod.fst_add, Prod.snd_add]
        ring
      rw [hsh]
      constructor <;> linarith [hT.1, hT.2]
    · unfold EvenSite at he
      rw [FLatticePaper.FreePolicy.pH_odd' frame η he h1]
      have hT := FLatticePaper.FirstOfferGrade.tp_odd frame.child.num frame.child.den frame.parents.odd.num
        frame.parents.odd.den r.1 r.2 t hn0 hN1 hrel ht hb3 hb4
        (by rcases hsp with ⟨he', h2, h3⟩ | ⟨ho', h2, h3⟩ <;> omega) (by rcases hsp with ⟨he', h2, h3⟩ | ⟨ho', h2, h3⟩ <;> omega)
      have hsh : frame.parents.odd.num * (r + (0, 1)).1 - frame.parents.odd.den * (r + (0, 1)).2 =
          (frame.parents.odd.num * r.1 - frame.parents.odd.den * r.2) - frame.parents.odd.den := by
        simp only [Prod.fst_add, Prod.snd_add]
        ring
      rw [hsh]
      constructor <;> linarith [hT.1, hT.2]

/-- **(i), phase one, at the prescribed neighbour.** The first offer vanishes at `r + prescribedH η r` for every free H root `r` of the word. -/
theorem first_offer_neighbour_W1 {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hW1 : (frameAt word).eps = 1) {r : Site} (hr : r ∈ (frameAt word).freeH) {η : ℤ} (hη : η = 1 ∨ η = -1) :
    (frameAt word).sheetA (FqW word) (r + (frameAt word).prescribedH η r) = 0 := by
  obtain ⟨hN1, hND, hD2, hnq, hdq, hn_eq, hd_eq, heps, -⟩ := pdata h
  have hrel : (frameAt word).parents.odd.num * (frameAt word).child.den - (frameAt word).child.num *
      (frameAt word).parents.odd.den = 1 := by
    rw [hd_eq, hn_eq]
    rw [hW1] at heps
    linear_combination (-1 : ℤ) * heps
  obtain ⟨hcn, hcd⟩ := frameAt_conj_num_den h
  have e1 : ((frameAt (conjWord word)).child.den + (frameAt (conjWord word)).child.num) / 2 =
      (frameAt word).parents.odd.den := by
    rw [hcn, hcd]
    omega
  have e2 : ((frameAt (conjWord word)).child.den - (frameAt (conjWord word)).child.num) / 2 =
      (frameAt word).parents.odd.num := by
    rw [hcn, hcd]
    omega
  have hwin := neighbour_window_W1 (frameAt word) hrel hN1 hND hr hη
  unfold ChildFrame.sheetA FqW
  rw [sheetShift_W1 word hW1, sub_zero]
  exact W1ZeroStrip.zeroStrip_of_strips (frameAt (conjWord word)) hSE.packet.strips _
    (by rw [e1, e2]; exact hwin.1) (by rw [e1, e2]; exact hwin.2)

/-! ### Phase zero (`N d − n D = −1`) -/

theorem tp_even_W0 (n d N D x1 x2 t : ℤ) (hn0 : 0 < n) (hN1 : 1 ≤ N) (hrel : N * d - n * D = -1)
    (ht : t = n * x1 - d * x2) (hx2 : 0 ≤ x2) (hx2n : x2 ≤ n - 1) (ht2 : 2 ≤ t) (htL : t ≤ d + n - 2) :
    0 ≤ N * x1 - D * x2 ∧ N * x1 - D * x2 ≤ D + N - 1 := by
  have e2 : x2 = N * t - n * (N * x1 - D * x2) := by rw [ht]; linear_combination x2 * hrel
  constructor
  · nlinarith
  · nlinarith

theorem tp_odd_W0 (n d N D x1 x2 t : ℤ) (hn0 : 0 < n) (hN1 : 1 ≤ N)
    (hrel : N * d - n * D = -1) (ht : t = n * x1 - d * x2) (hx2 : 0 ≤ x2) (hx2n : x2 ≤ n - 1)
    (htn : n ≤ t) (htd : t ≤ d) :
    1 ≤ N * x1 - D * x2 ∧ N * x1 - D * x2 ≤ D - 1 := by
  have e1 : x1 = D * t - d * (N * x1 - D * x2) := by rw [ht]; linear_combination x1 * hrel
  have e2 : x2 = N * t - n * (N * x1 - D * x2) := by rw [ht]; linear_combination x2 * hrel
  constructor
  · nlinarith
  · nlinarith

/-- **The zero-band window of the prescribed H neighbour (phase zero, frame level).** `−D ≤ t_p(input) ≤ N + 2D − 2`, the shifted form. -/
theorem neighbour_window_W0 (frame : ChildFrame)
    (hrel : frame.parents.odd.num * frame.child.den - frame.child.num * frame.parents.odd.den = -1)
    (hN1 : 1 ≤ frame.parents.odd.num) (hND : frame.parents.odd.num < frame.parents.odd.den)
    (hD : 2 ≤ frame.parents.odd.den)
    {r : Site} (hr : r ∈ frame.freeH) {η : ℤ} (hη : η = 1 ∨ η = -1) :
    -frame.parents.odd.den ≤ frame.parents.odd.num * (r + frame.prescribedH η r).1 - frame.parents.odd.den * (r + frame.prescribedH η r).2 ∧
      frame.parents.odd.num * (r + frame.prescribedH η r).1 - frame.parents.odd.den * (r + frame.prescribedH η r).2 ≤
        frame.parents.odd.num + 2 * frame.parents.odd.den - 2 := by
  obtain ⟨hn0, -, -, -, -⟩ := frame.child_facts
  obtain ⟨hco1, hco2⟩ := frame.child_odd
  obtain ⟨hb1, hb2, hb3, hb4⟩ := FLatticePaper.Induction.FreeTraceBox.freeH_box frame hr
  have hsp := hr.2.2
  unfold ChildFrame.hSpectrum at hsp
  unfold ChildFrame.tGrade at hsp
  obtain ⟨t, ht⟩ : ∃ t, t = frame.child.num * r.1 - frame.child.den * r.2 := ⟨_, rfl⟩
  rw [← ht] at hsp
  have hpar : t % 2 = (r.1 + r.2) % 2 := by
    rw [ht, Int.sub_emod, Int.mul_emod, Int.mul_emod frame.child.den, hco1, hco2]
    omega
  by_cases h1 : r = hFirst
  · subst h1
    rw [ChildFrame.prescribedH_hFirst]
    rcases hη with rfl | rfl
    · have e : hFirst + (0, -1) = ((1 : ℤ), (-1 : ℤ)) := by ext <;> simp [hFirst]
      rw [e]
      constructor <;> norm_num <;> omega
    · have e : hFirst + (0, -(-1)) = ((1 : ℤ), (1 : ℤ)) := by ext <;> simp [hFirst]
      rw [e]
      constructor <;> norm_num <;> omega
  · by_cases he : EvenSite r
    · unfold EvenSite at he
      rw [FLatticePaper.FreePolicy.pH_even frame η he]
      have hT := tp_even_W0 frame.child.num frame.child.den frame.parents.odd.num
        frame.parents.odd.den r.1 r.2 t hn0 hN1 hrel ht hb3 hb4
        (by rcases hsp with ⟨he', h2, h3⟩ | ⟨ho', h2, h3⟩ <;> omega) (by rcases hsp with ⟨he', h2, h3⟩ | ⟨ho', h2, h3⟩ <;> omega)
      have hsh : frame.parents.odd.num * (r + (1, 0)).1 - frame.parents.odd.den * (r + (1, 0)).2 =
          (frame.parents.odd.num * r.1 - frame.parents.odd.den * r.2) + frame.parents.odd.num := by
        simp only [Prod.fst_add, Prod.snd_add]
        ring
      rw [hsh]
      constructor <;> linarith [hT.1, hT.2]
    · unfold EvenSite at he
      rw [FLatticePaper.FreePolicy.pH_odd' frame η he h1]
      have hT := tp_odd_W0 frame.child.num frame.child.den frame.parents.odd.num
        frame.parents.odd.den r.1 r.2 t hn0 hN1 hrel ht hb3 hb4
        (by rcases hsp with ⟨he', h2, h3⟩ | ⟨ho', h2, h3⟩ <;> omega) (by rcases hsp with ⟨he', h2, h3⟩ | ⟨ho', h2, h3⟩ <;> omega)
      have hsh : frame.parents.odd.num * (r + (0, 1)).1 - frame.parents.odd.den * (r + (0, 1)).2 =
          (frame.parents.odd.num * r.1 - frame.parents.odd.den * r.2) - frame.parents.odd.den := by
        simp only [Prod.fst_add, Prod.snd_add]
        ring
      rw [hsh]
      constructor <;> linarith [hT.1, hT.2]

/-- **(i), phase zero, at the prescribed neighbour.** The first offer vanishes at `r + prescribedH η r` (phase zero, shifted by `l_v`). -/
theorem first_offer_neighbour_W0 {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hW0 : (frameAt word).eps = -1) {r : Site} (hr : r ∈ (frameAt word).freeH) {η : ℤ} (hη : η = 1 ∨ η = -1) :
    (frameAt word).sheetA (FqW word) (r + (frameAt word).prescribedH η r) = 0 := by
  obtain ⟨hN1, hND, hD2, hnq, hdq, hn_eq, hd_eq, heps, -⟩ := pdata h
  have hrel : (frameAt word).parents.odd.num * (frameAt word).child.den - (frameAt word).child.num *
      (frameAt word).parents.odd.den = -1 := by
    rw [hd_eq, hn_eq]
    rw [hW0] at heps
    linear_combination (-1 : ℤ) * heps
  obtain ⟨hcn, hcd⟩ := frameAt_conj_num_den h
  have e1 : ((frameAt (conjWord word)).child.den + (frameAt (conjWord word)).child.num) / 2 =
      (frameAt word).parents.odd.den := by
    rw [hcn, hcd]
    omega
  have e2 : ((frameAt (conjWord word)).child.den - (frameAt (conjWord word)).child.num) / 2 =
      (frameAt word).parents.odd.num := by
    rw [hcn, hcd]
    omega
  have hwin := neighbour_window_W0 (frameAt word) hrel hN1 hND hD2 hr hη
  unfold ChildFrame.sheetA FqW
  rw [sheetShift_W0 word hW0]
  have hlv : (frameAt word).parents.odd.num * (frameAt word).parents.even.den -
      (frameAt word).parents.odd.den * (frameAt word).parents.even.num = -1 := by
    rw [hd_eq, hn_eq] at hrel
    linear_combination hrel
  exact W1ZeroStrip.zeroStrip_of_strips (frameAt (conjWord word)) hSE.packet.strips
    (r + (frameAt word).prescribedH η r - ((frameAt word).parents.even.den, (frameAt word).parents.even.num))
    (by rw [e1, e2]; simp only [Prod.fst_sub, Prod.snd_sub]; linarith [hwin.1, hlv])
    (by rw [e1, e2]; simp only [Prod.fst_sub, Prod.snd_sub]; linarith [hwin.2, hlv])

end FLatticePaper.FirstOfferGrade
