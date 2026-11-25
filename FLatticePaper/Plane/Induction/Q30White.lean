import FLatticePaper.Plane.Induction.GameFort

/-! # Whiteness of the V-route middles (Q30, READING (a))

The harmonic grid `harmonicGrid` is harmonic (`ChildFrame.harmonicGrid_harmonic`). A field `F` that agrees with `harmonicGrid` at a site
and at its two inputs has zero Laplacian there, so such a site is white. The strips give agreement with `harmonicGrid` in the two grade
rows of Q30:

* the ordinary strip `hstrip`: `F = harmonicGrid` on the grades `[2 − 2d, 2L − 2]` (all parities), `L = d + n`;
* the odd extension `hodd`: `F = harmonicGrid` on odd sites with grades `[2 − 3d + n, 3d + n − 2]`.

An even centre with grade in `[2 − 2d + 2n, 2d − 2]` has its horizontal inputs (odd, grade `± L`) in `hodd`; an odd centre with grade in
`[2 − L, d + 3n − 2]` has its vertical inputs (even, grade `± c`, `c = d − n`) in `hstrip`. The two corollaries discharge `hu_white`,
`hm_white` of `GameFort.game_NW` and `GameFort.game_WNE`. The strip facts are hypotheses here; their derivation from the standard field
is the remaining wiring. -/

namespace FLatticePaper.Q30White

open FLatticePaper FLatticePaper.Induction FLatticePaper.GameFort Farey

/-- Agreement with the harmonic grid at a site and its two inputs makes its Laplacian zero. -/
theorem laplacian_eq_zero_of_agree {F : Field} {c : Site}
    (h0 : F c = harmonicGrid c) (h1 : F (incomingNeg c) = harmonicGrid (incomingNeg c))
    (h2 : F (incomingPos c) = harmonicGrid (incomingPos c)) : laplacian F c = 0 := by
  have hh := harmonicGrid_harmonic c
  unfold laplacian at hh ⊢
  rw [h0, h1, h2]
  exact hh

theorem sGrade_neg_even (frame : ChildFrame) {c : Site} (hc : EvenSite c) :
    frame.sGrade (incomingNeg c) = frame.sGrade c - (frame.child.den + frame.child.num) := by
  unfold incomingNeg ChildFrame.sGrade
  rw [if_pos hc]
  dsimp only
  ring

theorem sGrade_pos_even (frame : ChildFrame) {c : Site} (hc : EvenSite c) :
    frame.sGrade (incomingPos c) = frame.sGrade c + (frame.child.den + frame.child.num) := by
  unfold incomingPos ChildFrame.sGrade
  rw [if_pos hc]
  dsimp only
  ring

theorem sGrade_neg_odd (frame : ChildFrame) {c : Site} (hc : ¬ EvenSite c) :
    frame.sGrade (incomingNeg c) = frame.sGrade c - (frame.child.den - frame.child.num) := by
  unfold incomingNeg ChildFrame.sGrade
  rw [if_neg hc]
  dsimp only
  ring

theorem sGrade_pos_odd (frame : ChildFrame) {c : Site} (hc : ¬ EvenSite c) :
    frame.sGrade (incomingPos c) = frame.sGrade c + (frame.child.den - frame.child.num) := by
  unfold incomingPos ChildFrame.sGrade
  rw [if_neg hc]
  dsimp only
  ring

theorem not_even_incomingNeg_of_even {c : Site} (hc : EvenSite c) : ¬ EvenSite (incomingNeg c) := by
  unfold incomingNeg
  rw [if_pos hc]
  unfold EvenSite at hc ⊢
  dsimp only at hc ⊢
  omega

theorem not_even_incomingPos_of_even {c : Site} (hc : EvenSite c) : ¬ EvenSite (incomingPos c) := by
  unfold incomingPos
  rw [if_pos hc]
  unfold EvenSite at hc ⊢
  dsimp only at hc ⊢
  omega

theorem even_incomingNeg_of_odd {c : Site} (hc : ¬ EvenSite c) : EvenSite (incomingNeg c) := by
  unfold incomingNeg
  rw [if_neg hc]
  unfold EvenSite at hc ⊢
  dsimp only at hc ⊢
  omega

theorem even_incomingPos_of_odd {c : Site} (hc : ¬ EvenSite c) : EvenSite (incomingPos c) := by
  unfold incomingPos
  rw [if_neg hc]
  unfold EvenSite at hc ⊢
  dsimp only at hc ⊢
  omega

/-- **Even centre row (Q30).** An even centre whose grade lies in `[2 − 2d + 2n, 2d − 2]`, with the ordinary strip at the centre and
the odd extension at its two horizontal inputs, is white. -/
theorem even_centre_white (frame : ChildFrame) {F : Field}
    (hstrip : ∀ w : Site, 2 - 2 * frame.child.den ≤ frame.sGrade w →
      frame.sGrade w ≤ 2 * (frame.child.den + frame.child.num) - 2 → F w = harmonicGrid w)
    (hodd : ∀ w : Site, ¬ EvenSite w → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade w →
      frame.sGrade w ≤ 3 * frame.child.den + frame.child.num - 2 → F w = harmonicGrid w)
    {c : Site} (he : EvenSite c)
    (hlo : 2 - 2 * frame.child.den + 2 * frame.child.num ≤ frame.sGrade c)
    (hhi : frame.sGrade c ≤ 2 * frame.child.den - 2) : laplacian F c = 0 := by
  obtain ⟨hn, hnd, hdn, hd3, -⟩ := frame.child_facts
  apply laplacian_eq_zero_of_agree
  · exact hstrip c (by linarith) (by linarith)
  · exact hodd _ (not_even_incomingNeg_of_even he)
      (by rw [sGrade_neg_even frame he]; linarith) (by rw [sGrade_neg_even frame he]; linarith)
  · exact hodd _ (not_even_incomingPos_of_even he)
      (by rw [sGrade_pos_even frame he]; linarith) (by rw [sGrade_pos_even frame he]; linarith)

/-- **Odd centre row (Q30).** An odd centre whose grade lies in `[2 − L, d + 3n − 2]` is white when the ordinary strip covers it and its
two vertical inputs. -/
theorem odd_centre_white (frame : ChildFrame) {F : Field}
    (hstrip : ∀ w : Site, 2 - 2 * frame.child.den ≤ frame.sGrade w →
      frame.sGrade w ≤ 2 * (frame.child.den + frame.child.num) - 2 → F w = harmonicGrid w)
    {c : Site} (ho : ¬ EvenSite c)
    (hlo : 2 - (frame.child.den + frame.child.num) ≤ frame.sGrade c)
    (hhi : frame.sGrade c ≤ frame.child.den + 3 * frame.child.num - 2) : laplacian F c = 0 := by
  obtain ⟨hn, hnd, hdn, hd3, -⟩ := frame.child_facts
  apply laplacian_eq_zero_of_agree
  · exact hstrip c (by linarith) (by linarith)
  · exact hstrip _ (by rw [sGrade_neg_odd frame ho]; linarith) (by rw [sGrade_neg_odd frame ho]; linarith)
  · exact hstrip _ (by rw [sGrade_pos_odd frame ho]; linarith) (by rw [sGrade_pos_odd frame ho]; linarith)

/-- **The north middle of an odd V root (Q30, `hu_white` of `game_NW`).** -/
theorem V_NW_hu_white (frame : ChildFrame) {F : Field}
    (hstrip : ∀ w : Site, 2 - 2 * frame.child.den ≤ frame.sGrade w →
      frame.sGrade w ≤ 2 * (frame.child.den + frame.child.num) - 2 → F w = harmonicGrid w)
    (hodd : ∀ w : Site, ¬ EvenSite w → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade w →
      frame.sGrade w ≤ 3 * frame.child.den + frame.child.num - 2 → F w = harmonicGrid w)
    {z : Site} (ho : ¬ EvenSite z)
    (hS1 : 2 * frame.child.num + 2 - (frame.child.den - frame.child.num) ≤ frame.sGrade z)
    (hS2 : frame.sGrade z ≤ frame.child.den + frame.child.num - 2) :
    laplacian F (z.1, z.2 + 1) = 0 := by
  obtain ⟨hn, hnd, hdn, hd3, -⟩ := frame.child_facts
  have hu : EvenSite (z.1, z.2 + 1) := by
    unfold EvenSite at ho ⊢
    simp only at ho ⊢
    omega
  apply even_centre_white frame hstrip hodd hu
  · have h : frame.sGrade (z.1, z.2 + 1) = frame.sGrade z + (frame.child.den - frame.child.num) := by
      unfold ChildFrame.sGrade
      dsimp only
      ring
    rw [h]
    linarith
  · have h : frame.sGrade (z.1, z.2 + 1) = frame.sGrade z + (frame.child.den - frame.child.num) := by
      unfold ChildFrame.sGrade
      dsimp only
      ring
    rw [h]
    linarith

/-- **The west middle of an even internal V root (Q30, `hu_white` of `game_WNE`).** -/
theorem V_WNE_hu_white (frame : ChildFrame) {F : Field}
    (hstrip : ∀ w : Site, 2 - 2 * frame.child.den ≤ frame.sGrade w →
      frame.sGrade w ≤ 2 * (frame.child.den + frame.child.num) - 2 → F w = harmonicGrid w)
    {z : Site} (he : EvenSite z)
    (hS1 : 2 ≤ frame.sGrade z) (hS2 : frame.sGrade z ≤ 2 * frame.child.num - 2) :
    laplacian F (z.1 - 1, z.2) = 0 := by
  obtain ⟨hn, hnd, hdn, hd3, -⟩ := frame.child_facts
  have hu : ¬ EvenSite (z.1 - 1, z.2) := by
    unfold EvenSite at he ⊢
    simp only at he ⊢
    omega
  apply odd_centre_white frame hstrip hu
  · have h : frame.sGrade (z.1 - 1, z.2) = frame.sGrade z - (frame.child.den + frame.child.num) := by
      unfold ChildFrame.sGrade
      dsimp only
      ring
    rw [h]
    linarith
  · have h : frame.sGrade (z.1 - 1, z.2) = frame.sGrade z - (frame.child.den + frame.child.num) := by
      unfold ChildFrame.sGrade
      dsimp only
      ring
    rw [h]
    linarith

/-- **The second middle of the west, north, east route (Q30, `hm_white` of `game_WNE`).** It needs the extra grade bound
`2 − 2d + 4n ≤ s(z)` (the audit's `σ ≥ 2 − 2d + 4n`; it holds for every internal midpoint when `d ≥ 2n`). -/
theorem V_WNE_hm_white (frame : ChildFrame) {F : Field}
    (hstrip : ∀ w : Site, 2 - 2 * frame.child.den ≤ frame.sGrade w →
      frame.sGrade w ≤ 2 * (frame.child.den + frame.child.num) - 2 → F w = harmonicGrid w)
    (hodd : ∀ w : Site, ¬ EvenSite w → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade w →
      frame.sGrade w ≤ 3 * frame.child.den + frame.child.num - 2 → F w = harmonicGrid w)
    {z : Site} (he : EvenSite z)
    (hS1 : 2 - 2 * frame.child.den + 4 * frame.child.num ≤ frame.sGrade z)
    (hS2 : frame.sGrade z ≤ 2 * frame.child.num - 2) :
    laplacian F (z.1 - 1, z.2 + 1) = 0 := by
  obtain ⟨hn, hnd, hdn, hd3, -⟩ := frame.child_facts
  have hm : EvenSite (z.1 - 1, z.2 + 1) := by
    unfold EvenSite at he ⊢
    simp only at he ⊢
    omega
  apply even_centre_white frame hstrip hodd hm
  · have h : frame.sGrade (z.1 - 1, z.2 + 1) = frame.sGrade z - 2 * frame.child.num := by
      unfold ChildFrame.sGrade
      dsimp only
      ring
    rw [h]
    linarith
  · have h : frame.sGrade (z.1 - 1, z.2 + 1) = frame.sGrade z - 2 * frame.child.num := by
      unfold ChildFrame.sGrade
      dsimp only
      ring
    rw [h]
    linarith

/-- **`game_NW` with its north-middle whiteness supplied by Q30.** -/
theorem game_NW_of_strips (frame : ChildFrame) {F : Field} {S : Set Site}
    (hG : IsGameFort frame (-1) F S)
    (hstrip : ∀ w : Site, 2 - 2 * frame.child.den ≤ frame.sGrade w →
      frame.sGrade w ≤ 2 * (frame.child.den + frame.child.num) - 2 → F w = harmonicGrid w)
    (hodd : ∀ w : Site, ¬ EvenSite w → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade w →
      frame.sGrade w ≤ 3 * frame.child.den + frame.child.num - 2 → F w = harmonicGrid w)
    {z : Site} (hzS : z ∈ S) (hzV : z ∈ frame.freeV) (hzH : z ∉ frame.freeH) (ho : ¬ EvenSite z)
    (hzW : laplacian F z = 0)
    (hS1 : 2 * frame.child.num + 2 - (frame.child.den - frame.child.num) ≤ frame.sGrade z)
    (hS2 : frame.sGrade z ≤ frame.child.den + frame.child.num - 2)
    (ht1 : frame.child.num + frame.child.den - 1 - frame.child.periodDenominator + frame.child.den < frame.tGrade z)
    (ht2 : frame.tGrade z < frame.child.den) :
    (z.1 - 1, z.2 + 1) ∈ S :=
  game_NW frame hG hzS hzV hzH ho hzW hS1 hS2 ht1 ht2 (V_NW_hu_white frame hstrip hodd ho hS1 hS2)

/-- **`game_WNE` with both middle whitenesses supplied by Q30.** The second middle needs the grade bound `hsig`. -/
theorem game_WNE_of_strips (frame : ChildFrame) {F : Field} {S : Set Site}
    (hG : IsGameFort frame (-1) F S)
    (hstrip : ∀ w : Site, 2 - 2 * frame.child.den ≤ frame.sGrade w →
      frame.sGrade w ≤ 2 * (frame.child.den + frame.child.num) - 2 → F w = harmonicGrid w)
    (hodd : ∀ w : Site, ¬ EvenSite w → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade w →
      frame.sGrade w ≤ 3 * frame.child.den + frame.child.num - 2 → F w = harmonicGrid w)
    {z : Site} (hzS : z ∈ S) (hzV : z ∈ frame.freeV) (hzH : z ∉ frame.freeH) (he : EvenSite z)
    (hF : z ≠ vFirst) (hL : z ≠ frame.vLast) (hzW : laplacian F z = 0)
    (hS1 : 2 ≤ frame.sGrade z) (hS2 : frame.sGrade z ≤ 2 * frame.child.num - 2)
    (ht1 : 2 * (frame.child.num + frame.child.den) - 1 - frame.child.periodDenominator < frame.tGrade z)
    (ht2 : frame.tGrade z < frame.child.num)
    (hsig : 2 - 2 * frame.child.den + 4 * frame.child.num ≤ frame.sGrade z) :
    (z.1, z.2 + 1) ∈ S :=
  game_WNE frame hG hzS hzV hzH he hF hL hzW hS1 hS2 ht1 ht2
    (V_WNE_hu_white frame hstrip he hS1 hS2) (V_WNE_hm_white frame hstrip hodd he hsig hS2)

end FLatticePaper.Q30White
