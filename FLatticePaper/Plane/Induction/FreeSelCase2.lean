import FLatticePaper.Plane.Induction.FreeSelSquares
import FLatticePaper.Plane.Induction.FreeWebClaims
import FLatticePaper.Plane.Induction.RouteSteps
import FLatticePaper.Plane.Induction.StrictNonfree
import FLatticePaper.Plane.Induction.ArcRanges
import FLatticePaper.Plane.Induction.ShortPassages

/-! # Case 2 of the square clauses (Q42 part (1)): the grade facts of the collar lemmas

Lemma C of Q42: the north neighbour of an even free H site is strictly interior, hence nonfree. -/

namespace FLatticePaper.FreeSelCase2

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1 FLatticePaper.FreeWebClaims

theorem north_nonfree_of_even_freeH (frame : ChildFrame) {x y : ℤ} (hy : (x, y) ∈ frame.freeH)
    (hev : EvenSite (x, y)) : Nonfree frame (x, y + 1) := by
  obtain ⟨hn0, hnlt, -, -, -⟩ := frame.child_facts
  obtain ⟨hodd_n, hodd_d⟩ := frame.child_odd
  have hnd : frame.child.num + 2 ≤ frame.child.den := by omega
  have ht := FreeWebClaims.freeH_even_t frame hy hev
  have hs := RouteSteps.freeH_even_s_lt frame hy hev
  have hsl := FreeWebClaims.freeH_s frame hy
  have hT3 := ShortPassages.T_ge frame
  rw [frame_tGrade_eq] at ht
  rw [frame_sGrade_eq] at hs hsl
  rw [frame_periodDenominator_eq] at hs hsl hT3
  have hodd : ¬ EvenSite (x, y + 1) := by
    unfold EvenSite at hev ⊢
    simp only at hev ⊢
    omega
  have hSI : FLatticePaper.W1.StrictInterior frame.child.num frame.child.den (x, y + 1) := by
    unfold FLatticePaper.W1.StrictInterior
    simp only [w1b, w1a, w1c, w1h, if_neg hodd]
    unfold w1t w1s w1T at *
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
  exact FLatticePaper.Induction.strictInterior_nonfree frame hSI

/-- `sGrade` is additive. -/
theorem sGrade_add (frame : ChildFrame) (p q : Site) :
    frame.sGrade (p + q) = frame.sGrade p + frame.sGrade q := by
  rw [frame_sGrade_eq, frame_sGrade_eq, frame_sGrade_eq]
  unfold w1s
  simp only [Prod.fst_add, Prod.snd_add]
  ring

/-- The grade of a deck combination: `s(combine i j) = i · T`. -/
theorem sGrade_combine (frame : ChildFrame) (i j : ℤ) :
    frame.sGrade (frame.child.modifiedDeck.combine i j) = i * frame.child.periodDenominator := by
  have hk := frame.child_modifiedDeck_kernel
  have ht := frame.child_modifiedDeck_transverse
  have hc : frame.child.modifiedDeck.combine i j =
      (i * frame.child.den + j * (frame.child.num - frame.child.den),
        i * frame.child.num + j * (frame.child.num + frame.child.den)) := by
    ext <;> simp [PeriodDeck.combine, hk, ht]
  rw [hc, frame_sGrade_eq, frame_periodDenominator_eq]
  unfold w1s w1T
  ring

/-- **Lemma D (Q42).** The west neighbour of an odd free V site is nonfree. -/
theorem nonfree_west_of_odd_freeV (frame : ChildFrame) {wx wy : ℤ} (hw : (wx, wy) ∈ frame.freeV)
    (hodd : ¬ EvenSite (wx, wy)) : Nonfree frame (wx - 1, wy) := by
  obtain ⟨hn0, hnlt, -, -, -⟩ := frame.child_facts
  obtain ⟨hodd_n, hodd_d⟩ := frame.child_odd
  have hnd : frame.child.num + 2 ≤ frame.child.den := by omega
  have hs := FreeWebClaims.freeV_odd_s frame hw hodd
  have hT3 := ShortPassages.T_ge frame
  have hxe : EvenSite (wx - 1, wy) := by
    unfold EvenSite at hodd ⊢
    simp only at hodd ⊢
    omega
  have hsx : frame.sGrade (wx - 1, wy) = frame.sGrade (wx, wy) - (frame.child.den + frame.child.num) := by
    have hlin := sGrade_add frame (wx - 1, wy) (1, 0)
    have hsone : frame.sGrade ((1 : ℤ), (0 : ℤ)) = frame.child.den + frame.child.num := by
      rw [frame_sGrade_eq]
      unfold w1s
      ring
    have hw' : (wx - 1, wy) + ((1 : ℤ), (0 : ℤ)) = (wx, wy) := by
      ext <;> simp
    rw [hw'] at hlin
    linarith
  have hx_lo : 2 - 2 * frame.child.den ≤ frame.sGrade (wx - 1, wy) := by
    rw [hsx]
    have := hs.1
    have hL : frame.child.den + frame.child.num = frame.child.den + frame.child.num := rfl
    omega
  have hx_hi : frame.sGrade (wx - 1, wy) ≤ -2 := by
    rw [hsx]
    have := hs.2
    omega
  intro v hv hmem
  obtain ⟨i, j, hvij⟩ := hv
  have hsv : frame.sGrade v = i * frame.child.periodDenominator := by
    rw [hvij]
    exact sGrade_combine frame i j
  have hsum : frame.sGrade ((wx - 1, wy) + v) = frame.sGrade (wx - 1, wy) + i * frame.child.periodDenominator := by
    rw [sGrade_add, hsv]
  have hev : EvenSite ((wx - 1, wy) + v) := by
    have hvev := FreePolicy.span_even frame ⟨i, j, hvij⟩
    unfold EvenSite at hxe hvev ⊢
    simp only [Prod.fst_add, Prod.snd_add] at hxe hvev ⊢
    omega
  have hTnn : 0 ≤ frame.child.periodDenominator := by linarith
  rcases hmem with hH | hV
  · have hlt := RouteSteps.freeH_even_s_lt frame (x := ((wx - 1, wy) + v).1) (y := ((wx - 1, wy) + v).2) hH hev
    have hlow := (FreeWebClaims.freeH_s frame hH).1
    rw [hsum] at hlt hlow
    by_cases hi : i ≤ 0
    · have hiT := mul_le_mul_of_nonneg_right hi hTnn
      linarith
    · have hi1 : (1 : ℤ) ≤ i := by omega
      have hiT := mul_le_mul_of_nonneg_right hi1 hTnn
      linarith
  · have hev' := FreeWebClaims.freeV_even_s frame hV hev
    rw [hsum] at hev'
    by_cases hi : i ≤ 0
    · have hiT := mul_le_mul_of_nonneg_right hi hTnn
      linarith
    · have hi1 : (1 : ℤ) ≤ i := by omega
      have hiT := mul_le_mul_of_nonneg_right hi1 hTnn
      linarith

end FLatticePaper.FreeSelCase2
