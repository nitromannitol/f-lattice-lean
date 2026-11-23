import FLatticePaper.Plane.Induction.ConjFreeRoot
import FLatticePaper.Plane.Induction.W1Lower
import FLatticePaper.Plane.Induction.W1Strips
import FLatticePaper.Plane.Induction.W1Seeds
import FLatticePaper.Plane.Induction.OddStep

/-! Task 72 (case (b), the even window `hWin` and the neighbour zero strip `hsy`).

The extended even window of the parent field, `1 − r ≤ t_p ≤ 2r − 1` with `r = D + N`, is the conjugate's extended odd `h0` band:
for `x` even, `z = Z x` is odd, `s_c(z) = 2 (t_p x − N)` runs over `[2 − 3d_c + n_c, 3d_c + n_c − 2] = [2 − 2D − 4N, 4D + 2N − 2]`,
where `(n_c, d_c) = (D − N, D + N)`. There `standardField (conjWord w) z = harmonicGrid z` (`odd_band_conj`, from `lower_odd_h0`,
`odd_h0_upper` and the ordinary harmonic strip). The harmonic identity `h(Z x) = −h(x)` (`harmonicGrid_zTurn`) then gives the zero. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper FLatticePaper.W1Seeds FLatticePaper.W1Strips

/-- The harmonic grid is odd under the quarter turn `Z`: `h(Z x) = −h(x)`. -/
theorem harmonicGrid_zTurn (x : Site) : harmonicGrid (zTurn x) = -harmonicGrid x := by
  have h1 := harmonicGrid_exact (zTurn x)
  have h2 := harmonicGrid_exact x
  have hm : ((zTurn x).1 + (zTurn x).2) % 2 = 1 - (x.1 + x.2) % 2 := by
    unfold zTurn
    simp only
    omega
  have key : 4 * (harmonicGrid (zTurn x) + harmonicGrid x) = 0 := by
    rw [mul_add, h1, h2, hm]
    unfold zTurn
    ring
  omega

/-- **The conjugate's odd band.** For the conjugate word, `F = h` on odd sites with conjugate `s` in the extended odd band
`[2 − 3d + n, 3d + n − 2]`. -/
theorem odd_band_conj {w : Word} (hS : StrongEstimates (conjWord w)) (hpar : SeedFields (conjWord w)) (z : Site)
    (hz : ¬ EvenSite z)
    (hlo : 2 - 3 * (frameAt (conjWord w)).child.den + (frameAt (conjWord w)).child.num ≤ (frameAt (conjWord w)).sGrade z)
    (hhi : (frameAt (conjWord w)).sGrade z ≤ 3 * (frameAt (conjWord w)).child.den + (frameAt (conjWord w)).child.num - 2) :
    standardField (conjWord w) z = harmonicGrid z := by
  have hlow : ∀ z : Site, ¬ EvenSite z →
      2 - 3 * (frameAt (conjWord w)).child.den + (frameAt (conjWord w)).child.num ≤ (frameAt (conjWord w)).sGrade z →
      (frameAt (conjWord w)).sGrade z ≤ 1 - 2 * (frameAt (conjWord w)).child.den →
      standardField (conjWord w) z = harmonicGrid z :=
    fun z hz h1 h2 => FLatticePaper.W1Lower.lower_odd_h0 (frameAt (conjWord w)) hS.packet.strips hS.priceRange
      (fun z => by have := (hS.priceDrift z).1; linarith)
      (fun z => by have := (hS.priceDrift z).2; linarith)
      (fun v hv hs => hpar.odd_bottom v hv hs) z hz h1 h2
  by_cases hs1 : (frameAt (conjWord w)).sGrade z ≤ 1 - 2 * (frameAt (conjWord w)).child.den
  · exact hlow z hz hlo hs1
  by_cases hs2 : (frameAt (conjWord w)).sGrade z ≤
      2 * ((frameAt (conjWord w)).child.den + (frameAt (conjWord w)).child.num) - 1
  · exact hS.packet.strips.2 z (by omega) hs2
  · exact FLatticePaper.W1Strips.odd_h0_upper (frameAt (conjWord w)) (FLatticePaper.W1Strips.standardField_iRefl hS) hlow z hz (by omega) hhi

/-- **The extended even window (`hWin`).** For `x` even with `1 − (D+N) ≤ t_p x ≤ 2(D+N) − 1`, the parent field vanishes. -/
theorem even_window_zero_of_strong {w : Word} (h : ∃ x ∈ w, x ≠ Digit.three)
    (hS : StrongEstimates (conjWord w)) (hpar : SeedFields (conjWord w)) (x : Site) (hx : EvenSite x)
    (hlo : 1 - ((frameAt w).parents.odd.den + (frameAt w).parents.odd.num) ≤ (frameAt w).parentTGrade x)
    (hhi : (frameAt w).parentTGrade x ≤ 2 * ((frameAt w).parents.odd.den + (frameAt w).parents.odd.num) - 1) :
    quarterTurnField (standardField (conjWord w)) x = 0 := by
  have hconj : (frameAt (conjWord w)).child = (frameAt w).parents.odd.rotate := frameAt_conj_child h
  obtain ⟨hcn, hcd⟩ := conj_child_num_den hconj
  have hzE : ¬ EvenSite (zTurn x) := by
    unfold EvenSite at hx ⊢
    simp only [zTurn] at hx ⊢
    omega
  have hs := conj_sGrade_zTurn h x
  have hG := odd_band_conj hS hpar (zTurn x) hzE
    (by rw [hcn, hcd, hs]; omega) (by rw [hcn, hcd, hs]; omega)
  unfold quarterTurnField
  rw [quarterTurn_site]
  show standardField (conjWord w) (zTurn x) + harmonicGrid x = 0
  rw [hG, harmonicGrid_zTurn]
  ring

/-- The partner `x + εU_q` has the same site parity as `x`: the even parent has `num + den` even, so `εU_q` is an even
vector. -/
theorem evenSite_add_eps_uq_iff {w : Word} (x : Site) :
    EvenSite (x + ((frameAt w).eps * (frameAt w).parents.even.den, (frameAt w).eps * (frameAt w).parents.even.num)) ↔
      EvenSite x := by
  have hsq := (frameAt w).eps_sq_one
  have hev : ((frameAt w).parents.even.num + (frameAt w).parents.even.den) % 2 = 0 :=
    (frameAt w).valid.even_parity
  have heps : (frameAt w).eps = 1 ∨ (frameAt w).eps = -1 := by
    have : (frameAt w).eps * (frameAt w).eps = 1 := hsq
    rcases Int.eq_one_or_neg_one_of_mul_eq_one this with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
  rcases heps with h1 | h1 <;> rw [h1] <;> simp only [EvenSite, Prod.fst_add, Prod.snd_add] <;>
    constructor <;> intro hh <;> omega

/-- **An even jump vanishes**: for `x` even with `t_p x` and `t_p x + 1` both in the extended window, the jump `a(x) = 0`
(both arguments `x, x + εU_q` are even, so `hWin` applies to each). -/
theorem jumpA_zero_of_even_window {w : Word} (h : ∃ x ∈ w, x ≠ Digit.three)
    (hS : StrongEstimates (conjWord w)) (hpar : SeedFields (conjWord w)) (x : Site) (hx : EvenSite x)
    (hlo : 1 - ((frameAt w).parents.odd.den + (frameAt w).parents.odd.num) ≤ (frameAt w).parentTGrade x)
    (hhi : (frameAt w).parentTGrade x ≤ 2 * ((frameAt w).parents.odd.den + (frameAt w).parents.odd.num) - 1)
    (hlo' : 1 - ((frameAt w).parents.odd.den + (frameAt w).parents.odd.num) ≤
      (frameAt w).parentTGrade x + 1)
    (hhi' : (frameAt w).parentTGrade x + 1 ≤ 2 * ((frameAt w).parents.odd.den + (frameAt w).parents.odd.num) - 1) :
    jumpA (frameAt w) (quarterTurnField (standardField (conjWord w))) x = 0 := by
  have hsh := parentTGrade_add_eps_uq (frameAt w) x
  have hx1 := even_window_zero_of_strong h hS hpar x hx hlo hhi
  have hx2 := even_window_zero_of_strong h hS hpar
    (x + ((frameAt w).eps * (frameAt w).parents.even.den, (frameAt w).eps * (frameAt w).parents.even.num))
    ((evenSite_add_eps_uq_iff x).2 hx)
    (by rw [hsh]; exact hlo') (by rw [hsh]; exact hhi')
  unfold jumpA
  rw [hx1, hx2]
  norm_num

end FLatticePaper.Induction
