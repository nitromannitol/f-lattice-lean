import FLatticePaper.Plane.Induction.W1OfferOne
import FLatticePaper.Plane.Induction.W1OddSeedZero

/-! # Task 75 (offers): the second offer at the odd seed, through the reflected even seed

The second offer is the other sheet at `Y`. Its `F_p`-part is `G(Q₂) − h₀(Q₂)` with `Q₂` the `Z` of the sheet argument, and
the conjugate reflection `G(c − Q) = G(Q) − t'(Q) + s_C` (with `c = centre`, `s_C = symmetryConstant`) together with the even seed
`G = 0` at the even point `c − Q₂` (`t' = 2 − 2D`, the induction hypothesis `SeedFields(conjWord w).even_zero`) gives `G(Q₂) = t'(Q₂) − s_C`.
The harmonic identity `h₀(Q₂) + h₀(y) = t'(Q₂) − s_C` (no relation needed, with the parity of the odd point `y`) turns the sheet into
`h₀(y)` plus the affine term, which is the second offer of `W1OddSeedId`. -/

namespace FLatticePaper.W1OfferTwo

open Farey FLatticePaper FLatticePaper.Induction

/-- **The reflected even seed** (generic): if `c − Q` is an even point with `t' = 2 − L'` and the even seed vanishes there, then
`G(Q) = t'(Q) − s_C`. -/
theorem conj_fp_of_seed (C : ChildFrame) {G : Field} (hP : C.Packet G)
    (hseed : ∀ z : Site, EvenSite z → C.tGrade z = 2 - (C.child.den + C.child.num) → G z = 0)
    (Q : Site) (hev : EvenSite (C.centre - Q))
    (ht : C.tGrade (C.centre - Q) = 2 - (C.child.den + C.child.num)) :
    G Q = C.tGrade Q - C.symmetryConstant := by
  have hr := hP.reflection Q
  rw [hseed _ hev ht] at hr
  linarith

/-- The centre of the conjugate frame: `c = (D − N + 1, 3D − N − 1)` for the child `(D − N, D + N)`. -/
theorem conj_centre (C : ChildFrame) (D N : ℤ) (hb : C.child.num = D - N) (hr : C.child.den = D + N) :
    C.centre = (D - N + 1, 3 * D - N - 1) := by
  unfold ChildFrame.centre
  rw [ChildFrame.child_modifiedDeck_kernel, ChildFrame.child_modifiedDeck_transverse, hb, hr]
  refine Prod.ext ?_ ?_ <;> simp only [Prod.mk_add_mk] <;> ring

/-- The symmetry constant of the conjugate: `s_C = D − D² − 2DN + N²` (from `(d' + n' − T')/2`). -/
theorem conj_symmetry (C : ChildFrame) (D N : ℤ) (hb : C.child.num = D - N) (hr : C.child.den = D + N)
    (hT : C.child.periodDenominator = C.child.den ^ 2 + 2 * C.child.den * C.child.num - C.child.num ^ 2) :
    C.symmetryConstant = D - D ^ 2 - 2 * D * N + N ^ 2 := by
  unfold ChildFrame.symmetryConstant
  rw [hT, hb, hr]
  have h2 : (D + N + (D - N) - ((D + N) ^ 2 + 2 * (D + N) * (D - N) - (D - N) ^ 2)) =
      2 * (D - D ^ 2 - 2 * D * N + N ^ 2) := by ring
  rw [h2, Int.mul_ediv_cancel_left _ two_ne_zero]

/-- **The second offer for `ε = +1`** (task 75): the `C`-sheet at `Y` is `−h₀(z)`, through the reflected even seed. -/
theorem offer_two_sheetC_pos {w : Word} (h : ∃ x ∈ w, x ≠ Digit.three)
    (hS : StrongEstimates (conjWord w)) (hε : (frameAt w).eps = 1)
    (hseed : ∀ z : Site, EvenSite z →
      (frameAt (conjWord w)).tGrade z = 2 - ((frameAt (conjWord w)).child.den + (frameAt (conjWord w)).child.num) →
        standardField (conjWord w) z = 0) :
    (frameAt w).sheetC (quarterTurnField (standardField (conjWord w)))
        (W1OddSeedY.oddSeedY (frameAt w)) =
      -harmonicGrid (W1OddSeedY.oddSeedPoint (frameAt w)) := by
  have hcj : (frameAt (conjWord w)).child = (frameAt w).parents.odd.rotate := frameAt_conj_child h
  have hrot : (frameAt w).parents.odd.rotate =
      ⟨(frameAt w).parents.odd.den - (frameAt w).parents.odd.num,
        (frameAt w).parents.odd.den + (frameAt w).parents.odd.num⟩ :=
    Fraction.rotate_of_odd (frameAt w).valid.odd_parity
  have hb : (frameAt (conjWord w)).child.num =
      (frameAt w).parents.odd.den - (frameAt w).parents.odd.num := by rw [hcj, hrot]
  have hr' : (frameAt (conjWord w)).child.den =
      (frameAt w).parents.odd.den + (frameAt w).parents.odd.num := by rw [hcj, hrot]
  have hcn : (frameAt w).child.num = 2 * (frameAt w).parents.odd.num + (frameAt w).parents.even.num :=
    (frameAt w).child_num_eq
  have hcd : (frameAt w).child.den = 2 * (frameAt w).parents.odd.den + (frameAt w).parents.even.den :=
    (frameAt w).child_den_eq
  have hev : ((frameAt w).child.num + (frameAt w).child.den) % 2 = 0 := (frameAt w).child_even
  have hpe := ZoneI1.eps_eq (frameAt w)
  rw [hε] at hpe
  have hrel : (frameAt w).parents.odd.num * (frameAt w).parents.even.den -
      (frameAt w).parents.odd.den * (frameAt w).parents.even.num = 1 := by
    linear_combination (-1 : ℤ) * hpe
  obtain ⟨hDpos, hN0, hND⟩ := (frameAt w).valid.odd_bounds
  obtain ⟨heD, her0, -⟩ := (frameAt w).valid.even_bounds
  obtain ⟨J0, hJ⟩ := FLatticePaper.W1OfferOne.exists_half_J (frameAt w).parents.even.den (frameAt w).parents.even.num
  have hz : W1OddSeedY.oddSeedPoint (frameAt w) =
      ((frameAt w).parents.odd.den + (frameAt w).parents.odd.num - 1,
        (frameAt w).parents.odd.den - (frameAt w).parents.odd.num + 1) := by
    unfold W1OddSeedY.oddSeedPoint
    rw [FLatticePaper.W1Seeds.phaseW_pos (frameAt w) hε]
    simp
  have hY : W1OddSeedY.oddSeedY (frameAt w) =
      ((frameAt w).parents.odd.den + (frameAt w).parents.odd.num + (frameAt w).parents.even.den - 1,
        (frameAt w).parents.odd.den + 3 * (frameAt w).parents.odd.num + (frameAt w).parents.even.num - 2) := by
    unfold W1OddSeedY.oddSeedY
    rw [hz, hcn, hcd]
    refine Prod.ext ?_ ?_ <;> ring
  have hsh1 : (frameAt w).sheetShift = 0 := by
    unfold ChildFrame.sheetShift
    rw [FLatticePaper.W1Seeds.phaseW_pos (frameAt w) hε]
    simp
  have hso1 : (frameAt w).sheetOffset =
      ((frameAt w).parents.even.num, (frameAt w).parents.even.den + 2 * (frameAt w).parents.even.num) := by
    unfold ChildFrame.sheetOffset
    rw [hε]
    refine Prod.ext ?_ ?_ <;>
      simp only [Fraction.unmodifiedDeck, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
      ring
  have hPk : (frameAt (conjWord w)).Packet (standardField (conjWord w)) := hS.packet
  obtain ⟨-, -, -, -, hT⟩ := (frameAt (conjWord w)).child_facts
  -- the conjugate argument Q₂ = Z(Y − (r, e + 2r))
  have hQ2 : (-((W1OddSeedY.oddSeedY (frameAt w)) - ((frameAt w).parents.even.num,
        (frameAt w).parents.even.den + 2 * (frameAt w).parents.even.num)).2,
      ((W1OddSeedY.oddSeedY (frameAt w)) - ((frameAt w).parents.even.num,
        (frameAt w).parents.even.den + 2 * (frameAt w).parents.even.num)).1 - 1) =
      (-(frameAt w).parents.odd.den - 3 * (frameAt w).parents.odd.num + (frameAt w).parents.even.num +
          (frameAt w).parents.even.den + 2,
        (frameAt w).parents.odd.den + (frameAt w).parents.odd.num + (frameAt w).parents.even.den -
          (frameAt w).parents.even.num - 2) := by
    rw [hY]
    refine Prod.ext ?_ ?_ <;> simp only [Prod.fst_sub, Prod.snd_sub] <;> ring
  -- the reflected even seed at c − Q₂
  have hcen := conj_centre (frameAt (conjWord w)) (frameAt w).parents.odd.den (frameAt w).parents.odd.num hb hr'
  have hev2 : EvenSite ((frameAt (conjWord w)).centre -
      (-(frameAt w).parents.odd.den - 3 * (frameAt w).parents.odd.num + (frameAt w).parents.even.num +
          (frameAt w).parents.even.den + 2,
        (frameAt w).parents.odd.den + (frameAt w).parents.odd.num + (frameAt w).parents.even.den -
          (frameAt w).parents.even.num - 2)) := by
    rw [hcen]
    unfold EvenSite
    simp only [Prod.fst_sub, Prod.snd_sub]
    omega
  have ht2 : (frameAt (conjWord w)).tGrade ((frameAt (conjWord w)).centre -
      (-(frameAt w).parents.odd.den - 3 * (frameAt w).parents.odd.num + (frameAt w).parents.even.num +
          (frameAt w).parents.even.den + 2,
        (frameAt w).parents.odd.den + (frameAt w).parents.odd.num + (frameAt w).parents.even.den -
          (frameAt w).parents.even.num - 2)) =
      2 - ((frameAt (conjWord w)).child.den + (frameAt (conjWord w)).child.num) := by
    rw [hcen]
    unfold ChildFrame.tGrade
    simp only [Prod.fst_sub, Prod.snd_sub]
    rw [hb, hr']
    linear_combination 2 * hrel
  have hG2 := conj_fp_of_seed (frameAt (conjWord w)) hPk hseed _ hev2 ht2
  have hsym := conj_symmetry (frameAt (conjWord w)) (frameAt w).parents.odd.den (frameAt w).parents.odd.num hb hr' hT
  -- the harmonic identity h0(Q₂) + h0(y) = t'(Q₂) − s_C
  have eQ := FLatticePaper.W1OddSeedId.four_harmonic_even
    (-(frameAt w).parents.odd.den - 3 * (frameAt w).parents.odd.num + (frameAt w).parents.even.num +
        (frameAt w).parents.even.den + 2,
      (frameAt w).parents.odd.den + (frameAt w).parents.odd.num + (frameAt w).parents.even.den -
        (frameAt w).parents.even.num - 2) (by simp only; omega)
  have ey := FLatticePaper.W1OddSeedId.four_harmonic_odd
    ((frameAt w).parents.odd.num - (frameAt w).parents.odd.den - ((frameAt w).parents.even.num - (frameAt w).parents.even.den) - 1,
      (frameAt w).parents.odd.den + (frameAt w).parents.odd.num - ((frameAt w).parents.even.den + (frameAt w).parents.even.num) - 2)
    (by simp only; omega)
  have hH2 : 4 * (harmonicGrid (-(frameAt w).parents.odd.den - 3 * (frameAt w).parents.odd.num + (frameAt w).parents.even.num +
        (frameAt w).parents.even.den + 2,
      (frameAt w).parents.odd.den + (frameAt w).parents.odd.num + (frameAt w).parents.even.den -
        (frameAt w).parents.even.num - 2) +
      harmonicGrid ((frameAt w).parents.odd.num - (frameAt w).parents.odd.den - ((frameAt w).parents.even.num - (frameAt w).parents.even.den) - 1,
        (frameAt w).parents.odd.den + (frameAt w).parents.odd.num - ((frameAt w).parents.even.den + (frameAt w).parents.even.num) - 2)) =
      4 * ((frameAt (conjWord w)).tGrade (-(frameAt w).parents.odd.den - 3 * (frameAt w).parents.odd.num + (frameAt w).parents.even.num +
        (frameAt w).parents.even.den + 2,
      (frameAt w).parents.odd.den + (frameAt w).parents.odd.num + (frameAt w).parents.even.den -
        (frameAt w).parents.even.num - 2) - (frameAt (conjWord w)).symmetryConstant) := by
    rw [hsym]
    unfold ChildFrame.tGrade
    simp only []
    rw [hb, hr']
    linear_combination eQ + ey
  have hH2' := mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0) hH2
  have hoff := FLatticePaper.W1OddSeedId.offer_two_pos (frameAt w).parents.odd.den (frameAt w).parents.odd.num
    (frameAt w).parents.even.den (frameAt w).parents.even.num J0 hrel hJ
  -- the sheet C at Y
  unfold ChildFrame.sheetC
  rw [hsh1, sub_zero, hso1, FLatticePaper.W1ZeroStrip.quarterTurn_eq_sub, hQ2, hG2]
  unfold ChildFrame.siblingSlope ChildFrame.sheetConstant
  rw [FLatticePaper.W1Seeds.phaseW_pos (frameAt w) hε, hY, hz]
  have hPJ : ((frameAt w).parents.even.periodDenominator - (frameAt w).parents.even.den -
      (frameAt w).parents.even.num) / 2 = J0 := by
    have h2 : (frameAt w).parents.even.periodDenominator - (frameAt w).parents.even.den -
        (frameAt w).parents.even.num = 2 * J0 := by
      unfold Fraction.periodDenominator
      linear_combination (-1 : ℤ) * hJ
    rw [h2]
    omega
  rw [hPJ]
  linear_combination hoff - hH2'

/-- **The second offer for `ε = −1`** (task 75): the `A`-sheet at `Y` is `−h₀(z)`, through the reflected even seed. -/
theorem offer_two_sheetA_neg {w : Word} (h : ∃ x ∈ w, x ≠ Digit.three)
    (hS : StrongEstimates (conjWord w)) (hε : (frameAt w).eps = -1)
    (hseed : ∀ z : Site, EvenSite z →
      (frameAt (conjWord w)).tGrade z = 2 - ((frameAt (conjWord w)).child.den + (frameAt (conjWord w)).child.num) →
        standardField (conjWord w) z = 0) :
    (frameAt w).sheetA (quarterTurnField (standardField (conjWord w)))
        (W1OddSeedY.oddSeedY (frameAt w)) =
      -harmonicGrid (W1OddSeedY.oddSeedPoint (frameAt w)) := by
  have hcj : (frameAt (conjWord w)).child = (frameAt w).parents.odd.rotate := frameAt_conj_child h
  have hrot : (frameAt w).parents.odd.rotate =
      ⟨(frameAt w).parents.odd.den - (frameAt w).parents.odd.num,
        (frameAt w).parents.odd.den + (frameAt w).parents.odd.num⟩ :=
    Fraction.rotate_of_odd (frameAt w).valid.odd_parity
  have hb : (frameAt (conjWord w)).child.num =
      (frameAt w).parents.odd.den - (frameAt w).parents.odd.num := by rw [hcj, hrot]
  have hr' : (frameAt (conjWord w)).child.den =
      (frameAt w).parents.odd.den + (frameAt w).parents.odd.num := by rw [hcj, hrot]
  have hcn : (frameAt w).child.num = 2 * (frameAt w).parents.odd.num + (frameAt w).parents.even.num :=
    (frameAt w).child_num_eq
  have hcd : (frameAt w).child.den = 2 * (frameAt w).parents.odd.den + (frameAt w).parents.even.den :=
    (frameAt w).child_den_eq
  have hev : ((frameAt w).child.num + (frameAt w).child.den) % 2 = 0 := (frameAt w).child_even
  have hpe := ZoneI1.eps_eq (frameAt w)
  rw [hε] at hpe
  have hrel : (frameAt w).parents.odd.num * (frameAt w).parents.even.den -
      (frameAt w).parents.odd.den * (frameAt w).parents.even.num = -1 := by
    linear_combination (-1 : ℤ) * hpe
  obtain ⟨hDpos, hN0, hND⟩ := (frameAt w).valid.odd_bounds
  obtain ⟨heD, her0, -⟩ := (frameAt w).valid.even_bounds
  have hz : W1OddSeedY.oddSeedPoint (frameAt w) =
      ((frameAt w).parents.odd.den + (frameAt w).parents.odd.num - 1 + (frameAt w).parents.even.den +
          (frameAt w).parents.even.num,
        (frameAt w).parents.odd.den - (frameAt w).parents.odd.num + 1 + (frameAt w).parents.even.den -
          (frameAt w).parents.even.num) := by
    unfold W1OddSeedY.oddSeedPoint
    rw [FLatticePaper.W1Seeds.phaseW_neg (frameAt w) hε]
    refine Prod.ext ?_ ?_ <;> dsimp only <;> ring
  have hY : W1OddSeedY.oddSeedY (frameAt w) =
      ((frameAt w).parents.odd.den + (frameAt w).parents.odd.num + (frameAt w).parents.even.num - 1,
        (frameAt w).parents.odd.den + 3 * (frameAt w).parents.odd.num + (frameAt w).parents.even.den +
          2 * (frameAt w).parents.even.num - 2) := by
    unfold W1OddSeedY.oddSeedY
    rw [hz, hcn, hcd]
    refine Prod.ext ?_ ?_ <;> dsimp only <;> ring
  have hsh2 : (frameAt w).sheetShift = ((frameAt w).parents.even.den, (frameAt w).parents.even.num) := by
    unfold ChildFrame.sheetShift
    rw [FLatticePaper.W1Seeds.phaseW_neg (frameAt w) hε]
    simp [Fraction.unmodifiedDeck]
  have hPk : (frameAt (conjWord w)).Packet (standardField (conjWord w)) := hS.packet
  obtain ⟨-, -, -, -, hT⟩ := (frameAt (conjWord w)).child_facts
  -- the conjugate argument Q₂ = Z(Y − (e, r))
  have hQ2 : (-((W1OddSeedY.oddSeedY (frameAt w)) - ((frameAt w).parents.even.den,
        (frameAt w).parents.even.num)).2,
      ((W1OddSeedY.oddSeedY (frameAt w)) - ((frameAt w).parents.even.den,
        (frameAt w).parents.even.num)).1 - 1) =
      (-(frameAt w).parents.odd.den - 3 * (frameAt w).parents.odd.num - (frameAt w).parents.even.den -
          (frameAt w).parents.even.num + 2,
        (frameAt w).parents.odd.den + (frameAt w).parents.odd.num + (frameAt w).parents.even.num -
          (frameAt w).parents.even.den - 2) := by
    rw [hY]
    refine Prod.ext ?_ ?_ <;> simp only [Prod.fst_sub, Prod.snd_sub] <;> ring
  have hcen := conj_centre (frameAt (conjWord w)) (frameAt w).parents.odd.den (frameAt w).parents.odd.num hb hr'
  have hev2 : EvenSite ((frameAt (conjWord w)).centre -
      (-(frameAt w).parents.odd.den - 3 * (frameAt w).parents.odd.num - (frameAt w).parents.even.den -
          (frameAt w).parents.even.num + 2,
        (frameAt w).parents.odd.den + (frameAt w).parents.odd.num + (frameAt w).parents.even.num -
          (frameAt w).parents.even.den - 2)) := by
    rw [hcen]
    unfold EvenSite
    simp only [Prod.fst_sub, Prod.snd_sub]
    omega
  have ht2 : (frameAt (conjWord w)).tGrade ((frameAt (conjWord w)).centre -
      (-(frameAt w).parents.odd.den - 3 * (frameAt w).parents.odd.num - (frameAt w).parents.even.den -
          (frameAt w).parents.even.num + 2,
        (frameAt w).parents.odd.den + (frameAt w).parents.odd.num + (frameAt w).parents.even.num -
          (frameAt w).parents.even.den - 2)) =
      2 - ((frameAt (conjWord w)).child.den + (frameAt (conjWord w)).child.num) := by
    rw [hcen]
    unfold ChildFrame.tGrade
    simp only [Prod.fst_sub, Prod.snd_sub]
    rw [hb, hr']
    linear_combination (-2 : ℤ) * hrel
  have hG2 := conj_fp_of_seed (frameAt (conjWord w)) hPk hseed _ hev2 ht2
  have hsym := conj_symmetry (frameAt (conjWord w)) (frameAt w).parents.odd.den (frameAt w).parents.odd.num hb hr' hT
  have eQ := FLatticePaper.W1OddSeedId.four_harmonic_even
    (-(frameAt w).parents.odd.den - 3 * (frameAt w).parents.odd.num - (frameAt w).parents.even.den -
        (frameAt w).parents.even.num + 2,
      (frameAt w).parents.odd.den + (frameAt w).parents.odd.num + (frameAt w).parents.even.num -
        (frameAt w).parents.even.den - 2) (by simp only; omega)
  have ey := FLatticePaper.W1OddSeedId.four_harmonic_odd
    ((frameAt w).parents.odd.num - (frameAt w).parents.odd.den + (frameAt w).parents.even.num -
        (frameAt w).parents.even.den - 1,
      (frameAt w).parents.odd.den + (frameAt w).parents.odd.num + (frameAt w).parents.even.den +
        (frameAt w).parents.even.num - 2) (by simp only; omega)
  have hH2 : 4 * (harmonicGrid (-(frameAt w).parents.odd.den - 3 * (frameAt w).parents.odd.num -
        (frameAt w).parents.even.den - (frameAt w).parents.even.num + 2,
      (frameAt w).parents.odd.den + (frameAt w).parents.odd.num + (frameAt w).parents.even.num -
        (frameAt w).parents.even.den - 2) +
      harmonicGrid ((frameAt w).parents.odd.num - (frameAt w).parents.odd.den + (frameAt w).parents.even.num -
          (frameAt w).parents.even.den - 1,
        (frameAt w).parents.odd.den + (frameAt w).parents.odd.num + (frameAt w).parents.even.den +
          (frameAt w).parents.even.num - 2)) =
      4 * ((frameAt (conjWord w)).tGrade (-(frameAt w).parents.odd.den - 3 * (frameAt w).parents.odd.num -
        (frameAt w).parents.even.den - (frameAt w).parents.even.num + 2,
      (frameAt w).parents.odd.den + (frameAt w).parents.odd.num + (frameAt w).parents.even.num -
        (frameAt w).parents.even.den - 2) - (frameAt (conjWord w)).symmetryConstant) := by
    rw [hsym]
    unfold ChildFrame.tGrade
    simp only []
    rw [hb, hr']
    linear_combination eQ + ey
  have hH2' := mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0) hH2
  have hoff := FLatticePaper.W1OddSeedId.offer_two_neg (frameAt w).parents.odd.den (frameAt w).parents.odd.num
    (frameAt w).parents.even.den (frameAt w).parents.even.num
  -- the sheet A at Y
  unfold ChildFrame.sheetA
  rw [hsh2, FLatticePaper.W1ZeroStrip.quarterTurn_eq_sub, hQ2, hG2, hz]
  linear_combination hoff - hH2'

end FLatticePaper.W1OfferTwo
