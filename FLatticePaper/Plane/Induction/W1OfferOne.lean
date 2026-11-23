import FLatticePaper.Plane.Induction.W1OddSeedY
import FLatticePaper.Plane.Induction.W1OddSeedId
import FLatticePaper.Plane.Induction.W1VShift
import FLatticePaper.Plane.Induction.W1ZeroStrip
import FLatticePaper.Plane.Induction.StrongEstimates
import FLatticePaper.Plane.Induction.ZoneI1
import FLatticePaper.Plane.Induction.Packet

/-! # Task 75 (offers): the first offer at the odd seed, for `ε = +1`

With `Y = Z z + U` (`oddSeedY`), `W = 1` and `F = frameAt w`, the sheet `A(Y) = F_p(Y)` where `F_p = quarterTurnField (standardField (conjWord w))`.
`Z Y = Zv + V' − U'` for `v = q + k = (e − 1, r − 2)`, `Zv = (2 − r, e − 2)`, `V' = (n' − d', n' + d')`, `U' = (d', n')` (the conjugate child
`(n', d') = (D − N, D + N)`). The conjugate packet gives:
* `G(Zv) = h₀(Zv)`: the h₀ clause at `Zv`, `s'(Zv) = 4D − 4N + 2` (N ≥ 1);
* `G(Zv + V') = G(Zv) + t'(Zv) + c'` (transverse period);
* `G(· − U') = G(·)` (kernel period, `c_U' = 0`).
The bracket identity `h₀(Zv) + t'(Zv) + c' − h₀(ZY) = t_p(v) − H` (certificate `2·relH + 2·relc`) and `offer_one_pos` then give
`A(Y) = −h₀(z)`. -/

namespace FLatticePaper.W1OfferOne

open Farey FLatticePaper FLatticePaper.Induction

/-- `(B + R)` is even: there is `H` with `2H = D² + 2DN − N² + (D + N)`. -/
theorem exists_half_BR (D N : ℤ) : ∃ H : ℤ, 2 * H = D ^ 2 + 2 * D * N - N ^ 2 + (D + N) := by
  obtain ⟨a, ha⟩ := Int.even_mul_succ_self D
  obtain ⟨b, hb⟩ := Int.even_mul_succ_self N
  exact ⟨D * N + a - b + N, by linear_combination (-1 : ℤ) * ha + hb⟩

/-- **The first offer for `ε = +1`** (task 75): `A(Y) = −h₀(z)`. -/
theorem offer_one_sheetA_pos {w : Word} (h : ∃ x ∈ w, x ≠ Digit.three)
    (hS : StrongEstimates (conjWord w)) (hε : (frameAt w).eps = 1) :
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
      (frameAt w).parents.odd.den * (frameAt w).parents.even.num = 1 := by
    linear_combination (-1 : ℤ) * hpe
  obtain ⟨hDpos, hN0, hND⟩ := (frameAt w).valid.odd_bounds
  obtain ⟨heD, her0, -⟩ := (frameAt w).valid.even_bounds
  have hN1 : 1 ≤ (frameAt w).parents.odd.num := by
    by_contra hc
    have hN0' : (frameAt w).parents.odd.num = 0 := by omega
    rw [hN0'] at hrel
    nlinarith [mul_nonneg hDpos.le her0]
  obtain ⟨H, hH⟩ := exists_half_BR (frameAt w).parents.odd.den (frameAt w).parents.odd.num
  -- the seed point and its image at W = 1
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
  have hPk : (frameAt (conjWord w)).Packet (standardField (conjWord w)) := hS.packet
  have hre : ((frameAt w).parents.even.den + (frameAt w).parents.even.num) % 2 = 0 := by omega
  -- the conjugate sGrade at Zv = (2 - r, e - 2)
  have hsZ : (frameAt (conjWord w)).sGrade (2 - (frameAt w).parents.even.num, (frameAt w).parents.even.den - 2) =
      4 * (frameAt w).parents.odd.den - 4 * (frameAt w).parents.odd.num + 2 := by
    unfold ChildFrame.sGrade
    rw [hb, hr']
    linear_combination 2 * hrel
  -- the h0 clause of the conjugate at Zv
  have hG0 : standardField (conjWord w) (2 - (frameAt w).parents.even.num, (frameAt w).parents.even.den - 2) =
      harmonicGrid (2 - (frameAt w).parents.even.num, (frameAt w).parents.even.den - 2) :=
    hPk.strips.2 _ (by rw [hsZ, hr']; linarith) (by rw [hsZ, hr', hb]; linarith)
  -- the transverse period and the kernel period of the conjugate
  have hV := FLatticePaper.W1VShift.packet_V_step (frameAt (conjWord w)) hPk
    (2 - (frameAt w).parents.even.num, (frameAt w).parents.even.den - 2)
  have hU : standardField (conjWord w)
      ((2 - (frameAt w).parents.even.num, (frameAt w).parents.even.den - 2) +
        ((frameAt (conjWord w)).child.num - (frameAt (conjWord w)).child.den,
          (frameAt (conjWord w)).child.num + (frameAt (conjWord w)).child.den) +
        (-1 : ℤ) • (frameAt (conjWord w)).child.modifiedDeck.kernel) =
      standardField (conjWord w)
        ((2 - (frameAt w).parents.even.num, (frameAt w).parents.even.den - 2) +
          ((frameAt (conjWord w)).child.num - (frameAt (conjWord w)).child.den,
            (frameAt (conjWord w)).child.num + (frameAt (conjWord w)).child.den)) := by
    have := FLatticePaper.W1VShift.packet_U_zsmul (frameAt (conjWord w)) hPk
      ((2 - (frameAt w).parents.even.num, (frameAt w).parents.even.den - 2) +
        ((frameAt (conjWord w)).child.num - (frameAt (conjWord w)).child.den,
          (frameAt (conjWord w)).child.num + (frameAt (conjWord w)).child.den)) (-1)
    exact this
  -- the bridge from Z(Y) to the conjugate lattice form
  have hQeq : (-(W1OddSeedY.oddSeedY (frameAt w)).2, (W1OddSeedY.oddSeedY (frameAt w)).1 - 1) =
      (2 - (frameAt w).parents.even.num, (frameAt w).parents.even.den - 2) +
        ((frameAt (conjWord w)).child.num - (frameAt (conjWord w)).child.den,
          (frameAt (conjWord w)).child.num + (frameAt (conjWord w)).child.den) +
        (-1 : ℤ) • (frameAt (conjWord w)).child.modifiedDeck.kernel := by
    rw [ChildFrame.child_modifiedDeck_kernel, hY, hb, hr']
    refine Prod.ext ?_ ?_ <;> simp only [Prod.mk_add_mk, Prod.smul_mk, smul_eq_mul] <;> ring
  -- the sheet is the conjugate value at Z(Y): A(Y) = G(Z Y) - h0(Z Y)
  have hsh : (frameAt w).sheetShift = 0 := by
    unfold ChildFrame.sheetShift
    rw [FLatticePaper.W1Seeds.phaseW_pos (frameAt w) hε]
    simp
  unfold ChildFrame.sheetA
  rw [hsh, sub_zero, FLatticePaper.W1ZeroStrip.quarterTurn_eq_sub, hQeq, hU, hV, hG0, hz]
  -- the lattice point of Z(Y) in closed form
  have hQ' : (2 - (frameAt w).parents.even.num, (frameAt w).parents.even.den - 2) +
        ((frameAt (conjWord w)).child.num - (frameAt (conjWord w)).child.den,
          (frameAt (conjWord w)).child.num + (frameAt (conjWord w)).child.den) +
        (-1 : ℤ) • (frameAt (conjWord w)).child.modifiedDeck.kernel =
      (2 - (frameAt w).parents.even.num - 3 * (frameAt w).parents.odd.num - (frameAt w).parents.odd.den,
        (frameAt w).parents.odd.den + (frameAt w).parents.odd.num + (frameAt w).parents.even.den - 2) := by
    rw [ChildFrame.child_modifiedDeck_kernel, hb, hr']
    refine Prod.ext ?_ ?_ <;> simp only [Prod.mk_add_mk, Prod.smul_mk, smul_eq_mul] <;> ring
  rw [hQ']
  -- the tGrade and coherent constant of the conjugate at Zv
  obtain ⟨-, -, -, -, hT⟩ := (frameAt (conjWord w)).child_facts
  have hcV := (frameAt (conjWord w)).coherentConstantV_eq
  rw [hT, hb, hr'] at hcV
  have e1 : 4 * harmonicGrid (2 - (frameAt w).parents.even.num, (frameAt w).parents.even.den - 2) =
      (2 - (frameAt w).parents.even.num) ^ 2 + 2 * (2 - (frameAt w).parents.even.num) * ((frameAt w).parents.even.den - 2) -
        ((frameAt w).parents.even.den - 2) ^ 2 - 2 * ((frameAt w).parents.even.den - 2) :=
    FLatticePaper.W1OddSeedId.four_harmonic_even _ (by simp only; omega)
  have e2 : 4 * harmonicGrid (2 - (frameAt w).parents.even.num - 3 * (frameAt w).parents.odd.num - (frameAt w).parents.odd.den,
        (frameAt w).parents.odd.den + (frameAt w).parents.odd.num + (frameAt w).parents.even.den - 2) =
      (2 - (frameAt w).parents.even.num - 3 * (frameAt w).parents.odd.num - (frameAt w).parents.odd.den) ^ 2 +
        2 * (2 - (frameAt w).parents.even.num - 3 * (frameAt w).parents.odd.num - (frameAt w).parents.odd.den) *
          ((frameAt w).parents.odd.den + (frameAt w).parents.odd.num + (frameAt w).parents.even.den - 2) -
        ((frameAt w).parents.odd.den + (frameAt w).parents.odd.num + (frameAt w).parents.even.den - 2) ^ 2 -
        2 * ((frameAt w).parents.odd.den + (frameAt w).parents.odd.num + (frameAt w).parents.even.den - 2) :=
    FLatticePaper.W1OddSeedId.four_harmonic_even _ (by simp only; omega)
  have hX : 4 * (harmonicGrid (2 - (frameAt w).parents.even.num, (frameAt w).parents.even.den - 2) +
      (frameAt (conjWord w)).tGrade (2 - (frameAt w).parents.even.num, (frameAt w).parents.even.den - 2) +
      (frameAt (conjWord w)).coherentConstantV -
      harmonicGrid (2 - (frameAt w).parents.even.num - 3 * (frameAt w).parents.odd.num - (frameAt w).parents.odd.den,
        (frameAt w).parents.odd.den + (frameAt w).parents.odd.num + (frameAt w).parents.even.den - 2) -
      ((frameAt w).parents.odd.num * ((frameAt w).parents.even.den - 1) -
        (frameAt w).parents.odd.den * ((frameAt w).parents.even.num - 2) - H)) = 0 := by
    unfold ChildFrame.tGrade
    rw [hb, hr']
    simp only []
    linear_combination e1 - e2 + 2 * hH + 2 * hcV
  have hX' := (mul_eq_zero.mp hX).resolve_left (by norm_num)
  have hOne := FLatticePaper.W1OddSeedId.offer_one_pos (frameAt w).parents.odd.den (frameAt w).parents.odd.num
    (frameAt w).parents.even.den (frameAt w).parents.even.num H hrel hH
  linarith

end FLatticePaper.W1OfferOne
