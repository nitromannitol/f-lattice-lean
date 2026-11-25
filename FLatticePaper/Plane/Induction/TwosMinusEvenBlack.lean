import FLatticePaper.Plane.Induction.TwosMinusEvenExcl
import FLatticePaper.Plane.Induction.TwosMinusRhoCases
import FLatticePaper.Plane.Induction.TwosBlackEven

/-! Twos flatness, sign `-1`, the even black centres: the horizontal drops. For an even black non-special tile point `p = (x, y)`
(not `EvenWhitePiece`), the horizontal neighbour `i` (left `(x-1, y)`, right `(x+1, y)`) has the same sign `-1` potential only
off the families of `TwosMinusEvenExcl` and the right families `(x, x)` and `(a, a)`; there the potentials differ, and off them
the rank of `i` is one less. The arithmetic is done on the region covers `bt_cover` of `bulkTreeM`, with the native boxes. -/

noncomputable section

namespace FLatticePaper.TwosEPolicy

open FLatticePaper FLatticePaper.Construction FLatticePaper.Induction Farey
open scoped Classical

/-- The right family `(x, x)` with `2 ≤ x`, `2x ≤ a+2`: the potential of `(x+1, x)` is one less than that of `(x, x)`. -/
theorem even_right_ne_c (k : ℕ) {x y : ℤ} (hy : y = x) (h2 : 2 ≤ x) (h3 : 2 * x ≤ 2 * (k : ℤ) + 6) :
    (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) (-1)
        (x + 1, y) ≠
      (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) (-1)
        (x, y) := by
  subst y
  have hNp : NativeT (2 * (k : ℤ) + 4) x x := by
    unfold NativeT
    omega
  have hNi : NativeT (2 * (k : ℤ) + 4) (x + 1) x := by
    unfold NativeT
    omega
  rw [chainM_native_level k hNi (by omega), chainM_native_level k hNp (by omega)]
  intro h
  have si := twosSlip_eq_zero_of k (z1 := x + 1 - 1) (z2 := x - 1) (by unfold TwosKey; omega)
    (by unfold TwosSlipZ0; omega) (by unfold TwosSlipZ2; omega)
  have sp := twosSlip_eq_zero_of k (z1 := x - 1) (z2 := x - 1) (by unfold TwosKey; omega)
    (by unfold TwosSlipZ0; omega) (by unfold TwosSlipZ2; omega)
  have di : TwosDelta k (x + 1 - 1) (x - 1) := by
    unfold TwosDelta
    omega
  have dp : ¬ TwosDelta k (x - 1) (x - 1) := by
    unfold TwosDelta
    omega
  rw [if_pos di, if_neg dp, si, sp] at h
  omega

/-- The right family `(a, a)`: the potential of `(a+1, a)` is one less than that of `(a, a)`. -/
theorem even_right_ne_d (k : ℕ) {x y : ℤ} (hx : x = 2 * (k : ℤ) + 4) (hy : y = x) :
    (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) (-1)
        (x + 1, y) ≠
      (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) (-1)
        (x, y) := by
  subst hx
  subst hy
  have hNp : NativeT (2 * (k : ℤ) + 4) (2 * (k : ℤ) + 4) (2 * (k : ℤ) + 4) := by
    unfold NativeT
    omega
  have hNi : NativeT (2 * (k : ℤ) + 4) (2 * (k : ℤ) + 4 + 1) (2 * (k : ℤ) + 4) := by
    unfold NativeT
    omega
  rw [chainM_native_level k hNi (by omega), chainM_native_level k hNp (by omega)]
  intro h
  have si := twosSlip_eq_one_of k (z1 := 2 * (k : ℤ) + 4 + 1 - 1) (z2 := 2 * (k : ℤ) + 4 - 1)
    (by unfold TwosKey; omega) (by unfold TwosSlipZ0; omega) (by unfold TwosSlipZ2; omega)
  have sp := twosSlip_eq_one_of k (z1 := 2 * (k : ℤ) + 4 - 1) (z2 := 2 * (k : ℤ) + 4 - 1)
    (by unfold TwosKey; omega) (by unfold TwosSlipZ0; omega) (by unfold TwosSlipZ2; omega)
  have di : TwosDelta k (2 * (k : ℤ) + 4 + 1 - 1) (2 * (k : ℤ) + 4 - 1) := by
    unfold TwosDelta
    omega
  have dp : ¬ TwosDelta k (2 * (k : ℤ) + 4 - 1) (2 * (k : ℤ) + 4 - 1) := by
    unfold TwosDelta
    omega
  rw [if_pos di, if_neg dp, si, sp] at h
  omega

/-! ### The native box. For an even point the strip branches of `NativeT` are excluded, so a native even point lies in a linear box. -/

theorem box_p {a x y : ℤ} (he : (x + y) % 2 = 0) (hN : NativeT a x y) :
    -1 ≤ x ∧ x ≤ a + 1 ∧ 1 ≤ y + 1 ∧ y + 1 ≤ 3 * a - 1 ∧ -1 ≤ y + 1 - (x) ∧ y + 1 - (x) ≤ 2 * a + 1 ∧ ¬((x = -1 ∧ y + 1 ≤ a + 1) ∨ (x = a + 1 ∧ 2 * a - 1 ≤ y + 1)) := by
  unfold NativeT at hN
  omega

theorem box_left_i {a x y : ℤ} (nc9 : ¬ (x = 0 ∧ y = 2 * a)) (hBp : -1 ≤ x ∧ x ≤ a + 1 ∧ 1 ≤ y + 1 ∧ y + 1 ≤ 3 * a - 1 ∧ -1 ≤ y + 1 - (x) ∧ y + 1 - (x) ≤ 2 * a + 1 ∧ ¬((x = -1 ∧ y + 1 ≤ a + 1) ∨ (x = a + 1 ∧ 2 * a - 1 ≤ y + 1)))
    (hN : NativeT a (x - 1) y) : -1 ≤ x - 1 ∧ x - 1 ≤ a + 1 ∧ 1 ≤ y + 1 ∧ y + 1 ≤ 3 * a - 1 ∧ -1 ≤ y + 1 - (x - 1) ∧ y + 1 - (x - 1) ≤ 2 * a + 1 ∧ ¬((x - 1 = -1 ∧ y + 1 ≤ a + 1) ∨ (x - 1 = a + 1 ∧ 2 * a - 1 ≤ y + 1)) := by
  unfold NativeT at hN
  omega

theorem box_right_i {a x y : ℤ} (hF : ¬ (x = a ∧ y = a - 2)) (hBp : -1 ≤ x ∧ x ≤ a + 1 ∧ 1 ≤ y + 1 ∧ y + 1 ≤ 3 * a - 1 ∧ -1 ≤ y + 1 - (x) ∧ y + 1 - (x) ≤ 2 * a + 1 ∧ ¬((x = -1 ∧ y + 1 ≤ a + 1) ∨ (x = a + 1 ∧ 2 * a - 1 ≤ y + 1)))
    (hN : NativeT a (x + 1) y) : -1 ≤ x + 1 ∧ x + 1 ≤ a + 1 ∧ 1 ≤ y + 1 ∧ y + 1 ≤ 3 * a - 1 ∧ -1 ≤ y + 1 - (x + 1) ∧ y + 1 - (x + 1) ≤ 2 * a + 1 ∧ ¬((x + 1 = -1 ∧ y + 1 ≤ a + 1) ∨ (x + 1 = a + 1 ∧ 2 * a - 1 ≤ y + 1)) := by
  unfold NativeT at hN
  omega

/-! ### The arithmetic of the drops. The region covers give the values; the boundary negations are kept only at the boundary. -/

set_option maxHeartbeats 400000 in
/-- The left bulk drop is arithmetic: off the families and the white and special clauses, the tree of `(x-1, y)` is below
that of `(x, y)`. -/
theorem left_arith_m {a x y : ℤ} {k : ℕ} (hk : a = 2 * (k : ℤ) + 4) (he2 : a % 2 = 0) (he : (x + y) % 2 = 0)
    (hBp : -1 ≤ x ∧ x ≤ a + 1 ∧ 1 ≤ y + 1 ∧ y + 1 ≤ 3 * a - 1 ∧ -1 ≤ y + 1 - (x) ∧ y + 1 - (x) ≤ 2 * a + 1 ∧ ¬((x = -1 ∧ y + 1 ≤ a + 1) ∨ (x = a + 1 ∧ 2 * a - 1 ≤ y + 1))) (hBi : -1 ≤ x - 1 ∧ x - 1 ≤ a + 1 ∧ 1 ≤ y + 1 ∧ y + 1 ≤ 3 * a - 1 ∧ -1 ≤ y + 1 - (x - 1) ∧ y + 1 - (x - 1) ≤ 2 * a + 1 ∧ ¬((x - 1 = -1 ∧ y + 1 ≤ a + 1) ∨ (x - 1 = a + 1 ∧ 2 * a - 1 ≤ y + 1)))
    (hF : ¬ (x = a ∧ y = a - 2)) (hi2 : ¬ (x - 1 = a ∧ y = 2 * a - 1)) (nc9 : ¬ (x = 0 ∧ y = 2 * a))
    (nc4 : ¬ (y - x = -2 ∧ 2 ≤ x ∧ x ≤ a - 1)) (nc8 : ¬ (y - x = a - 2 ∧ 2 ≤ x ∧ x ≤ a))
    (fa : ¬ (x = 0 ∧ 2 * (k : ℤ) + 6 ≤ y ∧ 2 * y ≤ 3 * a)) (fb : ¬ (x = 1 ∧ 1 ≤ y ∧ 2 * y ≤ a ∧ y % 2 = 1))
    (hW : ¬ (x = a + 1 ∧ a - 1 ≤ y ∧ y ≤ 2 * a - 3)) :
    bulkTreeM a (x - 1) y < bulkTreeM a x y := by
  have ha : (4 : ℤ) ≤ a := by omega
  by_cases hb : x = 0 ∨ x = 1 ∨ x = a ∨ x = a + 1
  · rcases bt_cover a (x) y ha with h | h | h | h | h | h | h | h | h | h <;>
    rcases bt_cover a (x - 1) y ha with h' | h' | h' | h' | h' | h' | h' | h' | h' | h' <;>
    rw [h.1, h'.1] <;> omega
  · clear hF hi2 nc9 fa fb
    rcases bt_cover a (x) y ha with h | h | h | h | h | h | h | h | h | h <;>
      rcases bt_cover a (x - 1) y ha with h' | h' | h' | h' | h' | h' | h' | h' | h' | h' <;>
      rw [h.1, h'.1] <;> omega

/-- The free left drop at column `x = 1`: the sign `-1` free value of `(0, y)` is below the bulk value of `(1, y)`. -/
theorem free_arith_x1 {a x y : ℤ} (hx : x = 1) (he2 : a % 2 = 0) (he : (x + y) % 2 = 0)
    (hy0 : 0 ≤ y) (hya : y < a) (fb : ¬ (x = 1 ∧ 1 ≤ y ∧ 2 * y ≤ a ∧ y % 2 = 1)) :
    (if y = 0 then 5 else if y < a then 2 * a + 3 - 2 * y - y % 2 else if y = a then 2
      else if y = a + 1 then 1 else 2 * a + 4 - 2 * (y - a) + (y - a) % 2) < bulkTreeM a x y := by
  subst hx
  unfold bulkTreeM
  split_ifs <;> omega

/-- The free left drop at column `x = 0`: the sign `-1` free value of `(-1, y)` is below the bulk value of `(0, y)`. -/
theorem free_arith_x0 {a x y : ℤ} {k : ℕ} (hk : a = 2 * (k : ℤ) + 4) (hx : x = 0) (he2 : a % 2 = 0)
    (he : (x + y) % 2 = 0) (hy0 : a ≤ y) (hya : y < 2 * a)
    (fa : ¬ (x = 0 ∧ 2 * (k : ℤ) + 6 ≤ y ∧ 2 * y ≤ 3 * a)) :
    (if y = 0 then 5 else if y < a then 2 * a + 3 - 2 * y - y % 2 else if y = a then 2
      else if y = a + 1 then 1 else 2 * a + 4 - 2 * (y - a) + (y - a) % 2) < bulkTreeM a x y := by
  subst hx
  unfold bulkTreeM
  split_ifs <;> omega

/-- The left free V drop is arithmetic: the V value of `(x-1, y)` is below the bulk value of `(x, y)`, split by the column
`x = 1` (where `(x-1, y)` is the V site `(0, y)`) and `x = 0` (where it is `(-1, y)`). -/
theorem left_free_arith_m {a x y : ℤ} {k : ℕ} (hk : a = 2 * (k : ℤ) + 4) (he2 : a % 2 = 0) (he : (x + y) % 2 = 0)
    (hV : FreeVSite a (x - 1) y)
    (fa : ¬ (x = 0 ∧ 2 * (k : ℤ) + 6 ≤ y ∧ 2 * y ≤ 3 * a)) (fb : ¬ (x = 1 ∧ 1 ≤ y ∧ 2 * y ≤ a ∧ y % 2 = 1)) :
    freeV a (-1) (x - 1) y < bulkTreeM a x y := by
  unfold FreeVSite at hV
  rw [freeV_minus_eq]
  rcases hV with ⟨hx, hy0, hya⟩ | ⟨hx, hy0, hya⟩
  · exact free_arith_x1 (by omega) he2 he hy0 hya fb
  · exact free_arith_x0 hk (by omega) he2 he (by omega) (by omega) fa

set_option maxHeartbeats 400000 in
/-- The right bulk drop is arithmetic: off the families and the white and special clauses, the tree of `(x+1, y)` is below
that of `(x, y)`. -/
theorem right_arith_m {a x y : ℤ} {k : ℕ} (hk : a = 2 * (k : ℤ) + 4) (he2 : a % 2 = 0) (he : (x + y) % 2 = 0)
    (hBp : -1 ≤ x ∧ x ≤ a + 1 ∧ 1 ≤ y + 1 ∧ y + 1 ≤ 3 * a - 1 ∧ -1 ≤ y + 1 - (x) ∧ y + 1 - (x) ≤ 2 * a + 1 ∧ ¬((x = -1 ∧ y + 1 ≤ a + 1) ∨ (x = a + 1 ∧ 2 * a - 1 ≤ y + 1))) (hBi : -1 ≤ x + 1 ∧ x + 1 ≤ a + 1 ∧ 1 ≤ y + 1 ∧ y + 1 ≤ 3 * a - 1 ∧ -1 ≤ y + 1 - (x + 1) ∧ y + 1 - (x + 1) ≤ 2 * a + 1 ∧ ¬((x + 1 = -1 ∧ y + 1 ≤ a + 1) ∨ (x + 1 = a + 1 ∧ 2 * a - 1 ≤ y + 1)))
    (hp1 : ¬ (x = a ∧ y = 2 * a - 2)) (hp2 : ¬ (x = a ∧ y = 2 * a - 1)) (hp3 : ¬ (x = a + 1 ∧ y = a - 2))
    (hF : ¬ (x = a ∧ y = a - 2)) (hi2 : ¬ (x + 1 = a ∧ y = 2 * a - 1))
    (nc3 : ¬ (x = 0 ∧ 0 ≤ y ∧ y ≤ a)) (nc7 : ¬ (y - x = a ∧ 0 ≤ x ∧ x ≤ a - 2))
    (fc : ¬ (y = x ∧ 2 ≤ x ∧ 2 * x ≤ 2 * (k : ℤ) + 6)) (fd : ¬ (x = a ∧ y = a)) :
    bulkTreeM a (x + 1) y < bulkTreeM a x y := by
  have ha : (4 : ℤ) ≤ a := by omega
  by_cases hb : x = 0 ∨ x = a - 1 ∨ x = a ∨ x = a + 1
  · rcases bt_cover a (x) y ha with h | h | h | h | h | h | h | h | h | h <;>
    rcases bt_cover a (x + 1) y ha with h' | h' | h' | h' | h' | h' | h' | h' | h' | h' <;>
    rw [h.1, h'.1] <;> omega
  · clear hp1 hp2 hp3 hF hi2 nc3 fd
    rcases bt_cover a (x) y ha with h | h | h | h | h | h | h | h | h | h <;>
      rcases bt_cover a (x + 1) y ha with h' | h' | h' | h' | h' | h' | h' | h' | h' | h' <;>
      rw [h.1, h'.1] <;> omega

set_option maxHeartbeats 400000 in
/-- **The even black left drop.** For an even black non-special tile point `p = (x, y)`, the left neighbour `(x-1, y)` has
rank one less when the two sign `-1` potentials agree. -/
theorem even_left_m {a x y : ℤ} {k : ℕ} (hk : a = 2 * (k : ℤ) + 4) (hp : TwosTile a (x, y))
    (hp2 : ¬ (x = a ∧ y = 2 * a - 1))
    (hF : ¬ (x = a ∧ y = a - 2)) (hB : ¬ EvenWhitePiece a x y) (he : (x + y) % 2 = 0)
    (hi : TwosTile a (x - 1, y)) (hi2 : ¬ (x - 1 = a ∧ y = 2 * a - 1))
    (hΦ : (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) (-1)
        (x - 1, y) =
      (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) (-1)
        (x, y)) :
    rhoTwos a (-1) (x - 1, y) < rhoTwos a (-1) (x, y) := by
  have ha : (4 : ℤ) ≤ a := by omega
  have he2 : a % 2 = 0 := by omega
  have hNp : NativeT a x y := ((tile_iff_lin _ _ _).mp hp).1
  have hFp : ¬ FreeSite a x y := by
    unfold EvenWhitePiece at hB
    unfold FreeSite FreeHSite FreeVSite
    omega
  have nc9 : ¬ (x = 0 ∧ y = 2 * a) := fun h =>
    hB (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))
  have nc4 : ¬ (y - x = -2 ∧ 2 ≤ x ∧ x ≤ a - 1) := fun h => hB (Or.inr (Or.inr (Or.inr (Or.inl h))))
  have nc8 : ¬ (y - x = a - 2 ∧ 2 ≤ x ∧ x ≤ a) :=
    fun h => hB (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))
  have hW : ¬ (x = a + 1 ∧ a - 1 ≤ y ∧ y ≤ 2 * a - 3) := fun h =>
    hB (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  clear hB
  by_cases fa : x = 0 ∧ 2 * (k : ℤ) + 6 ≤ y ∧ 2 * y ≤ 3 * a
  · exact absurd hΦ (even_left_ne_a k fa.1 (by omega) (by omega))
  by_cases fb : x = 1 ∧ 1 ≤ y ∧ 2 * y ≤ a ∧ y % 2 = 1
  · exact absurd hΦ (even_left_ne_b k fb.1 fb.2.1 (by omega) fb.2.2.2)
  have hBp := box_p he hNp
  rw [rho_bulk_eq_m ha he2 hp hFp hp2]
  by_cases hFi : FreeSite a (x - 1) y
  · have hH : ¬ FreeHSite a (x - 1) y := by
      intro hH
      unfold FreeHSite at hH
      rcases hH with h1 | h1 | h1
      · exact hFp (Or.inl (by unfold FreeHSite; omega))
      · omega
      · unfold NativeT at hNp
        omega
    have hV : FreeVSite a (x - 1) y := by
      unfold FreeSite at hFi
      rcases hFi with h | h
      · exact absurd h hH
      · exact h
    rw [rhoTwos_tile_freeV_eta (-1) ha he2 hi hH hV]
    exact left_free_arith_m hk he2 he hV fa fb
  · rw [rho_bulk_eq_m ha he2 hi hFi hi2]
    have hBi := box_left_i nc9 hBp ((tile_iff_lin _ _ _).mp hi).1
    exact left_arith_m hk he2 he hBp hBi hF hi2 nc9 nc4 nc8 fa fb hW

set_option maxHeartbeats 400000 in
/-- **The even black right drop.** For an even black non-special tile point `p = (x, y)`, the right neighbour `(x+1, y)` has
rank one less when the two sign `-1` potentials agree. -/
theorem even_right_m {a x y : ℤ} {k : ℕ} (hk : a = 2 * (k : ℤ) + 4) (hp : TwosTile a (x, y))
    (hp1 : ¬ (x = a ∧ y = 2 * a - 2)) (hp2 : ¬ (x = a ∧ y = 2 * a - 1)) (hp3 : ¬ (x = a + 1 ∧ y = a - 2))
    (hF : ¬ (x = a ∧ y = a - 2)) (hB : ¬ EvenWhitePiece a x y) (he : (x + y) % 2 = 0)
    (hi : TwosTile a (x + 1, y)) (hi2 : ¬ (x + 1 = a ∧ y = 2 * a - 1))
    (hΦ : (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) (-1)
        (x + 1, y) =
      (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) (-1)
        (x, y)) :
    rhoTwos a (-1) (x + 1, y) < rhoTwos a (-1) (x, y) := by
  have ha : (4 : ℤ) ≤ a := by omega
  have he2 : a % 2 = 0 := by omega
  have hNp : NativeT a x y := ((tile_iff_lin _ _ _).mp hp).1
  have hFp : ¬ FreeSite a x y := by
    unfold EvenWhitePiece at hB
    unfold FreeSite FreeHSite FreeVSite
    omega
  have nc3 : ¬ (x = 0 ∧ 0 ≤ y ∧ y ≤ a) := fun h => hB (Or.inr (Or.inr (Or.inl h)))
  have nc7 : ¬ (y - x = a ∧ 0 ≤ x ∧ x ≤ a - 2) :=
    fun h => hB (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
  have hFi : ¬ FreeSite a (x + 1) y := by
    intro hF'
    rcases hF' with hH | hV
    · unfold FreeHSite at hH
      rcases hH with h1 | h1 | h1
      · unfold EvenWhitePiece at hB
        exact hB (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)))
      · omega
      · exact hF ⟨by omega, by omega⟩
    · unfold FreeVSite at hV
      unfold NativeT at hNp
      omega
  clear hB
  by_cases fc : y = x ∧ 2 ≤ x ∧ 2 * x ≤ 2 * (k : ℤ) + 6
  · exact absurd hΦ (even_right_ne_c k fc.1 fc.2.1 fc.2.2)
  by_cases fd : x = a ∧ y = a
  · exact absurd hΦ (even_right_ne_d k (by omega) (by omega))
  have hBp := box_p he hNp
  have hBi := box_right_i hF hBp ((tile_iff_lin _ _ _).mp hi).1
  rw [rho_bulk_eq_m ha he2 hp hFp hp2, rho_bulk_eq_m ha he2 hi hFi hi2]
  exact right_arith_m hk he2 he hBp hBi hp1 hp2 hp3 hF hi2 nc3 nc7 fc fd

end FLatticePaper.TwosEPolicy
