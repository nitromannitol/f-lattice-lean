import FLatticePaper.Plane.Induction.TwosChainMono1

-- TwosChainMono: part 2 of 2; declarations from even_left_s1_gt to twosChain_nonincreasing.
namespace FLatticePaper.TwosEPolicy
open FLatticePaper FLatticePaper.Construction FLatticePaper.Induction Farey
open scoped Classical

/-- Strip 1 of `even_left_chain`, the range `y − x > 2a` (impossible in the box). -/
theorem even_left_s1_gt
    (k : ℕ) {x y : ℤ} (hn : NativeT (2 * (k : ℤ) + 4) x y) (hab : 1 ≤ x ∧ x ≤ 2 * (k : ℤ) + 3)
    (ht : 2 * (2 * (k : ℤ) + 4) < y - x) :
    (¬ TwosDelta k (x + 1 + 0) (y + 1 + 0) ∨ TwosDelta k (x - 1 + 1 + 0) (y + 1 + 0)) ∨
      twosSlip k (x - 1, y) < twosSlip k (x, y) := by
  exfalso
  unfold NativeT at hn
  rcases hn with ⟨⟨g1, g2, g3, g4, g5, g6⟩, g7⟩ | g8 | g9 <;> omega

/-- Strip 1 of `even_left_chain`: the dispatcher over the ranges of `y − x`. -/
theorem even_left_s1 (k : ℕ) {x y : ℤ} (hn : NativeT (2 * (k : ℤ) + 4) x y) (hp : (x + y) % 2 = 0)
    (n1 : ¬ (y - x = 2 * (2 * (k : ℤ) + 4) ∧ 2 * (2 * (k : ℤ) + 4) + 1 ≤ y ∧ y ≤ 3 * (2 * (k : ℤ) + 4) - 2))
    (n2 : ¬ (x = -1 ∧ (2 * (k : ℤ) + 4) + 1 ≤ y ∧ y ≤ 2 * (2 * (k : ℤ) + 4) - 1))
    (n3 : ¬ (x = 0 ∧ 0 ≤ y ∧ y ≤ (2 * (k : ℤ) + 4)))
    (n4 : ¬ (y - x = -2 ∧ 0 ≤ y ∧ y ≤ (2 * (k : ℤ) + 4) - 3))
    (n5 : ¬ (x = (2 * (k : ℤ) + 4) + 1 ∧ (2 * (k : ℤ) + 4) - 1 ≤ y ∧ y ≤ 2 * (2 * (k : ℤ) + 4) - 3))
    (n6 : ¬ (x = (2 * (k : ℤ) + 4) ∧ 2 * (2 * (k : ℤ) + 4) - 2 ≤ y ∧ y ≤ 3 * (2 * (k : ℤ) + 4) - 2))
    (n7 : ¬ (y - x = (2 * (k : ℤ) + 4) ∧ 0 ≤ x ∧ x ≤ (2 * (k : ℤ) + 4) - 2))
    (n8 : ¬ (y - x = (2 * (k : ℤ) + 4) - 2 ∧ 2 ≤ x ∧ x ≤ (2 * (k : ℤ) + 4)))
    (n9 : ¬ (x = 0 ∧ y = 2 * (2 * (k : ℤ) + 4)))
    (n10 : ¬ (x = (2 * (k : ℤ) + 4) ∧ y = (2 * (k : ℤ) + 4) - 2))
    (hab : 1 ≤ x ∧ x ≤ 2 * (k : ℤ) + 3) :
    twosSlip k (x - 1, y) + twosP k (x - 1 + 1, y + 1) ≤ twosSlip k (x, y) + twosP k (x + 1, y + 1) := by
  have hk1 : TwosKey (2 * (k : ℤ) + 4) x y := twosKey_of_native hn
  have hk2 := (even_left_key k hn hp n1 n2 n3 n4 n5 n6 n7 n8 n9 n10).1
  have hcl := even_left_D k hn hp n1 n2 n3 n4 n5 n6 n7 n8 n9 n10
  have hD := twosSlip_le_of_bands k (x := (x, y)) (y := (x - 1, y)) hk1 hk2 hcl.1 hcl.2
  refine twosChain_le_tr k 0 0 0 (twosP_shift0 k) hD ?_ ?_ ?_
  · clear n2 n3 n4 n5 n6 n7 n8 n9 n10 hD hcl hk1 hk2
    unfold TwosKey
    (try dsimp only)
    unfold NativeT at hn
    rcases hn with ⟨⟨g1, g2, g3, g4, g5, g6⟩, g7⟩ | g8 | g9 <;> omega
  · clear n2 n3 n4 n5 n6 n7 n8 n9 n10 hD hcl hk1 hk2
    unfold TwosKey
    (try dsimp only)
    unfold NativeT at hn
    rcases hn with ⟨⟨g1, g2, g3, g4, g5, g6⟩, g7⟩ | g8 | g9 <;> omega
  · rcases lt_trichotomy (y - x) (2 * (k : ℤ) + 4 - 2) with ht | ht | ht
    · exact even_left_s1_lt k hn hp hab hk1 hk2 ht
    · by_cases hx2 : 2 ≤ x
      · exact even_left_s1_eq2 k hab hx2 ht n8
      · exact even_left_s1_eq1 k hn hp hab hk1 hk2 hx2 ht
    · rcases lt_trichotomy (y - x) (2 * (2 * (k : ℤ) + 4)) with ht2 | ht2 | ht2
      · exact even_left_s1_mid k hn hp hab hk1 hk2 ht
      · exact even_left_s1_top k hn hab ht2 n1
      · exact even_left_s1_gt k hn hab ht2
set_option maxHeartbeats 400000 in
/-- Strip 2 of `even_left_chain`. -/
theorem even_left_s2 (k : ℕ) {x y : ℤ} (hn : NativeT (2 * (k : ℤ) + 4) x y) (hp : (x + y) % 2 = 0)
    (n1 : ¬ (y - x = 2 * (2 * (k : ℤ) + 4) ∧ 2 * (2 * (k : ℤ) + 4) + 1 ≤ y ∧ y ≤ 3 * (2 * (k : ℤ) + 4) - 2))
    (n2 : ¬ (x = -1 ∧ (2 * (k : ℤ) + 4) + 1 ≤ y ∧ y ≤ 2 * (2 * (k : ℤ) + 4) - 1))
    (n3 : ¬ (x = 0 ∧ 0 ≤ y ∧ y ≤ (2 * (k : ℤ) + 4)))
    (n4 : ¬ (y - x = -2 ∧ 0 ≤ y ∧ y ≤ (2 * (k : ℤ) + 4) - 3))
    (n5 : ¬ (x = (2 * (k : ℤ) + 4) + 1 ∧ (2 * (k : ℤ) + 4) - 1 ≤ y ∧ y ≤ 2 * (2 * (k : ℤ) + 4) - 3))
    (n6 : ¬ (x = (2 * (k : ℤ) + 4) ∧ 2 * (2 * (k : ℤ) + 4) - 2 ≤ y ∧ y ≤ 3 * (2 * (k : ℤ) + 4) - 2))
    (n7 : ¬ (y - x = (2 * (k : ℤ) + 4) ∧ 0 ≤ x ∧ x ≤ (2 * (k : ℤ) + 4) - 2))
    (n8 : ¬ (y - x = (2 * (k : ℤ) + 4) - 2 ∧ 2 ≤ x ∧ x ≤ (2 * (k : ℤ) + 4)))
    (n9 : ¬ (x = 0 ∧ y = 2 * (2 * (k : ℤ) + 4)))
    (n10 : ¬ (x = (2 * (k : ℤ) + 4) ∧ y = (2 * (k : ℤ) + 4) - 2))
    (h0 : x = 2 * (k : ℤ) + 4) :
    twosSlip k (x - 1, y) + twosP k (x - 1 + 1, y + 1) ≤ twosSlip k (x, y) + twosP k (x + 1, y + 1) := by
  obtain ⟨m, hm⟩ : ∃ m, y = 2 * m - x := ⟨(x + y) / 2, by omega⟩
  have hk1 : TwosKey (2 * (k : ℤ) + 4) x y := twosKey_of_native hn
  have hk2 := (even_left_key k hn hp n1 n2 n3 n4 n5 n6 n7 n8 n9 n10).1
  have hcl := even_left_D k hn hp n1 n2 n3 n4 n5 n6 n7 n8 n9 n10
  have hD := twosSlip_le_of_bands k (x := (x, y)) (y := (x - 1, y)) hk1 hk2 hcl.1 hcl.2
  have v1 := twos_slip_value k hk1
  have v2 := twos_slip_value k hk2
  subst h0
  refine twosChain_le_tr k 0 0 0 (twosP_shift0 k) hD ?_ ?_ ?_
  · clear n2 n3 n4 n5 n7 n9 v1 v2 hD hcl hk1 hk2; unfold TwosKey; (try dsimp only); unfold NativeT at hn; (rcases hn with ⟨⟨g1, g2, g3, g4, g5, g6⟩, g7⟩ | g8 | g9 <;> omega)
  · clear n2 n3 n4 n5 n7 n9 v1 v2 hD hcl hk1 hk2; unfold TwosKey; (try dsimp only); unfold NativeT at hn; (rcases hn with ⟨⟨g1, g2, g3, g4, g5, g6⟩, g7⟩ | g8 | g9 <;> omega)
  · clear n2 n3 n4 n5 n7 n9 hD hcl hk1 hk2
    (try unfold TwosSlipZ0 at *); (try unfold TwosSlipZ2 at *); unfold TwosDelta; (try dsimp only); unfold NativeT at hn; (rcases hn with ⟨⟨g1, g2, g3, g4, g5, g6⟩, g7⟩ | g8 | g9 <;> omega)

set_option maxHeartbeats 400000 in
/-- Strip 3 of `even_left_chain`. -/
theorem even_left_s3 (k : ℕ) {x y : ℤ} (hn : NativeT (2 * (k : ℤ) + 4) x y) (hp : (x + y) % 2 = 0)
    (n1 : ¬ (y - x = 2 * (2 * (k : ℤ) + 4) ∧ 2 * (2 * (k : ℤ) + 4) + 1 ≤ y ∧ y ≤ 3 * (2 * (k : ℤ) + 4) - 2))
    (n2 : ¬ (x = -1 ∧ (2 * (k : ℤ) + 4) + 1 ≤ y ∧ y ≤ 2 * (2 * (k : ℤ) + 4) - 1))
    (n3 : ¬ (x = 0 ∧ 0 ≤ y ∧ y ≤ (2 * (k : ℤ) + 4)))
    (n4 : ¬ (y - x = -2 ∧ 0 ≤ y ∧ y ≤ (2 * (k : ℤ) + 4) - 3))
    (n5 : ¬ (x = (2 * (k : ℤ) + 4) + 1 ∧ (2 * (k : ℤ) + 4) - 1 ≤ y ∧ y ≤ 2 * (2 * (k : ℤ) + 4) - 3))
    (n6 : ¬ (x = (2 * (k : ℤ) + 4) ∧ 2 * (2 * (k : ℤ) + 4) - 2 ≤ y ∧ y ≤ 3 * (2 * (k : ℤ) + 4) - 2))
    (n7 : ¬ (y - x = (2 * (k : ℤ) + 4) ∧ 0 ≤ x ∧ x ≤ (2 * (k : ℤ) + 4) - 2))
    (n8 : ¬ (y - x = (2 * (k : ℤ) + 4) - 2 ∧ 2 ≤ x ∧ x ≤ (2 * (k : ℤ) + 4)))
    (n9 : ¬ (x = 0 ∧ y = 2 * (2 * (k : ℤ) + 4)))
    (n10 : ¬ (x = (2 * (k : ℤ) + 4) ∧ y = (2 * (k : ℤ) + 4) - 2))
    (h0 : x = 2 * (k : ℤ) + 5) :
    twosSlip k (x - 1, y) + twosP k (x - 1 + 1, y + 1) ≤ twosSlip k (x, y) + twosP k (x + 1, y + 1) := by
  obtain ⟨m, hm⟩ : ∃ m, y = 2 * m - x := ⟨(x + y) / 2, by omega⟩
  have hk1 : TwosKey (2 * (k : ℤ) + 4) x y := twosKey_of_native hn
  have hk2 := (even_left_key k hn hp n1 n2 n3 n4 n5 n6 n7 n8 n9 n10).1
  have hcl := even_left_D k hn hp n1 n2 n3 n4 n5 n6 n7 n8 n9 n10
  have hD := twosSlip_le_of_bands k (x := (x, y)) (y := (x - 1, y)) hk1 hk2 hcl.1 hcl.2
  have v1 := twos_slip_value k hk1
  have v2 := twos_slip_value k hk2
  subst h0
  refine twosChain_le_tr k 0 0 0 (twosP_shift0 k) hD ?_ ?_ ?_
  · clear n2 n3 n6 n7 n8 n9 n10 v1 v2 hD hcl hk1 hk2; unfold TwosKey; (try dsimp only); unfold NativeT at hn; (rcases hn with ⟨⟨g1, g2, g3, g4, g5, g6⟩, g7⟩ | g8 | g9 <;> omega)
  · clear n2 n3 n6 n7 n8 n9 n10 v1 v2 hD hcl hk1 hk2; unfold TwosKey; (try dsimp only); unfold NativeT at hn; (rcases hn with ⟨⟨g1, g2, g3, g4, g5, g6⟩, g7⟩ | g8 | g9 <;> omega)
  · clear n2 n3 n6 n7 n8 n9 n10 hD hcl hk1 hk2
    (try unfold TwosSlipZ0 at *); (try unfold TwosSlipZ2 at *); unfold TwosDelta; (try dsimp only); unfold NativeT at hn; (rcases hn with ⟨⟨g1, g2, g3, g4, g5, g6⟩, g7⟩ | g8 | g9 <;> omega)

set_option maxHeartbeats 400000 in
/-- The left input of an even black centre: the chain claim, split into the strips of `x`. -/
theorem even_left_chain (k : ℕ) {x y : ℤ} (hn : NativeT (2 * (k : ℤ) + 4) x y) (hp : (x + y) % 2 = 0)
    (n1 : ¬ (y - x = 2 * (2 * (k : ℤ) + 4) ∧ 2 * (2 * (k : ℤ) + 4) + 1 ≤ y ∧ y ≤ 3 * (2 * (k : ℤ) + 4) - 2))
    (n2 : ¬ (x = -1 ∧ (2 * (k : ℤ) + 4) + 1 ≤ y ∧ y ≤ 2 * (2 * (k : ℤ) + 4) - 1))
    (n3 : ¬ (x = 0 ∧ 0 ≤ y ∧ y ≤ (2 * (k : ℤ) + 4)))
    (n4 : ¬ (y - x = -2 ∧ 0 ≤ y ∧ y ≤ (2 * (k : ℤ) + 4) - 3))
    (n5 : ¬ (x = (2 * (k : ℤ) + 4) + 1 ∧ (2 * (k : ℤ) + 4) - 1 ≤ y ∧ y ≤ 2 * (2 * (k : ℤ) + 4) - 3))
    (n6 : ¬ (x = (2 * (k : ℤ) + 4) ∧ 2 * (2 * (k : ℤ) + 4) - 2 ≤ y ∧ y ≤ 3 * (2 * (k : ℤ) + 4) - 2))
    (n7 : ¬ (y - x = (2 * (k : ℤ) + 4) ∧ 0 ≤ x ∧ x ≤ (2 * (k : ℤ) + 4) - 2))
    (n8 : ¬ (y - x = (2 * (k : ℤ) + 4) - 2 ∧ 2 ≤ x ∧ x ≤ (2 * (k : ℤ) + 4)))
    (n9 : ¬ (x = 0 ∧ y = 2 * (2 * (k : ℤ) + 4)))
    (n10 : ¬ (x = (2 * (k : ℤ) + 4) ∧ y = (2 * (k : ℤ) + 4) - 2)) :
    twosSlip k (x - 1, y) + twosP k (x - 1 + 1, y + 1) ≤ twosSlip k (x, y) + twosP k (x + 1, y + 1) := by
  have hs : x = 0 ∨ (1 ≤ x ∧ x ≤ 2 * (k : ℤ) + 3) ∨ x = 2 * (k : ℤ) + 4 ∨ x = 2 * (k : ℤ) + 5 := by
    clear n1 n3 n4 n5 n6 n7 n8 n9 n10
    unfold NativeT at hn
    rcases hn with ⟨⟨g1, g2, g3, g4, g5, g6⟩, g7⟩ | g8 | g9 <;> omega
  rcases hs with h0 | hab | h0 | h0
  · exact even_left_s0 k hn hp n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 h0
  · exact even_left_s1 k hn hp n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 hab
  · exact even_left_s2 k hn hp n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 h0
  · exact even_left_s3 k hn hp n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 h0

set_option maxHeartbeats 400000 in
/-- Strip 0 of `even_right_chain`. -/
theorem even_right_s0 (k : ℕ) {x y : ℤ} (hn : NativeT (2 * (k : ℤ) + 4) x y) (hp : (x + y) % 2 = 0)
    (n1 : ¬ (y - x = 2 * (2 * (k : ℤ) + 4) ∧ 2 * (2 * (k : ℤ) + 4) + 1 ≤ y ∧ y ≤ 3 * (2 * (k : ℤ) + 4) - 2))
    (n2 : ¬ (x = -1 ∧ (2 * (k : ℤ) + 4) + 1 ≤ y ∧ y ≤ 2 * (2 * (k : ℤ) + 4) - 1))
    (n3 : ¬ (x = 0 ∧ 0 ≤ y ∧ y ≤ (2 * (k : ℤ) + 4)))
    (n4 : ¬ (y - x = -2 ∧ 0 ≤ y ∧ y ≤ (2 * (k : ℤ) + 4) - 3))
    (n5 : ¬ (x = (2 * (k : ℤ) + 4) + 1 ∧ (2 * (k : ℤ) + 4) - 1 ≤ y ∧ y ≤ 2 * (2 * (k : ℤ) + 4) - 3))
    (n6 : ¬ (x = (2 * (k : ℤ) + 4) ∧ 2 * (2 * (k : ℤ) + 4) - 2 ≤ y ∧ y ≤ 3 * (2 * (k : ℤ) + 4) - 2))
    (n7 : ¬ (y - x = (2 * (k : ℤ) + 4) ∧ 0 ≤ x ∧ x ≤ (2 * (k : ℤ) + 4) - 2))
    (n8 : ¬ (y - x = (2 * (k : ℤ) + 4) - 2 ∧ 2 ≤ x ∧ x ≤ (2 * (k : ℤ) + 4)))
    (n9 : ¬ (x = 0 ∧ y = 2 * (2 * (k : ℤ) + 4)))
    (n10 : ¬ (x = (2 * (k : ℤ) + 4) ∧ y = (2 * (k : ℤ) + 4) - 2))
    (h0 : x = 0) :
    twosSlip k (x + 1, y) + twosP k (x + 1 + 1, y + 1) ≤ twosSlip k (x, y) + twosP k (x + 1, y + 1) := by
  obtain ⟨m, hm⟩ : ∃ m, y = 2 * m - x := ⟨(x + y) / 2, by omega⟩
  have hk1 : TwosKey (2 * (k : ℤ) + 4) x y := twosKey_of_native hn
  have hk2 := (even_right_key k hn hp n1 n2 n3 n4 n5 n6 n7 n8 n9 n10).1
  have hcl := even_right_D k hn hp n1 n2 n3 n4 n5 n6 n7 n8 n9 n10
  have hD := twosSlip_le_of_bands k (x := (x, y)) (y := (x + 1, y)) hk1 hk2 hcl.1 hcl.2
  have v1 := twos_slip_value k hk1
  have v2 := twos_slip_value k hk2
  subst h0
  refine twosChain_le_tr k 0 0 0 (twosP_shift0 k) hD ?_ ?_ ?_
  · clear n2 n5 n6 n8 n10 v1 v2 hD hcl hk1 hk2; unfold TwosKey; (try dsimp only); unfold NativeT at hn; (rcases hn with ⟨⟨g1, g2, g3, g4, g5, g6⟩, g7⟩ | g8 | g9 <;> omega)
  · clear n2 n5 n6 n8 n10 v1 v2 hD hcl hk1 hk2; unfold TwosKey; (try dsimp only); unfold NativeT at hn; (rcases hn with ⟨⟨g1, g2, g3, g4, g5, g6⟩, g7⟩ | g8 | g9 <;> omega)
  · clear n2 n5 n6 n8 n10 hD hcl hk1 hk2
    (try unfold TwosSlipZ0 at *); (try unfold TwosSlipZ2 at *); unfold TwosDelta; (try dsimp only); unfold NativeT at hn; (rcases hn with ⟨⟨g1, g2, g3, g4, g5, g6⟩, g7⟩ | g8 | g9 <;> omega)

set_option maxHeartbeats 400000 in
/-- Strip 1 of `even_right_chain`. -/
theorem even_right_s1 (k : ℕ) {x y : ℤ} (hn : NativeT (2 * (k : ℤ) + 4) x y) (hp : (x + y) % 2 = 0)
    (n1 : ¬ (y - x = 2 * (2 * (k : ℤ) + 4) ∧ 2 * (2 * (k : ℤ) + 4) + 1 ≤ y ∧ y ≤ 3 * (2 * (k : ℤ) + 4) - 2))
    (n2 : ¬ (x = -1 ∧ (2 * (k : ℤ) + 4) + 1 ≤ y ∧ y ≤ 2 * (2 * (k : ℤ) + 4) - 1))
    (n3 : ¬ (x = 0 ∧ 0 ≤ y ∧ y ≤ (2 * (k : ℤ) + 4)))
    (n4 : ¬ (y - x = -2 ∧ 0 ≤ y ∧ y ≤ (2 * (k : ℤ) + 4) - 3))
    (n5 : ¬ (x = (2 * (k : ℤ) + 4) + 1 ∧ (2 * (k : ℤ) + 4) - 1 ≤ y ∧ y ≤ 2 * (2 * (k : ℤ) + 4) - 3))
    (n6 : ¬ (x = (2 * (k : ℤ) + 4) ∧ 2 * (2 * (k : ℤ) + 4) - 2 ≤ y ∧ y ≤ 3 * (2 * (k : ℤ) + 4) - 2))
    (n7 : ¬ (y - x = (2 * (k : ℤ) + 4) ∧ 0 ≤ x ∧ x ≤ (2 * (k : ℤ) + 4) - 2))
    (n8 : ¬ (y - x = (2 * (k : ℤ) + 4) - 2 ∧ 2 ≤ x ∧ x ≤ (2 * (k : ℤ) + 4)))
    (n9 : ¬ (x = 0 ∧ y = 2 * (2 * (k : ℤ) + 4)))
    (n10 : ¬ (x = (2 * (k : ℤ) + 4) ∧ y = (2 * (k : ℤ) + 4) - 2))
    (hab : 1 ≤ x ∧ x ≤ 2 * (k : ℤ) + 3) :
    twosSlip k (x + 1, y) + twosP k (x + 1 + 1, y + 1) ≤ twosSlip k (x, y) + twosP k (x + 1, y + 1) := by
  obtain ⟨m, hm⟩ : ∃ m, y = 2 * m - x := ⟨(x + y) / 2, by omega⟩
  have hk1 : TwosKey (2 * (k : ℤ) + 4) x y := twosKey_of_native hn
  have hk2 := (even_right_key k hn hp n1 n2 n3 n4 n5 n6 n7 n8 n9 n10).1
  have hcl := even_right_D k hn hp n1 n2 n3 n4 n5 n6 n7 n8 n9 n10
  have hD := twosSlip_le_of_bands k (x := (x, y)) (y := (x + 1, y)) hk1 hk2 hcl.1 hcl.2
  have v1 := twos_slip_value k hk1
  have v2 := twos_slip_value k hk2
  obtain ⟨ha, hb⟩ := hab
  by_cases hex : x = 2 * (k : ℤ) + 3 ∧ 2 * (2 * (k : ℤ) + 4) - 1 ≤ y ∧ y ≤ 3 * (2 * (k : ℤ) + 4) - 3
  · refine twosChain_le_tr k (-(2 * (k : ℤ) + 5)) (-(2 * (k : ℤ) + 3)) 1 (twosP_shiftU k) hD ?_ ?_ ?_
    · clear n2 n3 n5 n6 n9 n10 v1 v2 hD hcl hk1 hk2; unfold TwosKey; (try dsimp only); unfold NativeT at hn; (rcases hn with ⟨⟨g1, g2, g3, g4, g5, g6⟩, g7⟩ | g8 | g9 <;> omega)
    · clear n2 n3 n5 n6 n9 n10 v1 v2 hD hcl hk1 hk2; unfold TwosKey; (try dsimp only); unfold NativeT at hn; (rcases hn with ⟨⟨g1, g2, g3, g4, g5, g6⟩, g7⟩ | g8 | g9 <;> omega)
    · clear n2 n3 n5 n6 n9 n10 hD hcl hk1 hk2
      (try unfold TwosSlipZ0 at *); (try unfold TwosSlipZ2 at *); unfold TwosDelta; (try dsimp only); unfold NativeT at hn; (rcases hn with ⟨⟨g1, g2, g3, g4, g5, g6⟩, g7⟩ | g8 | g9 <;> omega)
  · refine twosChain_le_tr k 0 0 0 (twosP_shift0 k) hD ?_ ?_ ?_
    · clear n2 n3 n5 n6 n9 n10 v1 v2 hD hcl hk1 hk2; unfold TwosKey; (try dsimp only); unfold NativeT at hn; (rcases hn with ⟨⟨g1, g2, g3, g4, g5, g6⟩, g7⟩ | g8 | g9 <;> omega)
    · clear n2 n3 n5 n6 n7 n8 n9 n10 v1 v2 hD hcl hk1 hk2 hm; unfold TwosKey; (try dsimp only); unfold NativeT at hn; (rcases hn with ⟨⟨g1, g2, g3, g4, g5, g6⟩, g7⟩ | g8 | g9 <;> omega)
    · clear n2 n3 n5 n6 n9 n10 hD hcl hk1 hk2
      (try unfold TwosSlipZ0 at *); (try unfold TwosSlipZ2 at *); unfold TwosDelta; (try dsimp only); unfold NativeT at hn; (rcases hn with ⟨⟨g1, g2, g3, g4, g5, g6⟩, g7⟩ | g8 | g9 <;> omega)

set_option maxHeartbeats 400000 in
/-- Strip 2 of `even_right_chain`. -/
theorem even_right_s2 (k : ℕ) {x y : ℤ} (hn : NativeT (2 * (k : ℤ) + 4) x y) (hp : (x + y) % 2 = 0)
    (n1 : ¬ (y - x = 2 * (2 * (k : ℤ) + 4) ∧ 2 * (2 * (k : ℤ) + 4) + 1 ≤ y ∧ y ≤ 3 * (2 * (k : ℤ) + 4) - 2))
    (n2 : ¬ (x = -1 ∧ (2 * (k : ℤ) + 4) + 1 ≤ y ∧ y ≤ 2 * (2 * (k : ℤ) + 4) - 1))
    (n3 : ¬ (x = 0 ∧ 0 ≤ y ∧ y ≤ (2 * (k : ℤ) + 4)))
    (n4 : ¬ (y - x = -2 ∧ 0 ≤ y ∧ y ≤ (2 * (k : ℤ) + 4) - 3))
    (n5 : ¬ (x = (2 * (k : ℤ) + 4) + 1 ∧ (2 * (k : ℤ) + 4) - 1 ≤ y ∧ y ≤ 2 * (2 * (k : ℤ) + 4) - 3))
    (n6 : ¬ (x = (2 * (k : ℤ) + 4) ∧ 2 * (2 * (k : ℤ) + 4) - 2 ≤ y ∧ y ≤ 3 * (2 * (k : ℤ) + 4) - 2))
    (n7 : ¬ (y - x = (2 * (k : ℤ) + 4) ∧ 0 ≤ x ∧ x ≤ (2 * (k : ℤ) + 4) - 2))
    (n8 : ¬ (y - x = (2 * (k : ℤ) + 4) - 2 ∧ 2 ≤ x ∧ x ≤ (2 * (k : ℤ) + 4)))
    (n9 : ¬ (x = 0 ∧ y = 2 * (2 * (k : ℤ) + 4)))
    (n10 : ¬ (x = (2 * (k : ℤ) + 4) ∧ y = (2 * (k : ℤ) + 4) - 2))
    (h0 : x = 2 * (k : ℤ) + 4) :
    twosSlip k (x + 1, y) + twosP k (x + 1 + 1, y + 1) ≤ twosSlip k (x, y) + twosP k (x + 1, y + 1)   := by
  obtain ⟨m, hm⟩ : ∃ m, y = 2 * m - x := ⟨(x + y) / 2, by omega⟩
  have hk1 : TwosKey (2 * (k : ℤ) + 4) x y := twosKey_of_native hn
  have hk2 := (even_right_key k hn hp n1 n2 n3 n4 n5 n6 n7 n8 n9 n10).1
  have hcl := even_right_D k hn hp n1 n2 n3 n4 n5 n6 n7 n8 n9 n10
  have hD := twosSlip_le_of_bands k (x := (x, y)) (y := (x + 1, y)) hk1 hk2 hcl.1 hcl.2
  have v1 := twos_slip_value k hk1
  have v2 := twos_slip_value k hk2
  subst h0
  by_cases hex : 2 * (k : ℤ) + 4 - 2 ≤ y
  · refine twosChain_le_tr k (-(2 * (k : ℤ) + 5)) (-(2 * (k : ℤ) + 3)) 1 (twosP_shiftU k) hD ?_ ?_ ?_
    · clear n2 n3 n4 n5 n7 n9 v1 v2 hD hcl hk1 hk2; unfold TwosKey; (try dsimp only); unfold NativeT at hn; (rcases hn with ⟨⟨g1, g2, g3, g4, g5, g6⟩, g7⟩ | g8 | g9 <;> omega)
    · clear n2 n3 n4 n5 n7 n9 v1 v2 hD hcl hk1 hk2; unfold TwosKey; (try dsimp only); unfold NativeT at hn; (rcases hn with ⟨⟨g1, g2, g3, g4, g5, g6⟩, g7⟩ | g8 | g9 <;> omega)
    · clear n2 n3 n4 n5 n7 n9 hD hcl hk1 hk2
      (try unfold TwosSlipZ0 at *); (try unfold TwosSlipZ2 at *); unfold TwosDelta; (try dsimp only); unfold NativeT at hn; (rcases hn with ⟨⟨g1, g2, g3, g4, g5, g6⟩, g7⟩ | g8 | g9 <;> omega)
  · refine twosChain_le_tr k (-2) (4 * (k : ℤ) + 8) 0 (twosP_shiftVp k) hD ?_ ?_ ?_
    · clear n2 n3 n4 n5 n7 n9 v1 v2 hD hcl hk1 hk2; unfold TwosKey; (try dsimp only); unfold NativeT at hn; (rcases hn with ⟨⟨g1, g2, g3, g4, g5, g6⟩, g7⟩ | g8 | g9 <;> omega)
    · clear n2 n3 n4 n5 n7 n9 v1 v2 hD hcl hk1 hk2; unfold TwosKey; (try dsimp only); unfold NativeT at hn; (rcases hn with ⟨⟨g1, g2, g3, g4, g5, g6⟩, g7⟩ | g8 | g9 <;> omega)
    · clear n2 n3 n4 n5 n7 n9 hD hcl hk1 hk2
      (try unfold TwosSlipZ0 at *); (try unfold TwosSlipZ2 at *); unfold TwosDelta; (try dsimp only); unfold NativeT at hn; (rcases hn with ⟨⟨g1, g2, g3, g4, g5, g6⟩, g7⟩ | g8 | g9 <;> omega)

set_option maxHeartbeats 400000 in
/-- Strip 3 of `even_right_chain`. -/
theorem even_right_s3 (k : ℕ) {x y : ℤ} (hn : NativeT (2 * (k : ℤ) + 4) x y) (hp : (x + y) % 2 = 0)
    (n1 : ¬ (y - x = 2 * (2 * (k : ℤ) + 4) ∧ 2 * (2 * (k : ℤ) + 4) + 1 ≤ y ∧ y ≤ 3 * (2 * (k : ℤ) + 4) - 2))
    (n2 : ¬ (x = -1 ∧ (2 * (k : ℤ) + 4) + 1 ≤ y ∧ y ≤ 2 * (2 * (k : ℤ) + 4) - 1))
    (n3 : ¬ (x = 0 ∧ 0 ≤ y ∧ y ≤ (2 * (k : ℤ) + 4)))
    (n4 : ¬ (y - x = -2 ∧ 0 ≤ y ∧ y ≤ (2 * (k : ℤ) + 4) - 3))
    (n5 : ¬ (x = (2 * (k : ℤ) + 4) + 1 ∧ (2 * (k : ℤ) + 4) - 1 ≤ y ∧ y ≤ 2 * (2 * (k : ℤ) + 4) - 3))
    (n6 : ¬ (x = (2 * (k : ℤ) + 4) ∧ 2 * (2 * (k : ℤ) + 4) - 2 ≤ y ∧ y ≤ 3 * (2 * (k : ℤ) + 4) - 2))
    (n7 : ¬ (y - x = (2 * (k : ℤ) + 4) ∧ 0 ≤ x ∧ x ≤ (2 * (k : ℤ) + 4) - 2))
    (n8 : ¬ (y - x = (2 * (k : ℤ) + 4) - 2 ∧ 2 ≤ x ∧ x ≤ (2 * (k : ℤ) + 4)))
    (n9 : ¬ (x = 0 ∧ y = 2 * (2 * (k : ℤ) + 4)))
    (n10 : ¬ (x = (2 * (k : ℤ) + 4) ∧ y = (2 * (k : ℤ) + 4) - 2))
    (h0 : x = 2 * (k : ℤ) + 5) :
    twosSlip k (x + 1, y) + twosP k (x + 1 + 1, y + 1) ≤ twosSlip k (x, y) + twosP k (x + 1, y + 1) := by
  obtain ⟨m, hm⟩ : ∃ m, y = 2 * m - x := ⟨(x + y) / 2, by omega⟩
  have hk1 : TwosKey (2 * (k : ℤ) + 4) x y := twosKey_of_native hn
  have hk2 := (even_right_key k hn hp n1 n2 n3 n4 n5 n6 n7 n8 n9 n10).1
  have hcl := even_right_D k hn hp n1 n2 n3 n4 n5 n6 n7 n8 n9 n10
  have hD := twosSlip_le_of_bands k (x := (x, y)) (y := (x + 1, y)) hk1 hk2 hcl.1 hcl.2
  have v1 := twos_slip_value k hk1
  have v2 := twos_slip_value k hk2
  subst h0
  refine twosChain_le_tr k 0 0 0 (twosP_shift0 k) hD ?_ ?_ ?_
  · clear n2 n3 n6 n7 n8 n9 n10 v1 v2 hD hcl hk1 hk2; unfold TwosKey; (try dsimp only); unfold NativeT at hn; (rcases hn with ⟨⟨g1, g2, g3, g4, g5, g6⟩, g7⟩ | g8 | g9 <;> omega)
  · clear n2 n3 n7 n9 v1 v2 hD hcl hk1 hk2; unfold TwosKey; (try dsimp only); unfold NativeT at hn; (rcases hn with ⟨⟨g1, g2, g3, g4, g5, g6⟩, g7⟩ | g8 | g9 <;> omega)
  · clear n2 n3 n7 n9 hD hcl hk1 hk2
    (try unfold TwosSlipZ0 at *); (try unfold TwosSlipZ2 at *); unfold TwosDelta; (try dsimp only); unfold NativeT at hn; (rcases hn with ⟨⟨g1, g2, g3, g4, g5, g6⟩, g7⟩ | g8 | g9 <;> omega)

set_option maxHeartbeats 400000 in
/-- The right input of an even black centre: the chain claim, split into the strips of `x` and the two exceptional strips
whose shifted pair needs the translate `-U`. -/
theorem even_right_chain (k : ℕ) {x y : ℤ} (hn : NativeT (2 * (k : ℤ) + 4) x y) (hp : (x + y) % 2 = 0)
    (n1 : ¬ (y - x = 2 * (2 * (k : ℤ) + 4) ∧ 2 * (2 * (k : ℤ) + 4) + 1 ≤ y ∧ y ≤ 3 * (2 * (k : ℤ) + 4) - 2))
    (n2 : ¬ (x = -1 ∧ (2 * (k : ℤ) + 4) + 1 ≤ y ∧ y ≤ 2 * (2 * (k : ℤ) + 4) - 1))
    (n3 : ¬ (x = 0 ∧ 0 ≤ y ∧ y ≤ (2 * (k : ℤ) + 4)))
    (n4 : ¬ (y - x = -2 ∧ 0 ≤ y ∧ y ≤ (2 * (k : ℤ) + 4) - 3))
    (n5 : ¬ (x = (2 * (k : ℤ) + 4) + 1 ∧ (2 * (k : ℤ) + 4) - 1 ≤ y ∧ y ≤ 2 * (2 * (k : ℤ) + 4) - 3))
    (n6 : ¬ (x = (2 * (k : ℤ) + 4) ∧ 2 * (2 * (k : ℤ) + 4) - 2 ≤ y ∧ y ≤ 3 * (2 * (k : ℤ) + 4) - 2))
    (n7 : ¬ (y - x = (2 * (k : ℤ) + 4) ∧ 0 ≤ x ∧ x ≤ (2 * (k : ℤ) + 4) - 2))
    (n8 : ¬ (y - x = (2 * (k : ℤ) + 4) - 2 ∧ 2 ≤ x ∧ x ≤ (2 * (k : ℤ) + 4)))
    (n9 : ¬ (x = 0 ∧ y = 2 * (2 * (k : ℤ) + 4)))
    (n10 : ¬ (x = (2 * (k : ℤ) + 4) ∧ y = (2 * (k : ℤ) + 4) - 2)) :
    twosSlip k (x + 1, y) + twosP k (x + 1 + 1, y + 1) ≤ twosSlip k (x, y) + twosP k (x + 1, y + 1) := by
  have hs : x = 0 ∨ (1 ≤ x ∧ x ≤ 2 * (k : ℤ) + 3) ∨ x = 2 * (k : ℤ) + 4 ∨ x = 2 * (k : ℤ) + 5 := by
    clear n1 n3 n4 n5 n6 n7 n8 n9 n10
    unfold NativeT at hn
    rcases hn with ⟨⟨g1, g2, g3, g4, g5, g6⟩, g7⟩ | g8 | g9 <;> omega
  rcases hs with h0 | hab | h0 | h0
  · exact even_right_s0 k hn hp n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 h0
  · exact even_right_s1 k hn hp n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 hab
  · exact even_right_s2 k hn hp n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 h0
  · exact even_right_s3 k hn hp n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 h0

set_option maxHeartbeats 400000 in
/-- The black branch of the chain claim at an odd centre: the rotated point is `LadderOddEvenBlack`, with no exceptions. -/
theorem black_odd_chain (k : ℕ) {x y j1 j2 : ℤ} (hn : NativeT (2 * (k : ℤ) + 4) x y) (hp : ¬ EvenSite (x, y))
    (hB : LadderOddEvenBlack (2 * (k : ℤ) + 4) (2 * (2 * (k : ℤ) + 4) - y, x + 1))
    (he : Edge (j1, j2) (x, y)) :
    twosSlip k (j1, j2) + twosP k (j1 + 1, j2 + 1) ≤ twosSlip k (x, y) + twosP k (x + 1, y + 1) := by
  have hk1 : TwosKey (2 * (k : ℤ) + 4) x y := twosKey_of_native hn
  have hk2 := (black_key_odd k hn hp hB he).1
  have hcl := black_key_odd_D k hn hp hB he
  have hD := twosSlip_le_of_bands k (x := (x, y)) (y := (j1, j2)) hk1 hk2 hcl.1 hcl.2
  have v1 := twos_slip_value k hk1
  have v2 := twos_slip_value k hk2
  have hEd := edge_odd_cases x y j1 j2 hp he
  unfold LadderOddEvenBlack at hB
  (try dsimp only at hB)
  clear hk2 hcl hk1 he
  rcases hEd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hB with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  all_goals
    refine twosChain_le_tr k 0 0 0 (twosP_shift0 k) hD ?_ ?_ ?_
    · clear hD v1 v2 hn hp; unfold TwosKey; (try dsimp only); omega
    · clear hD v1 v2 hn hp; unfold TwosKey; (try dsimp only); omega
    · clear hD hn hp
      (try unfold TwosSlipZ0 at *); (try unfold TwosSlipZ2 at *); unfold TwosDelta; (try dsimp only)
      rcases v1 with ⟨e1, z1⟩ | ⟨e1, z1, z1'⟩ | ⟨e1, z1⟩ <;> rcases v2 with ⟨e2, z2⟩ | ⟨e2, z2, z2'⟩ | ⟨e2, z2⟩ <;> omega

set_option maxHeartbeats 400000 in
/-- **The black branch of the chain claim.** -/
theorem black_chain (k : ℕ) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    {x y j1 j2 : ℤ} (hn : NativeT (2 * (k : ℤ) + 4) x y)
    (hl : laplacian (standardField (List.replicate (k + 1) Digit.two)) (x, y) = -1)
    (he : Edge (j1, j2) (x, y)) :
    twosSlip k (j1, j2) + twosP k (j1 + 1, j2 + 1) ≤ twosSlip k (x, y) + twosP k (x + 1, y + 1) := by
  have hR := black_region_of_lap k hagree hperiod hn hl
  by_cases hp : EvenSite (x, y)
  · have hW : ¬ LadderOddOddWhite (2 * (k : ℤ) + 4) (2 * (2 * (k : ℤ) + 4) - y, x + 1) := by
      rcases hR with ⟨hE, _⟩ | ⟨_, hW⟩
      · exact absurd ((evenSite_rot (2 * (k : ℤ) + 4) x y).mp hE) (not_not.mpr hp)
      · exact hW
    obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10⟩ := even_negs k hW
    have hp' : (x + y) % 2 = 0 := hp
    rcases edge_even_cases x y j1 j2 hp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · subst h1
      subst h2
      exact even_left_chain k hn hp' n1 n2 n3 n4 n5 n6 n7 n8 n9 n10
    · subst h1
      subst h2
      exact even_right_chain k hn hp' n1 n2 n3 n4 n5 n6 n7 n8 n9 n10
  · have hB : LadderOddEvenBlack (2 * (k : ℤ) + 4) (2 * (2 * (k : ℤ) + 4) - y, x + 1) := by
      rcases hR with ⟨_, hB⟩ | ⟨hNE, _⟩
      · exact hB
      · exact absurd ((evenSite_rot (2 * (k : ℤ) + 4) x y).mpr hp) hNE
    exact black_odd_chain k hn hp hB he

/-! ### Transport along aliases, and the chain potential of the twos policy (sign `+1`). -/

/-- Transport of the chain comparison along an alias: the slip and the shifted price both move by the same amount. -/
theorem twosChain_le_of_alias (k : ℕ) (p q i1 i2 c1 c2 u1 u2 j1 j2 : ℤ)
    (hu1 : u1 = c1 - p * (2 * (k : ℤ) + 4 + 1) + 2 * q)
    (hu2 : u2 = c2 - p * (2 * (k : ℤ) + 4 - 1) - 2 * (2 * (k : ℤ) + 4) * q)
    (hj1 : j1 = i1 - p * (2 * (k : ℤ) + 4 + 1) + 2 * q)
    (hj2 : j2 = i2 - p * (2 * (k : ℤ) + 4 - 1) - 2 * (2 * (k : ℤ) + 4) * q)
    (h : twosSlip k (j1, j2) + twosP k (j1 + 1, j2 + 1) ≤ twosSlip k (u1, u2) + twosP k (u1 + 1, u2 + 1)) :
    twosSlip k (i1, i2) + twosP k (i1 + 1, i2 + 1) ≤ twosSlip k (c1, c2) + twosP k (c1 + 1, c2 + 1) := by
  have a1 := twosSlip_shift k p q i1 i2
  have a2 := twosSlip_shift k p q c1 c2
  have b1 := twosP_shift k p q (i1 + 1) (i2 + 1)
  have b2 := twosP_shift k p q (c1 + 1) (c2 + 1)
  have e1 : j1 + 1 = i1 + 1 - p * (2 * (k : ℤ) + 4 + 1) + 2 * q := by rw [hj1]; ring
  have e2 : j2 + 1 = i2 + 1 - p * (2 * (k : ℤ) + 4 - 1) - 2 * (2 * (k : ℤ) + 4) * q := by rw [hj2]; ring
  have f1 : u1 + 1 = c1 + 1 - p * (2 * (k : ℤ) + 4 + 1) + 2 * q := by rw [hu1]; ring
  have f2 : u2 + 1 = c2 + 1 - p * (2 * (k : ℤ) + 4 - 1) - 2 * (2 * (k : ℤ) + 4) * q := by rw [hu2]; ring
  rw [← e1, ← e2] at b1
  rw [← f1, ← f2] at b2
  rw [← hj1, ← hj2] at a1
  rw [← hu1, ← hu2] at a2
  linarith



/-- The chain quantity of sign `+1` at the twos word, in the shifted price form: `Φ₊₁(z) = D(z) + P(z + (1,1)) + 1` (`σ + U = (1,1)`,
`P(· − U) = P + 1`). -/
theorem chainP_eq (k : ℕ) (z : Site) :
    (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) 1 z =
      twosSlip k z + twosP k (z.1 + 1, z.2 + 1) + 1 := by
  unfold ChildFrame.chainPotential
  have hs : (frameAt (List.replicate (k + 1) Digit.two)).slip (standardField (List.replicate (k + 1) Digit.two)) 1 z =
      twosSlip k z := by
    unfold ChildFrame.slip twosSlip
    simp only [one_smul]
  rw [hs]
  have e : z + (1 : ℤ) • (frameAt (List.replicate (k + 1) Digit.two)).shortShift =
      (z.1 + 1 - (2 * (k : ℤ) + 5), z.2 + 1 - (2 * (k : ℤ) + 3)) := by
    rw [one_smul, twos_shortShift_explicit]
    apply Prod.ext
    · simp only [Prod.fst_add]
      ring
    · simp only [Prod.snd_add]
      ring
  rw [e]
  have hP := twosP_negU k (z.1 + 1) (z.2 + 1)
  unfold twosP at hP ⊢
  linarith

/-- **The black branch of the chain claim, sign `+1`, in the chain potential form.** Along a black centre's selected input the
chain potential of sign `+1` does not increase (`black_chain`). -/
theorem twosChain_nonincreasing_black (k : ℕ) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    {x y j1 j2 : ℤ} (hn : NativeT (2 * (k : ℤ) + 4) x y)
    (hl : laplacian (standardField (List.replicate (k + 1) Digit.two)) (x, y) = -1)
    (he : Edge (j1, j2) (x, y)) :
    (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) 1 (j1, j2) ≤
      (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) 1 (x, y) := by
  rw [chainP_eq, chainP_eq]
  have h := black_chain k hagree hperiod hn hl he
  dsimp only at h ⊢
  linarith

/-- The chain comparison of the twos signed policy, in the twos form (the transport of `twosSlip_nonincreasing` with the price). -/
theorem twosChain_le_sel (k : ℕ) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    {c i : Site}
    (hT : TwosSel (2 * (k : ℤ) + 4) 1 (standardField (List.replicate (k + 1) Digit.two)) c i) :
    twosSlip k i + twosP k (i.1 + 1, i.2 + 1) ≤ twosSlip k c + twosP k (c.1 + 1, c.2 + 1) := by
  obtain ⟨c1, c2⟩ := c
  obtain ⟨i1, i2⟩ := i
  have ha2 : (2 * (k : ℤ) + 4) % 2 = 0 := by omega
  have hvalid := ladderOdd_valid_twos k
  rcases hT with ⟨hl, he⟩ | ⟨hl, ⟨u, hu, hF, hi⟩ | ⟨hnf, u, hu, hn, hg, hi⟩⟩
  · -- black centres: both inputs are kept, and the native copy is black too
    obtain ⟨u, hA, hn⟩ := native_copy_exists ha2 hvalid (c1, c2)
    have hlu := laplacian_twos_alias hagree hperiod hA
    obtain ⟨u1, u2⟩ := u
    obtain ⟨p, q, hpq⟩ := hA
    have hu1 : u1 = c1 - p * (2 * (k : ℤ) + 4 + 1) + 2 * q := congrArg Prod.fst hpq
    have hu2 : u2 = c2 - p * (2 * (k : ℤ) + 4 - 1) - 2 * (2 * (k : ℤ) + 4) * q := congrArg Prod.snd hpq
    have hlu' : laplacian (standardField (List.replicate (k + 1) Digit.two)) (u1, u2) = -1 := by
      rw [hlu]; exact hl
    obtain ⟨j1, hj1⟩ : ∃ j : ℤ, j = i1 - p * (2 * (k : ℤ) + 4 + 1) + 2 * q := ⟨_, rfl⟩
    obtain ⟨j2, hj2⟩ : ∃ j : ℤ, j = i2 - p * (2 * (k : ℤ) + 4 - 1) - 2 * (2 * (k : ℤ) + 4) * q := ⟨_, rfl⟩
    have hμ : (-p * (2 * (k : ℤ) + 4 + 1) + 2 * q + (-p * (2 * (k : ℤ) + 4 - 1) - 2 * (2 * (k : ℤ) + 4) * q)) % 2 = 0 := by
      have e : -p * (2 * (k : ℤ) + 4 + 1) + 2 * q + (-p * (2 * (k : ℤ) + 4 - 1) - 2 * (2 * (k : ℤ) + 4) * q) =
          2 * (-p * (2 * (k : ℤ) + 4) + q - (2 * (k : ℤ) + 4) * q) := by ring
      rw [e]
      exact Int.mul_emod_right _ _
    have hE := (edge_add (i1, i2) (c1, c2) (-p * (2 * (k : ℤ) + 4 + 1) + 2 * q)
      (-p * (2 * (k : ℤ) + 4 - 1) - 2 * (2 * (k : ℤ) + 4) * q) hμ).mpr he
    dsimp only at hE
    have hE' : Edge (j1, j2) (u1, u2) := by
      rw [hj1, hj2, hu1, hu2]
      rw [show i1 + (-p * (2 * (k : ℤ) + 4 + 1) + 2 * q) = i1 - p * (2 * (k : ℤ) + 4 + 1) + 2 * q by ring,
        show i2 + (-p * (2 * (k : ℤ) + 4 - 1) - 2 * (2 * (k : ℤ) + 4) * q) = i2 - p * (2 * (k : ℤ) + 4 - 1) - 2 * (2 * (k : ℤ) + 4) * q by ring,
        show c1 + (-p * (2 * (k : ℤ) + 4 + 1) + 2 * q) = c1 - p * (2 * (k : ℤ) + 4 + 1) + 2 * q by ring,
        show c2 + (-p * (2 * (k : ℤ) + 4 - 1) - 2 * (2 * (k : ℤ) + 4) * q) = c2 - p * (2 * (k : ℤ) + 4 - 1) - 2 * (2 * (k : ℤ) + 4) * q by ring] at hE
      exact hE
    have hb := twosChain_nonincreasing_black k hagree hperiod hn hlu' hE'
    rw [chainP_eq, chainP_eq] at hb
    dsimp only at hb
    have hb' : twosSlip k (j1, j2) + twosP k (j1 + 1, j2 + 1) ≤ twosSlip k (u1, u2) + twosP k (u1 + 1, u2 + 1) := by
      linarith
    exact twosChain_le_of_alias k p q i1 i2 c1 c2 u1 u2 j1 j2 hu1 hu2 hj1 hj2 hb'
  · -- free centres: the free table at the free alias
    obtain ⟨u1, u2⟩ := u
    obtain ⟨p, q, hpq⟩ := hu
    have hu1 : u1 = c1 - p * (2 * (k : ℤ) + 4 + 1) + 2 * q := congrArg Prod.fst hpq
    have hu2 : u2 = c2 - p * (2 * (k : ℤ) + 4 - 1) - 2 * (2 * (k : ℤ) + 4) * q := congrArg Prod.snd hpq
    have hi1 : i1 = c1 + (freeDisp (2 * (k : ℤ) + 4) 1 u1 u2).1 := congrArg Prod.fst hi
    have hi2 : i2 = c2 + (freeDisp (2 * (k : ℤ) + 4) 1 u1 u2).2 := congrArg Prod.snd hi
    have hfree := freeChain_mono k (x := u1) (y := u2) hF
    obtain ⟨j1, hj1⟩ : ∃ j : ℤ, j = i1 - p * (2 * (k : ℤ) + 4 + 1) + 2 * q := ⟨_, rfl⟩
    obtain ⟨j2, hj2⟩ : ∃ j : ℤ, j = i2 - p * (2 * (k : ℤ) + 4 - 1) - 2 * (2 * (k : ℤ) + 4) * q := ⟨_, rfl⟩
    have hj1' : j1 = u1 + (freeDisp (2 * (k : ℤ) + 4) 1 u1 u2).1 := by
      rw [hj1, hi1]; linarith
    have hj2' : j2 = u2 + (freeDisp (2 * (k : ℤ) + 4) 1 u1 u2).2 := by
      rw [hj2, hi2]; linarith
    have hb : twosSlip k (j1, j2) + twosP k (j1 + 1, j2 + 1) ≤ twosSlip k (u1, u2) + twosP k (u1 + 1, u2 + 1) := by
      rw [hj1', hj2']; exact hfree
    exact twosChain_le_of_alias k p q i1 i2 c1 c2 u1 u2 j1 j2 hu1 hu2 hj1 hj2 hb
  · -- non-free centres: the candidate displacement at the native copy
    obtain ⟨u1, u2⟩ := u
    obtain ⟨p, q, hpq⟩ := hu
    have hu1 : u1 = c1 - p * (2 * (k : ℤ) + 4 + 1) + 2 * q := congrArg Prod.fst hpq
    have hu2 : u2 = c2 - p * (2 * (k : ℤ) + 4 - 1) - 2 * (2 * (k : ℤ) + 4) * q := congrArg Prod.snd hpq
    have hi1 : i1 = c1 + (candDisp (2 * (k : ℤ) + 4) u1 u2).1 := congrArg Prod.fst hi
    have hi2 : i2 = c2 + (candDisp (2 * (k : ℤ) + 4) u1 u2).2 := congrArg Prod.snd hi
    have hcand := chainC_mono k (x := u1) (y := u2) hn hg
    obtain ⟨j1, hj1⟩ : ∃ j : ℤ, j = i1 - p * (2 * (k : ℤ) + 4 + 1) + 2 * q := ⟨_, rfl⟩
    obtain ⟨j2, hj2⟩ : ∃ j : ℤ, j = i2 - p * (2 * (k : ℤ) + 4 - 1) - 2 * (2 * (k : ℤ) + 4) * q := ⟨_, rfl⟩
    have hj1' : j1 = u1 + (candDisp (2 * (k : ℤ) + 4) u1 u2).1 := by
      rw [hj1, hi1]; linarith
    have hj2' : j2 = u2 + (candDisp (2 * (k : ℤ) + 4) u1 u2).2 := by
      rw [hj2, hi2]; linarith
    have hb : twosSlip k (j1, j2) + twosP k (j1 + 1, j2 + 1) ≤ twosSlip k (u1, u2) + twosP k (u1 + 1, u2 + 1) := by
      rw [hj1', hj2']; exact hcand
    exact twosChain_le_of_alias k p q i1 i2 c1 c2 u1 u2 j1 j2 hu1 hu2 hj1 hj2 hb



/-- **The chain comparison of the twos signed policy, sign `+1`:** along a selected input the chain potential does not increase. -/
theorem twosChain_nonincreasing (k : ℕ) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    {c i : Site}
    (hT : TwosSel (2 * (k : ℤ) + 4) 1 (standardField (List.replicate (k + 1) Digit.two)) c i) :
    (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) 1 i ≤
      (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) 1 c := by
  rw [chainP_eq, chainP_eq]
  have h := twosChain_le_sel k hagree hperiod hT
  linarith

end FLatticePaper.TwosEPolicy

