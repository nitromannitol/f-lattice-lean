import FLatticePaper.Plane.Induction.TwosUnitPrice

/-! Task 118, base inputs at `2^(k+1)`: `F1_noPriceSaddle` (no star of the primitive price has two opposite nonzero increments).

As for the unit step, a neighbour of a polygon point is reached by one of the lattice shifts `±U`, `±V` (`twos_cover_*`), and the
price changes accordingly (`twos_price_U_step`, `twos_price_V_step`). For a horizontal star (even centre) the two neighbours are the
left and right ones, for a vertical star (odd centre) the lower and upper ones; each is a case split over three covers, decided by
`omega` on the bands `TwosDelta`. -/

namespace FLatticePaper.Induction
open Farey Construction

set_option maxHeartbeats 400000 in
/-- The horizontal star at a polygon point has no opposite nonzero increments. -/
theorem twos_star_h (k : ℕ) {y1 y2 : ℤ} (hy : TwosKey (2 * (k : ℤ) + 4) (y1) (y2)) :
    ¬ (((((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (y1 - 1, y2)) - ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (y1, y2))) = -1 ∧ (((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (y1 + 1, y2)) - ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (y1, y2))) = 1) ∨
      ((((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (y1 - 1, y2)) - ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (y1, y2))) = 1 ∧ (((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (y1 + 1, y2)) - ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (y1, y2))) = -1)) := by
  have hd := twos_price_delta k hy
  unfold TwosDelta at hd
  rcases twos_cover_m k hy with hL0 | hLU | hLV <;> rcases twos_cover_p k hy with hR0 | hRU | hRV
  · have hl := twos_price_delta k hL0
    have hr := twos_price_delta k hR0
    unfold TwosDelta at hl hr
    simp only [twosKey_pos] at *
    omega
  · have hl := twos_price_delta k hL0
    have hr := twos_price_delta k hRU
    have hrr := twos_price_U_step k (y1 + 1 - (2 * (k : ℤ) + 5)) (y2 - (2 * (k : ℤ) + 3))
    rw [show y1 + 1 - (2 * (k : ℤ) + 5) + (2 * (k : ℤ) + 5) = y1 + 1 by ring, show y2 - (2 * (k : ℤ) + 3) + (2 * (k : ℤ) + 3) = y2 by ring] at hrr
    unfold TwosDelta at hl hr
    simp only [twosKey_pos] at *
    omega
  · have hl := twos_price_delta k hL0
    have hr := twos_price_delta k hRV
    have hrr := twos_price_V_step k (y1 + 1) y2
    unfold TwosDelta at hl hr
    simp only [twosKey_pos] at *
    omega
  · have hl := twos_price_delta k hLU
    have hr := twos_price_delta k hR0
    have hll := twos_price_U_step k (y1 - 1) y2
    unfold TwosDelta at hl hr
    simp only [twosKey_pos] at *
    omega
  · have hl := twos_price_delta k hLU
    have hr := twos_price_delta k hRU
    have hll := twos_price_U_step k (y1 - 1) y2
    have hrr := twos_price_U_step k (y1 + 1 - (2 * (k : ℤ) + 5)) (y2 - (2 * (k : ℤ) + 3))
    rw [show y1 + 1 - (2 * (k : ℤ) + 5) + (2 * (k : ℤ) + 5) = y1 + 1 by ring, show y2 - (2 * (k : ℤ) + 3) + (2 * (k : ℤ) + 3) = y2 by ring] at hrr
    unfold TwosDelta at hl hr
    simp only [twosKey_pos] at *
    omega
  · have hl := twos_price_delta k hLU
    have hr := twos_price_delta k hRV
    have hll := twos_price_U_step k (y1 - 1) y2
    have hrr := twos_price_V_step k (y1 + 1) y2
    unfold TwosDelta at hl hr
    simp only [twosKey_pos] at *
    omega
  · have hl := twos_price_delta k hLV
    have hr := twos_price_delta k hR0
    have hll := twos_price_V_step k (y1 - 1 + 2) (y2 - (4 * (k : ℤ) + 8))
    rw [show y1 - 1 + 2 - 2 = y1 - 1 by ring, show y2 - (4 * (k : ℤ) + 8) + (4 * (k : ℤ) + 8) = y2 by ring] at hll
    unfold TwosDelta at hl hr
    simp only [twosKey_pos] at *
    omega
  · have hl := twos_price_delta k hLV
    have hr := twos_price_delta k hRU
    have hll := twos_price_V_step k (y1 - 1 + 2) (y2 - (4 * (k : ℤ) + 8))
    rw [show y1 - 1 + 2 - 2 = y1 - 1 by ring, show y2 - (4 * (k : ℤ) + 8) + (4 * (k : ℤ) + 8) = y2 by ring] at hll
    have hrr := twos_price_U_step k (y1 + 1 - (2 * (k : ℤ) + 5)) (y2 - (2 * (k : ℤ) + 3))
    rw [show y1 + 1 - (2 * (k : ℤ) + 5) + (2 * (k : ℤ) + 5) = y1 + 1 by ring, show y2 - (2 * (k : ℤ) + 3) + (2 * (k : ℤ) + 3) = y2 by ring] at hrr
    unfold TwosDelta at hl hr
    simp only [twosKey_pos] at *
    omega
  · have hl := twos_price_delta k hLV
    have hr := twos_price_delta k hRV
    have hll := twos_price_V_step k (y1 - 1 + 2) (y2 - (4 * (k : ℤ) + 8))
    rw [show y1 - 1 + 2 - 2 = y1 - 1 by ring, show y2 - (4 * (k : ℤ) + 8) + (4 * (k : ℤ) + 8) = y2 by ring] at hll
    have hrr := twos_price_V_step k (y1 + 1) y2
    unfold TwosDelta at hl hr
    simp only [twosKey_pos] at *
    omega

set_option maxHeartbeats 400000 in
/-- The vertical star at a polygon point has no opposite nonzero increments. -/
theorem twos_star_v (k : ℕ) {y1 y2 : ℤ} (hy : TwosKey (2 * (k : ℤ) + 4) (y1) (y2)) :
    ¬ ((((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (y1, y2 - 1)) - ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (y1, y2)) = -1 ∧ ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (y1, y2 + 1)) - ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (y1, y2)) = 1) ∨
      (((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (y1, y2 - 1)) - ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (y1, y2)) = 1 ∧ ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (y1, y2 + 1)) - ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (y1, y2)) = -1)) := by
  have hd := twos_price_delta k hy
  unfold TwosDelta at hd
  rcases twos_cover_r k hy with hL0 | hLU | hLV <;> rcases twos_cover_q k hy with hR0 | hRV | hRU
  · have hl := twos_price_delta k hL0
    have hr := twos_price_delta k hR0
    unfold TwosDelta at hl hr
    simp only [twosKey_pos] at *
    omega
  · have hl := twos_price_delta k hL0
    have hr := twos_price_delta k hRV
    have hrr := twos_price_V_step k (y1 + 2) (y2 + 1 - (4 * (k : ℤ) + 8))
    rw [show y1 + 2 - 2 = y1 by ring, show y2 + 1 - (4 * (k : ℤ) + 8) + (4 * (k : ℤ) + 8) = y2 + 1 by ring] at hrr
    unfold TwosDelta at hl hr
    simp only [twosKey_pos] at *
    omega
  · have hl := twos_price_delta k hL0
    have hr := twos_price_delta k hRU
    have hrr := twos_price_U_step k (y1 - (2 * (k : ℤ) + 5)) (y2 + 1 - (2 * (k : ℤ) + 3))
    rw [show y1 - (2 * (k : ℤ) + 5) + (2 * (k : ℤ) + 5) = y1 by ring, show y2 + 1 - (2 * (k : ℤ) + 3) + (2 * (k : ℤ) + 3) = y2 + 1 by ring] at hrr
    unfold TwosDelta at hl hr
    simp only [twosKey_pos] at *
    omega
  · have hl := twos_price_delta k hLU
    have hr := twos_price_delta k hR0
    have hll := twos_price_U_step k (y1) (y2 - 1)
    unfold TwosDelta at hl hr
    simp only [twosKey_pos] at *
    omega
  · have hl := twos_price_delta k hLU
    have hr := twos_price_delta k hRV
    have hll := twos_price_U_step k (y1) (y2 - 1)
    have hrr := twos_price_V_step k (y1 + 2) (y2 + 1 - (4 * (k : ℤ) + 8))
    rw [show y1 + 2 - 2 = y1 by ring, show y2 + 1 - (4 * (k : ℤ) + 8) + (4 * (k : ℤ) + 8) = y2 + 1 by ring] at hrr
    unfold TwosDelta at hl hr
    simp only [twosKey_pos] at *
    omega
  · have hl := twos_price_delta k hLU
    have hr := twos_price_delta k hRU
    have hll := twos_price_U_step k (y1) (y2 - 1)
    have hrr := twos_price_U_step k (y1 - (2 * (k : ℤ) + 5)) (y2 + 1 - (2 * (k : ℤ) + 3))
    rw [show y1 - (2 * (k : ℤ) + 5) + (2 * (k : ℤ) + 5) = y1 by ring, show y2 + 1 - (2 * (k : ℤ) + 3) + (2 * (k : ℤ) + 3) = y2 + 1 by ring] at hrr
    unfold TwosDelta at hl hr
    simp only [twosKey_pos] at *
    omega
  · have hl := twos_price_delta k hLV
    have hr := twos_price_delta k hR0
    have hll := twos_price_V_step k (y1) (y2 - 1)
    unfold TwosDelta at hl hr
    simp only [twosKey_pos] at *
    omega
  · have hl := twos_price_delta k hLV
    have hr := twos_price_delta k hRV
    have hll := twos_price_V_step k (y1) (y2 - 1)
    have hrr := twos_price_V_step k (y1 + 2) (y2 + 1 - (4 * (k : ℤ) + 8))
    rw [show y1 + 2 - 2 = y1 by ring, show y2 + 1 - (4 * (k : ℤ) + 8) + (4 * (k : ℤ) + 8) = y2 + 1 by ring] at hrr
    unfold TwosDelta at hl hr
    simp only [twosKey_pos] at *
    omega
  · have hl := twos_price_delta k hLV
    have hr := twos_price_delta k hRU
    have hll := twos_price_V_step k (y1) (y2 - 1)
    have hrr := twos_price_U_step k (y1 - (2 * (k : ℤ) + 5)) (y2 + 1 - (2 * (k : ℤ) + 3))
    rw [show y1 - (2 * (k : ℤ) + 5) + (2 * (k : ℤ) + 5) = y1 by ring, show y2 + 1 - (2 * (k : ℤ) + 3) + (2 * (k : ℤ) + 3) = y2 + 1 by ring] at hrr
    unfold TwosDelta at hl hr
    simp only [twosKey_pos] at *
    omega

set_option maxHeartbeats 400000 in
/-- **`F1_noPriceSaddle` at `2^(k+1)`.** -/
theorem twos_noPriceSaddle (k : ℕ) :
    NoPriceSaddle (frameAt (List.replicate (k + 1) Digit.two)) (standardField (List.replicate (k + 1) Digit.two)) := by
  intro site
  dsimp only
  obtain ⟨y, hy, i, j, hc⟩ := (frameAt (List.replicate (k + 1) Digit.two)).closedPolygon_covers site
  have hyT := twos_E_key k y hy
  have hcomb : (frameAt (List.replicate (k + 1) Digit.two)).child.modifiedDeck.combine i j =
      (i * (2 * (k : ℤ) + 5) + j * (-2), i * (2 * (k : ℤ) + 3) + j * (4 * (k : ℤ) + 8)) := by
    simp only [PeriodDeck.combine, twos_kernel_explicit, twos_transverse_explicit]
  rw [hcomb] at hc
  obtain ⟨y1, y2⟩ := y
  obtain ⟨c1, c2⟩ := site
  unfold priceIncrement
  have hc1 : c1 = y1 + (i * (2 * (k : ℤ) + 5) + j * (-2)) := by
    have := congrArg Prod.fst hc
    simpa using this
  have hc2 : c2 = y2 + (i * (2 * (k : ℤ) + 3) + j * (4 * (k : ℤ) + 8)) := by
    have := congrArg Prod.snd hc
    simpa using this
  by_cases hev : EvenSite (c1, c2)
  · unfold incomingNeg incomingPos
    simp only [if_pos hev]
    have hA : ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (c1 - 1, c2)) = ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (y1 - 1, y2)) - i := by
      rw [show (c1 - 1, c2) = ((y1 - 1) + (i * (2 * (k : ℤ) + 5) + j * (-2)), y2 + (i * (2 * (k : ℤ) + 3) + j * (4 * (k : ℤ) + 8))) from
        Prod.ext (by rw [hc1]; ring) (by rw [hc2])]
      exact twos_price_lattice k (y1 - 1) y2 i j
    have hB : ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (c1, c2)) = ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (y1, y2)) - i := by
      rw [show (c1, c2) = (y1 + (i * (2 * (k : ℤ) + 5) + j * (-2)), y2 + (i * (2 * (k : ℤ) + 3) + j * (4 * (k : ℤ) + 8))) from Prod.ext (by rw [hc1]) (by rw [hc2])]
      exact twos_price_lattice k y1 y2 i j
    have hC : ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (c1 + 1, c2)) = ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (y1 + 1, y2)) - i := by
      rw [show (c1 + 1, c2) = ((y1 + 1) + (i * (2 * (k : ℤ) + 5) + j * (-2)), y2 + (i * (2 * (k : ℤ) + 3) + j * (4 * (k : ℤ) + 8))) from
        Prod.ext (by rw [hc1]; ring) (by rw [hc2])]
      exact twos_price_lattice k (y1 + 1) y2 i j
    simp only [hA, hB, hC]
    intro h
    apply twos_star_h k hyT
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      constructor <;> linarith
    · right
      constructor <;> linarith
  · unfold incomingNeg incomingPos
    simp only [if_neg hev]
    have hA : ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (c1, c2 - 1)) = ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (y1, y2 - 1)) - i := by
      rw [show (c1, c2 - 1) = (y1 + (i * (2 * (k : ℤ) + 5) + j * (-2)), (y2 - 1) + (i * (2 * (k : ℤ) + 3) + j * (4 * (k : ℤ) + 8))) from
        Prod.ext (by rw [hc1]) (by rw [hc2]; ring)]
      exact twos_price_lattice k y1 (y2 - 1) i j
    have hB : ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (c1, c2)) = ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (y1, y2)) - i := by
      rw [show (c1, c2) = (y1 + (i * (2 * (k : ℤ) + 5) + j * (-2)), y2 + (i * (2 * (k : ℤ) + 3) + j * (4 * (k : ℤ) + 8))) from Prod.ext (by rw [hc1]) (by rw [hc2])]
      exact twos_price_lattice k y1 y2 i j
    have hC : ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (c1, c2 + 1)) = ((frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) (y1, y2 + 1)) - i := by
      rw [show (c1, c2 + 1) = (y1 + (i * (2 * (k : ℤ) + 5) + j * (-2)), (y2 + 1) + (i * (2 * (k : ℤ) + 3) + j * (4 * (k : ℤ) + 8))) from
        Prod.ext (by rw [hc1]) (by rw [hc2]; ring)]
      exact twos_price_lattice k y1 (y2 + 1) i j
    simp only [hA, hB, hC]
    intro h
    apply twos_star_v k hyT
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      constructor <;> linarith
    · right
      constructor <;> linarith

end FLatticePaper.Induction
