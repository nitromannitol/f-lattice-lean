import FLatticePaper.Plane.Induction.TwosCandDrop

noncomputable section

namespace FLatticePaper.TwosEPolicy

set_option maxHeartbeats 400000 in
/-- The W band: the destination `(x + -1, y + 0)` is a tile point of the same level, and the rank drops by one. -/
theorem candW {a x y : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) (hp : TwosTile a (x, y))
    (hpF : ¬ FreeSite a x y) (hband : (y - x = a ∧ 1 ≤ x ∧ x ≤ a - 2))
    (hi : TwosTile a (x + (-1), y + (0))) (hL : twosLev a (x + (-1)) (y + (0)) = twosLev a x y) :
    rhoTwos a 1 (x + (-1), y + (0)) < rhoTwos a 1 (x, y) := by
  have hsp : ¬ (x = a ∧ y = 2 * a - 1) := by
    intro h
    omega
  have hspi : ¬ (x + (-1) = a ∧ y + (0) = 2 * a - 1) := by
    intro h
    omega
  unfold twosLev at hL
  split_ifs at hL
  all_goals
    by_cases fi : FreeSite a (x + (-1)) (y + (0))
    · rcases rho_bulk_cases ha he2 hp hpF hsp with Hp | Hp | Hp | Hp | Hp | Hp | Hp <;>
        rcases rho_free_cases ha he2 hi fi with Hi | Hi | Hi | Hi | Hi <;> omega
    · have dp1 := bulk_nodup_U hp hpF
      have dp2 := bulk_nodup_V hp hpF
      have di1 := bulk_nodup_U hi fi
      have di2 := bulk_nodup_V hi fi
      unfold FreeSite FreeHSite FreeVSite at fi hpF
      rcases rho_bulk_cases ha he2 hp hpF hsp with Hp | Hp | Hp | Hp | Hp | Hp | Hp <;>
        rcases rho_bulk_cases ha he2 hi fi hspi with Hi | Hi | Hi | Hi | Hi | Hi | Hi <;> omega

set_option maxHeartbeats 400000 in
/-- The Low-down band: the destination `(x + 0, y + -1)` is a tile point of the same level, and the rank drops by one. -/
theorem candLow_down {a x y : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) (hp : TwosTile a (x, y))
    (hpF : ¬ FreeSite a x y) (hband : ((y - x) % 2 = 1 ∧ -1 ≤ y - x ∧ y - x ≤ a - 3 ∧ 1 ≤ x ∧ x ≤ a ∧ y < a - 1 ∧ ¬ (y - x = -1 ∧ x = 1)))
    (hi : TwosTile a (x + (0), y + (-1))) (hL : twosLev a (x + (0)) (y + (-1)) = twosLev a x y) :
    rhoTwos a 1 (x + (0), y + (-1)) < rhoTwos a 1 (x, y) := by
  have hsp : ¬ (x = a ∧ y = 2 * a - 1) := by
    intro h
    omega
  have hspi : ¬ (x + (0) = a ∧ y + (-1) = 2 * a - 1) := by
    intro h
    omega
  unfold twosLev at hL
  split_ifs at hL
  all_goals
    by_cases fi : FreeSite a (x + (0)) (y + (-1))
    · rcases rho_bulk_cases ha he2 hp hpF hsp with Hp | Hp | Hp | Hp | Hp | Hp | Hp <;>
        rcases rho_free_cases ha he2 hi fi with Hi | Hi | Hi | Hi | Hi <;> omega
    · have dp1 := bulk_nodup_U hp hpF
      have dp2 := bulk_nodup_V hp hpF
      have di1 := bulk_nodup_U hi fi
      have di2 := bulk_nodup_V hi fi
      unfold FreeSite FreeHSite FreeVSite at fi hpF
      rcases rho_bulk_cases ha he2 hp hpF hsp with Hp | Hp | Hp | Hp | Hp | Hp | Hp <;>
        rcases rho_bulk_cases ha he2 hi fi hspi with Hi | Hi | Hi | Hi | Hi | Hi | Hi <;> omega

set_option maxHeartbeats 400000 in
/-- The Low-up band: the destination `(x + 0, y + 1)` is a tile point of the same level, and the rank drops by one. -/
theorem candLow_up {a x y : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) (hp : TwosTile a (x, y))
    (hpF : ¬ FreeSite a x y) (hband : ((y - x) % 2 = 1 ∧ -1 ≤ y - x ∧ y - x ≤ a - 3 ∧ 1 ≤ x ∧ x ≤ a ∧ a - 1 < y ∧ ¬ (y - x = -1 ∧ x = 1)))
    (hi : TwosTile a (x + (0), y + (1))) (hL : twosLev a (x + (0)) (y + (1)) = twosLev a x y) :
    rhoTwos a 1 (x + (0), y + (1)) < rhoTwos a 1 (x, y) := by
  have hsp : ¬ (x = a ∧ y = 2 * a - 1) := by
    intro h
    omega
  have hspi : ¬ (x + (0) = a ∧ y + (1) = 2 * a - 1) := by
    intro h
    omega
  unfold twosLev at hL
  split_ifs at hL
  all_goals
    by_cases fi : FreeSite a (x + (0)) (y + (1))
    · rcases rho_bulk_cases ha he2 hp hpF hsp with Hp | Hp | Hp | Hp | Hp | Hp | Hp <;>
        rcases rho_free_cases ha he2 hi fi with Hi | Hi | Hi | Hi | Hi <;> omega
    · have dp1 := bulk_nodup_U hp hpF
      have dp2 := bulk_nodup_V hp hpF
      have di1 := bulk_nodup_U hi fi
      have di2 := bulk_nodup_V hi fi
      unfold FreeSite FreeHSite FreeVSite at fi hpF
      rcases rho_bulk_cases ha he2 hp hpF hsp with Hp | Hp | Hp | Hp | Hp | Hp | Hp <;>
        rcases rho_bulk_cases ha he2 hi fi hspi with Hi | Hi | Hi | Hi | Hi | Hi | Hi <;> omega

set_option maxHeartbeats 400000 in
/-- The High-down band: the destination `(x + 0, y + -1)` is a tile point of the same level, and the rank drops by one. -/
theorem candHigh_down {a x y : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) (hp : TwosTile a (x, y))
    (hpF : ¬ FreeSite a x y) (hband : ((y - x) % 2 = 1 ∧ a + 1 ≤ y - x ∧ y - x ≤ 2 * a - 1 ∧ 0 ≤ x ∧ x ≤ a - 1 ∧ y < 2 * a - 1 ∧ ¬ (y - x = 2 * a - 1 ∧ x = a - 1)))
    (hi : TwosTile a (x + (0), y + (-1))) (hL : twosLev a (x + (0)) (y + (-1)) = twosLev a x y) :
    rhoTwos a 1 (x + (0), y + (-1)) < rhoTwos a 1 (x, y) := by
  have hsp : ¬ (x = a ∧ y = 2 * a - 1) := by
    intro h
    omega
  have hspi : ¬ (x + (0) = a ∧ y + (-1) = 2 * a - 1) := by
    intro h
    omega
  unfold twosLev at hL
  split_ifs at hL
  all_goals
    by_cases fi : FreeSite a (x + (0)) (y + (-1))
    · rcases rho_bulk_cases ha he2 hp hpF hsp with Hp | Hp | Hp | Hp | Hp | Hp | Hp <;>
        rcases rho_free_cases ha he2 hi fi with Hi | Hi | Hi | Hi | Hi <;> omega
    · have dp1 := bulk_nodup_U hp hpF
      have dp2 := bulk_nodup_V hp hpF
      have di1 := bulk_nodup_U hi fi
      have di2 := bulk_nodup_V hi fi
      unfold FreeSite FreeHSite FreeVSite at fi hpF
      rcases rho_bulk_cases ha he2 hp hpF hsp with Hp | Hp | Hp | Hp | Hp | Hp | Hp <;>
        rcases rho_bulk_cases ha he2 hi fi hspi with Hi | Hi | Hi | Hi | Hi | Hi | Hi <;> omega

set_option maxHeartbeats 400000 in
/-- The High-up band: the destination `(x + 0, y + 1)` is a tile point of the same level, and the rank drops by one. -/
theorem candHigh_up {a x y : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) (hp : TwosTile a (x, y))
    (hpF : ¬ FreeSite a x y) (hband : ((y - x) % 2 = 1 ∧ a + 1 ≤ y - x ∧ y - x ≤ 2 * a - 1 ∧ 0 ≤ x ∧ x ≤ a - 1 ∧ 2 * a - 1 < y ∧ ¬ (y - x = 2 * a - 1 ∧ x = a - 1)))
    (hi : TwosTile a (x + (0), y + (1))) (hL : twosLev a (x + (0)) (y + (1)) = twosLev a x y) :
    rhoTwos a 1 (x + (0), y + (1)) < rhoTwos a 1 (x, y) := by
  have hsp : ¬ (x = a ∧ y = 2 * a - 1) := by
    intro h
    omega
  have hspi : ¬ (x + (0) = a ∧ y + (1) = 2 * a - 1) := by
    intro h
    omega
  unfold twosLev at hL
  split_ifs at hL
  all_goals
    by_cases fi : FreeSite a (x + (0)) (y + (1))
    · rcases rho_bulk_cases ha he2 hp hpF hsp with Hp | Hp | Hp | Hp | Hp | Hp | Hp <;>
        rcases rho_free_cases ha he2 hi fi with Hi | Hi | Hi | Hi | Hi <;> omega
    · have dp1 := bulk_nodup_U hp hpF
      have dp2 := bulk_nodup_V hp hpF
      have di1 := bulk_nodup_U hi fi
      have di2 := bulk_nodup_V hi fi
      unfold FreeSite FreeHSite FreeVSite at fi hpF
      rcases rho_bulk_cases ha he2 hp hpF hsp with Hp | Hp | Hp | Hp | Hp | Hp | Hp <;>
        rcases rho_bulk_cases ha he2 hi fi hspi with Hi | Hi | Hi | Hi | Hi | Hi | Hi <;> omega

end FLatticePaper.TwosEPolicy
