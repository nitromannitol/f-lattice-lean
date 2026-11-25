import FLatticePaper.Plane.Induction.TwosCandAll

noncomputable section

namespace FLatticePaper.TwosEPolicy

set_option maxHeartbeats 400000 in
/-- The free V2 (0,j), j even: the destination `(x + 1, y + 0)` is a tile point of the same level, and the rank drops by one. -/
theorem freeV2 {a x y : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) (hp : TwosTile a (x, y))
    (hF : FreeSite a x y) (hband : (x = 0 ∧ 2 ≤ y ∧ y < a ∧ y % 2 = 0))
    (hi : TwosTile a (x + (1), y + (0))) (hL : twosLev a (x + (1)) (y + (0)) = twosLev a x y) :
    rhoTwos a 1 (x + (1), y + (0)) < rhoTwos a 1 (x, y) := by
  have hspi : ¬ (x + (1) = a ∧ y + (0) = 2 * a - 1) := by
    intro h
    omega
  unfold twosLev at hL
  split_ifs at hL
  all_goals
    by_cases fi : FreeSite a (x + (1)) (y + (0))
    · rcases rho_free_cases ha he2 hp hF with Hp | Hp | Hp | Hp | Hp <;>
        rcases rho_free_cases ha he2 hi fi with Hi | Hi | Hi | Hi | Hi <;> omega
    · have di1 := bulk_nodup_U hi fi
      have di2 := bulk_nodup_V hi fi
      unfold FreeSite FreeHSite FreeVSite at fi hF
      rcases rho_free_cases ha he2 hp (by unfold FreeSite FreeHSite FreeVSite; omega) with Hp | Hp | Hp | Hp | Hp <;>
        rcases rho_bulk_cases ha he2 hi fi hspi with Hi | Hi | Hi | Hi | Hi | Hi | Hi <;> omega

set_option maxHeartbeats 400000 in
/-- The free V3 (0,j), j odd: the destination `(x + 0, y + -1)` is a tile point of the same level, and the rank drops by one. -/
theorem freeV3 {a x y : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) (hp : TwosTile a (x, y))
    (hF : FreeSite a x y) (hband : (x = 0 ∧ 1 ≤ y ∧ y < a ∧ y % 2 = 1))
    (hi : TwosTile a (x + (0), y + (-1))) (hL : twosLev a (x + (0)) (y + (-1)) = twosLev a x y) :
    rhoTwos a 1 (x + (0), y + (-1)) < rhoTwos a 1 (x, y) := by
  have hspi : ¬ (x + (0) = a ∧ y + (-1) = 2 * a - 1) := by
    intro h
    omega
  unfold twosLev at hL
  split_ifs at hL
  all_goals
    by_cases fi : FreeSite a (x + (0)) (y + (-1))
    · rcases rho_free_cases ha he2 hp hF with Hp | Hp | Hp | Hp | Hp <;>
        rcases rho_free_cases ha he2 hi fi with Hi | Hi | Hi | Hi | Hi <;> omega
    · have di1 := bulk_nodup_U hi fi
      have di2 := bulk_nodup_V hi fi
      unfold FreeSite FreeHSite FreeVSite at fi hF
      rcases rho_free_cases ha he2 hp (by unfold FreeSite FreeHSite FreeVSite; omega) with Hp | Hp | Hp | Hp | Hp <;>
        rcases rho_bulk_cases ha he2 hi fi hspi with Hi | Hi | Hi | Hi | Hi | Hi | Hi <;> omega

set_option maxHeartbeats 400000 in
/-- The free V4 (-1,j), j odd: the destination `(x + 1, y + 0)` is a tile point of the same level, and the rank drops by one. -/
theorem freeV4 {a x y : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) (hp : TwosTile a (x, y))
    (hF : FreeSite a x y) (hband : (x = -1 ∧ a < y ∧ y < 2 * a ∧ y % 2 = 1))
    (hi : TwosTile a (x + (1), y + (0))) (hL : twosLev a (x + (1)) (y + (0)) = twosLev a x y) :
    rhoTwos a 1 (x + (1), y + (0)) < rhoTwos a 1 (x, y) := by
  have hspi : ¬ (x + (1) = a ∧ y + (0) = 2 * a - 1) := by
    intro h
    omega
  unfold twosLev at hL
  split_ifs at hL
  all_goals
    by_cases fi : FreeSite a (x + (1)) (y + (0))
    · rcases rho_free_cases ha he2 hp hF with Hp | Hp | Hp | Hp | Hp <;>
        rcases rho_free_cases ha he2 hi fi with Hi | Hi | Hi | Hi | Hi <;> omega
    · have di1 := bulk_nodup_U hi fi
      have di2 := bulk_nodup_V hi fi
      unfold FreeSite FreeHSite FreeVSite at fi hF
      rcases rho_free_cases ha he2 hp (by unfold FreeSite FreeHSite FreeVSite; omega) with Hp | Hp | Hp | Hp | Hp <;>
        rcases rho_bulk_cases ha he2 hi fi hspi with Hi | Hi | Hi | Hi | Hi | Hi | Hi <;> omega

set_option maxHeartbeats 400000 in
/-- The free V5 (-1,j), j even: the destination `(x + 0, y + -1)` is a tile point of the same level, and the rank drops by one. -/
theorem freeV5 {a x y : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) (hp : TwosTile a (x, y))
    (hF : FreeSite a x y) (hband : (x = -1 ∧ a < y ∧ y < 2 * a ∧ y % 2 = 0))
    (hi : TwosTile a (x + (0), y + (-1))) (hL : twosLev a (x + (0)) (y + (-1)) = twosLev a x y) :
    rhoTwos a 1 (x + (0), y + (-1)) < rhoTwos a 1 (x, y) := by
  have hspi : ¬ (x + (0) = a ∧ y + (-1) = 2 * a - 1) := by
    intro h
    omega
  unfold twosLev at hL
  split_ifs at hL
  all_goals
    by_cases fi : FreeSite a (x + (0)) (y + (-1))
    · rcases rho_free_cases ha he2 hp hF with Hp | Hp | Hp | Hp | Hp <;>
        rcases rho_free_cases ha he2 hi fi with Hi | Hi | Hi | Hi | Hi <;> omega
    · have di1 := bulk_nodup_U hi fi
      have di2 := bulk_nodup_V hi fi
      unfold FreeSite FreeHSite FreeVSite at fi hF
      rcases rho_free_cases ha he2 hp (by unfold FreeSite FreeHSite FreeVSite; omega) with Hp | Hp | Hp | Hp | Hp <;>
        rcases rho_bulk_cases ha he2 hi fi hspi with Hi | Hi | Hi | Hi | Hi | Hi | Hi <;> omega

end FLatticePaper.TwosEPolicy
