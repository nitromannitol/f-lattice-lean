import FLatticePaper.Plane.Induction.TwosCandSel
import FLatticePaper.Plane.Induction.TwosRhoCases
import FLatticePaper.Plane.Induction.TwosBlackEvenDrop

/-! Twos flatness, the candidate tile drops (sign `+1`). A white non-free tile centre `p` in a candidate band keeps the
displacement `candDisp p`; when the destination is a tile point of the same level, the rank drops by one. -/

noncomputable section

namespace FLatticePaper.TwosEPolicy

set_option maxHeartbeats 400000 in
/-- The `E` band with the destination `(x+1, y)` a tile point: the rank drops by one on a flat edge. -/
theorem candE_tile_drop {a x y : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) (hp : TwosTile a (x, y))
    (hpF : ¬ FreeSite a x y) (hband : y - x = a - 2 ∧ 2 ≤ x ∧ x ≤ a - 1)
    (hi : TwosTile a (x + 1, y)) (hL : twosLev a (x + 1) y = twosLev a x y) :
    rhoTwos a 1 (x + 1, y) < rhoTwos a 1 (x, y) := by
  have hsp : ¬ (x = a ∧ y = 2 * a - 1) := by
    intro h
    omega
  have hspi : ¬ (x + 1 = a ∧ y = 2 * a - 1) := by
    intro h
    omega
  unfold twosLev at hL
  split_ifs at hL
  all_goals
    by_cases fi : FreeSite a (x + 1) y
    · rcases rho_bulk_cases ha he2 hp hpF hsp with Hp | Hp | Hp | Hp | Hp | Hp | Hp <;>
        rcases rho_free_cases ha he2 hi fi with Hi | Hi | Hi | Hi | Hi <;> omega
    · have dp1 := bulk_nodup_U hp hpF
      have dp2 := bulk_nodup_V hp hpF
      have di1 := bulk_nodup_U hi fi
      have di2 := bulk_nodup_V hi fi
      rcases rho_bulk_cases ha he2 hp hpF hsp with Hp | Hp | Hp | Hp | Hp | Hp | Hp <;>
        rcases rho_bulk_cases ha he2 hi fi hspi with Hi | Hi | Hi | Hi | Hi | Hi | Hi <;> omega

end FLatticePaper.TwosEPolicy
