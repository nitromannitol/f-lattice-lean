import FLatticePaper.Graph
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Group.Action.Defs

/-! # The two adjacent-chart offer identities of Q34 (W3, W4), as algebra on the sheet formulas

With `A z = Fp (z − lv)`, `C z = Fp (z − lv − e) + S (z − lv) + c` where `S x = n_q x_1 − d_q x_2`, `U_q = (d_q, n_q)`, `e = V_q + ε U_q`,
`V_q = (n_q − d_q, n_q + d_q)`:

* `S U_q = n_q d_q − d_q n_q = 0`, so `S` is invariant under `· − ε U_q`;
* `C (z − ε U_q) − A z = Ψ z + ψ₊ (x − e)` with `ψ₊ x = Fp (x − ε U_q) − Fp x` (the positive adjacent offer, W3);
* `C (z + ε U_q) − A z = B x` with `B x = Fp (x − V_q) − Fp x + S x + c` (the negative adjacent offer, W4), since `x + ε U_q − e = x − V_q`.

These are the exact identities checked numerically (T4). The sheets are abstract here; `FLatticePaper.Induction` instantiates them. -/

namespace FLatticePaper.AdjacentOffers

/-- The offer identity of the positive adjacent chart (W3). -/
theorem offer_plus (Fp : Site → ℤ) (eN eD c ε : ℤ) (lv e z : Site) :
    (Fp (z - ε • ((eD, eN) : Site) - lv - e) +
        (eN * (z - ε • ((eD, eN) : Site) - lv).1 - eD * (z - ε • ((eD, eN) : Site) - lv).2) + c) - Fp (z - lv) =
      ((Fp (z - lv - e) + (eN * (z - lv).1 - eD * (z - lv).2) + c) - Fp (z - lv)) +
        (Fp (z - lv - e - ε • ((eD, eN) : Site)) - Fp (z - lv - e)) := by
  have h1 : z - ε • ((eD, eN) : Site) - lv - e = (z - lv - e) - ε • ((eD, eN) : Site) := by
    ext <;> simp <;> ring
  have h2 : eN * (z - ε • ((eD, eN) : Site) - lv).1 - eD * (z - ε • ((eD, eN) : Site) - lv).2 =
      eN * (z - lv).1 - eD * (z - lv).2 := by
    simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_sub, Prod.snd_sub, smul_eq_mul]
    ring
  rw [h1, h2]
  ring

/-- The offer identity of the negative adjacent chart (W4). -/
theorem offer_minus (Fp : Site → ℤ) (eN eD c ε : ℤ) (lv e Vq z : Site)
    (hVq : Vq = e - ε • ((eD, eN) : Site)) :
    (Fp (z + ε • ((eD, eN) : Site) - lv - e) +
        (eN * (z + ε • ((eD, eN) : Site) - lv).1 - eD * (z + ε • ((eD, eN) : Site) - lv).2) + c) - Fp (z - lv) =
      Fp (z - lv - Vq) - Fp (z - lv) + (eN * (z - lv).1 - eD * (z - lv).2) + c := by
  have h1 : z + ε • ((eD, eN) : Site) - lv - e = (z - lv) - Vq := by
    rw [hVq]
    ext <;> simp <;> ring
  have h2 : eN * (z + ε • ((eD, eN) : Site) - lv).1 - eD * (z + ε • ((eD, eN) : Site) - lv).2 =
      eN * (z - lv).1 - eD * (z - lv).2 := by
    simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, smul_eq_mul]
    ring
  rw [h1, h2]
  ring

end FLatticePaper.AdjacentOffers
