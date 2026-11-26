import FLatticePaper.Plane.Induction.W1OffCollar
import FLatticePaper.Plane.Induction.W1Constructor

/-! # The pieces of a free V site, in the child's grades

For a free V site `u` of the child `(n, d)` (`freeVn n d u`: the closed rectangle, not the closed rectangle one step to the left,
and the V spectrum), the grades `t(u)`, `s(u)` lie in one of three pieces:

* `O` (odd `u`): `n − T ≤ t ≤ d`, `2 − d + n ≤ s ≤ d + n − 2`;
* `E0` (even `u`, `s ≤ 2n`): `2 − T ≤ t ≤ d + n − 2`, `0 ≤ s ≤ 2n`;
* `E1` (even `u`, `2n + 2 ≤ s`): `2 − T ≤ t ≤ 2n − T − 1`, `2n + 2 ≤ s ≤ d + n − 2`.

`T = d² + 2dn − n²`. The left neighbour of an `E1` site is outside the closed rectangle, which is the only source of the upper
bound `2n − T − 1` on `t`. -/

namespace FLatticePaper.OppPieces

open FLatticePaper FLatticePaper.W1 FLatticePaper.W1OffCollar

theorem freeVn_pieces {n d : ℤ} {u : Site} (hn : 3 ≤ n) (hnd : n + 2 ≤ d) (h : freeVn n d u) :
    (¬ EvenSite u ∧ n - w1T n d ≤ w1t n d u ∧ w1t n d u ≤ d ∧ 2 - d + n ≤ w1s n d u ∧ w1s n d u ≤ d + n - 2) ∨
    (EvenSite u ∧ 2 - w1T n d ≤ w1t n d u ∧ w1t n d u ≤ d + n - 2 ∧ 0 ≤ w1s n d u ∧ w1s n d u ≤ 2 * n) ∨
    (EvenSite u ∧ 2 * n + 2 ≤ w1s n d u ∧ w1s n d u ≤ d + n - 2 ∧ 2 - w1T n d ≤ w1t n d u ∧
      w1t n d u ≤ 2 * n - w1T n d - 1) := by
  obtain ⟨hcr, hnot, hsp⟩ := h
  rw [closedRect_iff] at hcr hnot
  have ht' : w1t n d (u.1 - 1, u.2) = w1t n d u - n := by unfold w1t; ring
  have hs' : w1s n d (u.1 - 1, u.2) = w1s n d u - (d + n) := by unfold w1s; ring
  have hpar' : EvenSite (u.1 - 1, u.2) ↔ ¬ EvenSite u := by unfold EvenSite; omega
  rw [hpar', ht', hs'] at hnot
  unfold vSp at hsp
  generalize w1t n d u = t at hcr hnot hsp ⊢
  generalize w1s n d u = s at hcr hnot hsp ⊢
  generalize w1T n d = T at hcr hnot hsp ⊢
  unfold EvenSite at *
  omega

end FLatticePaper.OppPieces
