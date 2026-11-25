import FLatticePaper.Plane.Induction.TwosWhiteSel
import FLatticePaper.Plane.Induction.TwosSpecialCentres

/-! Twos flatness, the selection at a non-free white tile centre `p` other than `(a, 2a-1)`: its only admissible alias is `p`
itself, so `TwosSel` keeps the candidate displacement `candDisp p` exactly when `CandGuard p` holds. -/

noncomputable section

namespace FLatticePaper.TwosEPolicy

open FLatticePaper FLatticePaper.Construction FLatticePaper.Induction Farey
open scoped Classical

/-- A native alias of a non-free tile point is the point itself. -/
theorem cand_native_alias {a : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) {p1 p2 u1 u2 : ℤ}
    (hp : TwosTile a (p1, p2)) (hpF : ¬ FreeSite a p1 p2) (hu : AliasOf a (p1, p2) (u1, u2))
    (hN : NativeT a u1 u2) : u1 = p1 ∧ u2 = p2 := by
  have hk : classKey a (u1, u2) = classKey a (p1, p2) := alias_classKey hu
  rcases native_cases hN with hT | ⟨hFq, hNq⟩ | ⟨hFq, hNq⟩
  · exact tile_unique ha he2 hT hp hk
  · exfalso
    have hq : TwosTile a (u1 - (a + 1), u2 - (a - 1)) := free_tile hFq hNq
    have hU := classKey_add_U a (u1 - (a + 1)) (u2 - (a - 1))
    rw [show u1 - (a + 1) + (a + 1) = u1 by ring, show u2 - (a - 1) + (a - 1) = u2 by ring] at hU
    obtain ⟨e1, e2⟩ := tile_unique ha he2 hp hq (by rw [← hk, hU])
    exact hpF (e1 ▸ e2 ▸ hFq)
  · exfalso
    have hq : TwosTile a (u1 + 2, u2 - 2 * a) := free_tile hFq hNq
    have hV := classKey_add_V a (u1 + 2) (u2 - 2 * a)
    rw [show u1 + 2 + -2 = u1 by ring, show u2 - 2 * a + 2 * a = u2 by ring] at hV
    obtain ⟨e1, e2⟩ := tile_unique ha he2 hp hq (by rw [← hk, hV])
    exact hpF (by rw [e1, e2]; exact hFq)

/-- A non-free tile point other than `(a, 2a-1)` has no free alias. -/
theorem nonfree_no_free_alias {a : ℤ} (ha : 4 ≤ a) (he2 : a % 2 = 0) {p1 p2 u1 u2 : ℤ}
    (hp : TwosTile a (p1, p2)) (hpF : ¬ FreeSite a p1 p2) (hpS : ¬ (p1 = a ∧ p2 = 2 * a - 1))
    (hu : AliasOf a (p1, p2) (u1, u2)) (huF : FreeSite a u1 u2) : False := by
  by_cases hN : NativeT a u1 u2
  · have h := cand_native_alias ha he2 hp hpF hu hN
    obtain ⟨e1, e2⟩ := h
    rw [e1, e2] at huF
    exact hpF huF
  · exfalso
    obtain ⟨hx, hy⟩ := free_nonnative_eq ha huF hN
    have hk : classKey a (u1, u2) = classKey a (p1, p2) := alias_classKey hu
    rw [hx, hy] at hk
    have hU := classKey_add_U a (-1) a
    rw [show (-1 : ℤ) + (a + 1) = a by ring, show a + (a - 1) = 2 * a - 1 by ring] at hU
    obtain ⟨e1, e2⟩ := tile_unique ha he2 hp (tile_a_2a1 ha) (by rw [← hk, hU])
    exact hpS ⟨e1, e2⟩

/-- **The selection at a non-free white tile centre.** Its only selected input is the candidate displacement, and only
when the candidate guard holds. -/
theorem twosSel_cand_tile {a : ℤ} {k : ℕ} (hk : a = 2 * (k : ℤ) + 4) {F : Field} {p1 p2 i1 i2 : ℤ}
    (hp : TwosTile a (p1, p2)) (hpF : ¬ FreeSite a p1 p2) (hpS : ¬ (p1 = a ∧ p2 = 2 * a - 1))
    (hl : laplacian F (p1, p2) = 0) (h : TwosSel a 1 F (p1, p2) (i1, i2)) :
    CandGuard a p1 p2 ∧ (i1, i2) = (p1 + (candDisp a p1 p2).1, p2 + (candDisp a p1 p2).2) := by
  have ha : (4 : ℤ) ≤ a := by omega
  have he2 : a % 2 = 0 := by omega
  rcases h with ⟨hm, -⟩ | ⟨-, h2 | ⟨hnfc, ⟨⟨u1, u2⟩, hu, hN, hG, hi⟩⟩⟩
  · rw [hl] at hm
    norm_num at hm
  · obtain ⟨⟨u1, u2⟩, hu, huF, -⟩ := h2
    exact absurd huF (fun hf => nonfree_no_free_alias ha he2 hp hpF hpS hu hf)
  · obtain ⟨e1, e2⟩ := cand_native_alias ha he2 hp hpF hu hN
    subst e1
    subst e2
    exact ⟨hG, hi⟩

end FLatticePaper.TwosEPolicy
