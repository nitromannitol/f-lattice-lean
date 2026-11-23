import FLatticePaper.Plane.Induction.Q3Para10
import FLatticePaper.Plane.Induction.Packet
import FLatticePaper.Plane.Induction.Binary

/-! Task 60, paragraph 10: the white boundary vertex and the black centres.

* `laplacian_eq_zero_of_freeV`: under the packet strips, a vertex of the V cut `freeV` is white (its Laplacian is `0`):
  its star lies in the ordinary h0 strip `1 − 2d ≤ s ≤ 2L − 1`, where `F = h0 = harmonicGrid`, and the Laplacian of
  `harmonicGrid` is `0`.
* `laplacian_add_period`, `child_kernel`: the packet's period `F(z + U) = F z + c` with `U = (d, n)` the child's modified
  kernel (`d + n` even), so the Laplacian is `U`-periodic and `v + U` is white when `v` is.
* `black_centres_contradiction`: `x = v + i U_p` with `x, x + U_q ∈ E` and `v ∈ freeV` force `i ∈ {0, 1}`; for `i = 0`,
  `x = v` is white, and for `i = 1`, `x + U_q = v + U` is white (`U_p + U_q = U`). So `x` and `x + U_q` cannot both be
  black centres. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- The Laplacian of `F` is invariant under a translation `U` that shifts `F` by a constant and preserves the parity. -/
theorem laplacian_add_period (F : Field) (U : Site) (c : ℤ) (hper : ∀ w, F (w + U) = F w + c)
    (hpar : ∀ z, EvenSite (z + U) ↔ EvenSite z) (z : Site) :
    laplacian F (z + U) = laplacian F z := by
  have hN : incomingNeg (z + U) = incomingNeg z + U := by
    unfold incomingNeg
    by_cases h : EvenSite z
    · rw [if_pos ((hpar z).mpr h), if_pos h]
      ext <;> (simp only [Prod.fst_add, Prod.snd_add]; try ring)
    · rw [if_neg (fun h' => h ((hpar z).mp h')), if_neg h]
      ext <;> (simp only [Prod.fst_add, Prod.snd_add]; try ring)
  have hP : incomingPos (z + U) = incomingPos z + U := by
    unfold incomingPos
    by_cases h : EvenSite z
    · rw [if_pos ((hpar z).mpr h), if_pos h]
      ext <;> (simp only [Prod.fst_add, Prod.snd_add]; try ring)
    · rw [if_neg (fun h' => h ((hpar z).mp h')), if_neg h]
      ext <;> (simp only [Prod.fst_add, Prod.snd_add]; try ring)
  unfold laplacian
  rw [hN, hP]
  simp only [hper]
  ring

namespace ChildFrame
variable (frame : ChildFrame)

/-- The child's modified kernel is `(d, n)`, since `d + n` is even. -/
theorem child_kernel : frame.child.modifiedDeck.kernel = (frame.child.den, frame.child.num) := by
  obtain ⟨-, -, -, -, -, -, -, -, hpar⟩ := frame.linear_facts
  simp [Fraction.modifiedDeck, Fraction.periodMultiplicity, hpar]

theorem child_evenSite_add_kernel (z : Site) :
    EvenSite (z + (frame.child.den, frame.child.num)) ↔ EvenSite z := by
  obtain ⟨-, -, -, -, -, -, -, -, hpar⟩ := frame.linear_facts
  unfold EvenSite
  simp only [Prod.fst_add, Prod.snd_add]
  omega

/-- A vertex of the V cut is white: under the packet strips its star is in the h0 strip, where `F = harmonicGrid`. -/
theorem laplacian_eq_zero_of_freeV {F : Field} (hstrips : frame.HasStrips F) {w : Site} (hw : w ∈ frame.freeV) :
    laplacian F w = 0 := by
  obtain ⟨hd, hn, hD, hN0, hND, hq, hn0, hnq, hpar⟩ := frame.linear_facts
  simp only [ChildFrame.freeV, Set.mem_setOf_eq] at hw
  obtain ⟨-, -, hvs⟩ := hw
  unfold ChildFrame.vSpectrum at hvs
  have hh := hstrips.2
  have hlap := harmonicGrid_harmonic w
  unfold laplacian at hlap ⊢
  by_cases he : EvenSite w
  · simp only [incomingNeg, incomingPos, if_pos he] at hlap ⊢
    have h0 : F w = harmonicGrid w := hh w (by omega) (by omega)
    have h1 : F (w.1 - 1, w.2) = harmonicGrid (w.1 - 1, w.2) :=
      hh _ (by rw [frame.sGrade_sub_x w]; omega) (by rw [frame.sGrade_sub_x w]; omega)
    have h2 : F (w.1 + 1, w.2) = harmonicGrid (w.1 + 1, w.2) :=
      hh _ (by rw [frame.sGrade_add_x w]; omega) (by rw [frame.sGrade_add_x w]; omega)
    rw [h0, h1, h2]
    linarith
  · simp only [incomingNeg, incomingPos, if_neg he] at hlap ⊢
    have h0 : F w = harmonicGrid w := hh w (by omega) (by omega)
    have h1 : F (w.1, w.2 - 1) = harmonicGrid (w.1, w.2 - 1) :=
      hh _ (by rw [frame.sGrade_sub_y w]; omega) (by rw [frame.sGrade_sub_y w]; omega)
    have h2 : F (w.1, w.2 + 1) = harmonicGrid (w.1, w.2 + 1) :=
      hh _ (by rw [frame.sGrade_add_y w]; omega) (by rw [frame.sGrade_add_y w]; omega)
    rw [h0, h1, h2]
    linarith

/-- Paragraph 10: `x = v + i U_p` with `x, x + U_q ∈ E` and `v ∈ freeV` cannot have both `x` and `x + U_q` black. -/
theorem black_centres_contradiction {F : Field} (hP : frame.Packet F) {v x : Site} {i : ℤ} (hv : v ∈ frame.freeV)
    (hx : x = v + (i * (2 * frame.parents.odd.den), i * (2 * frame.parents.odd.num)))
    (hxE : x ∈ frame.closedPolygon)
    (hxuE : x + (frame.parents.even.den, frame.parents.even.num) ∈ frame.closedPolygon)
    (hb : laplacian F x = -1)
    (hbu : laplacian F (x + (frame.parents.even.den, frame.parents.even.num)) = -1) : False := by
  have hi := frame.index_of_freeV v x i hx hv hxE hxuE
  have hw := frame.laplacian_eq_zero_of_freeV hP.strips hv
  obtain ⟨hper, -⟩ := hP.periods
  rw [frame.child_kernel] at hper
  rcases hi with rfl | rfl
  · have hxv : x = v := by
      rw [hx]
      simp
    rw [hxv, hw] at hb
    norm_num at hb
  · obtain ⟨hd, hn, -⟩ := frame.linear_facts
    have hxu : x + (frame.parents.even.den, frame.parents.even.num) =
        v + (frame.child.den, frame.child.num) := by
      rw [hx, hd, hn]
      ext <;> (simp only [Prod.fst_add, Prod.snd_add]; try ring)
    rw [hxu, laplacian_add_period F (frame.child.den, frame.child.num) frame.coherentConstantU hper
      frame.child_evenSite_add_kernel v, hw] at hbu
    norm_num at hbu

end ChildFrame

end FLatticePaper.Induction
