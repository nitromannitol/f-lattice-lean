import FLatticePaper.Plane.Induction.ChildFrame
import FLatticePaper.Plane.Induction.Binary

/-! Task w3, step C (correction): the free V point `V'_1 = (0,1)` is white, `laplacian F (0,1) = 0`.

Its two incoming neighbours are `(0,0)` and `(0,2)`, with `s`-grades `0`, `2(d − n)` and the middle `d − n`, all inside the
harmonic `s`-strip `[1 − 2d, 2(d + n) − 1]` of the child frame (`HasStrips`, second conjunct). So `F` is `harmonicGrid` at the
three points, and the laplacian is that of `harmonicGrid`, which vanishes (`harmonicGrid_harmonic`). -/

namespace FLatticePaper.VWhite

open Farey FLatticePaper FLatticePaper.Induction

theorem laplacian_V1_zero (C : ChildFrame) {G : Field} (hS : C.HasStrips G) :
    laplacian G ((0 : ℤ), (1 : ℤ)) = 0 := by
  obtain ⟨hn0, hnd, hdn, hd3, -⟩ := C.child_facts
  have hsv : ∀ z : Site, C.sGrade z = (C.child.den + C.child.num) * z.1 + (C.child.den - C.child.num) * z.2 := by
    intro z
    rfl
  have h0 : G ((0 : ℤ), (0 : ℤ)) = harmonicGrid ((0 : ℤ), (0 : ℤ)) := by
    refine hS.2 _ ?_ ?_
    · rw [hsv]
      simp
      omega
    · rw [hsv]
      simp
      omega
  have h1 : G ((0 : ℤ), (1 : ℤ)) = harmonicGrid ((0 : ℤ), (1 : ℤ)) := by
    refine hS.2 _ ?_ ?_
    · rw [hsv]
      simp
      omega
    · rw [hsv]
      simp
      omega
  have h2 : G ((0 : ℤ), (2 : ℤ)) = harmonicGrid ((0 : ℤ), (2 : ℤ)) := by
    refine hS.2 _ ?_ ?_
    · rw [hsv]
      simp
      omega
    · rw [hsv]
      simp
      omega
  have hlap := harmonicGrid_harmonic ((0 : ℤ), (1 : ℤ))
  have hodd : ¬ EvenSite ((0 : ℤ), (1 : ℤ)) := by
    unfold EvenSite
    norm_num
  have e1 : incomingNeg ((0 : ℤ), (1 : ℤ)) = ((0 : ℤ), (0 : ℤ)) := by
    unfold incomingNeg
    rw [if_neg hodd]
    norm_num
  have e2 : incomingPos ((0 : ℤ), (1 : ℤ)) = ((0 : ℤ), (2 : ℤ)) := by
    unfold incomingPos
    rw [if_neg hodd]
    norm_num
  unfold laplacian at hlap ⊢
  rw [e1, e2] at hlap ⊢
  rw [h0, h1, h2]
  exact hlap

end FLatticePaper.VWhite
