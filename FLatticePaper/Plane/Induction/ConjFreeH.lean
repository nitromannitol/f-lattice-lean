import FLatticePaper.Plane.Induction.FreeVWindow
import FLatticePaper.Plane.Induction.NativeCases
import FLatticePaper.Plane.Induction.S3FreeBoundary

/-! Task 72 / Q31 psi, step (1): membership in the free H arc of a child frame.

`freeH = closedPolygon ∩ {z | z − (0,1) ∉ closedPolygon} ∩ {z | hSpectrum (tGrade z)}`. The spectrum condition is a condition on the
grade `t` alone, and the exit condition `z − (0,1) ∉ closedPolygon` follows from it: the shift by `(0,1)` moves `t` by `d` and flips the
parity, which pushes `t` out of the window of the other parity. -/

namespace FLatticePaper.ConjFreeH

open FLatticePaper FLatticePaper.Induction

/-- **The exit of a spectrum point.** If `t(w)` is in the H spectrum, `w − (0, 1)` is outside the closed polygon. -/
theorem exit_of_hSpec (C : ChildFrame) (w : Site) (hsp : C.hSpectrum (C.tGrade w)) :
    (w.1, w.2 - 1) ∉ C.closedPolygon := by
  obtain ⟨hn0, hnd, hd2, hd3, hT⟩ := C.child_facts
  obtain ⟨hco1, hco2⟩ := C.child_odd
  have hp := NativeCases.tGrade_parity C w
  have hp' := NativeCases.tGrade_parity C (w.1, w.2 - 1)
  have ht' : C.tGrade (w.1, w.2 - 1) = C.tGrade w + C.child.den := by
    unfold ChildFrame.tGrade
    ring
  unfold ChildFrame.hSpectrum at hsp
  intro hmem
  by_cases he : EvenSite (w.1, w.2 - 1)
  · obtain ⟨⟨-, ht1⟩, -⟩ := (FreeVWindow.mem_closedPolygon_even C he).mp hmem
    unfold EvenSite at he
    rcases hsp with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · omega
    · omega
  · obtain ⟨⟨ht0, ht1⟩, -⟩ := (FreeVWindow.mem_closedPolygon_odd C he).mp hmem
    unfold EvenSite at he
    rcases hsp with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · omega
    · omega

end FLatticePaper.ConjFreeH
