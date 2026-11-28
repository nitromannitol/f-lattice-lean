import FLatticePaper.Tiles.CorrectedCellsBands
import FLatticePaper.Tiles.LCorrecProps

/-! The two mixed alternate domains at the first non-base word. -/

namespace FLatticePaper.Tiles.CorrectedFirstPolygons

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open Standard CorrectedCellsBands LCorrecProps

private abbrev K (z : Site) := Band (7,3) (-3,7) 0 0 z

private instance (z : Site) : Decidable (K z) := by
  unfold K Band
  infer_instance

private def square : Tile :=
  (Finset.Icc (-2:ℤ) 7 ×ˢ Finset.Icc (0:ℤ) 9).filter K

private theorem mem_square (z : Site) : z ∈ square ↔ K z := by
  simp only [square,Finset.mem_filter,Finset.mem_product,Finset.mem_Icc,and_iff_right_iff_imp]
  intro h
  obtain ⟨x,y⟩ := z
  by_cases par : (x+y)%2=1 <;> norm_num [K,Band,allowances,cross,oddSite,probe,mulI,par] at h <;> dsimp <;> omega

set_option maxRecDepth 8192 in
set_option maxHeartbeats 400000 in
private theorem domains : altOddT [.one]=square ∪ shift square (-4,2) ∧
    altEvenT [.one]=square ∪ shift square (2,4) := by decide +kernel

/-- In the odd alternate domain the second polygon is translated by minus four and two. -/
theorem odd (z : Site) : z ∈ altOddT [.one] ↔
    Band (7,3) (-3,7) 0 0 z ∨ Band (7,3) (-3,7) 0 0 (z-(-4,2)) := by
  rw [domains.1,Finset.mem_union,mem_shift,mem_square,mem_square]

/-- In the even alternate domain the second polygon is translated by two and four. -/
theorem even (z : Site) : z ∈ altEvenT [.one] ↔
    Band (7,3) (-3,7) 0 0 z ∨ Band (7,3) (-3,7) 0 0 (z-(2,4)) := by
  rw [domains.2,Finset.mem_union,mem_shift,mem_square,mem_square]

end FLatticePaper.Tiles.CorrectedFirstPolygons
