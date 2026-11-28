import FLatticePaper.Tiles.CorrectedPureBridges
import FLatticePaper.Tiles.CorrectedPhysicalFaces

/-! The two checkerboard classes of a translated enlarged bridge. -/

namespace FLatticePaper.Tiles.CorrectedBridgeGrid

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles Standard
open CorrectedPhysicalFaces CorrectedCellsBands CorrectedPureBridges

private theorem bounds (z t : Site) : z∈shift grid t ↔
    (0≤z.1-t.1 ∧ z.1-t.1≤2) ∧ (0≤z.2-t.2 ∧ z.2-t.2≤2) :=
  mem_shift.trans (Finset.mem_product.trans (and_congr Finset.mem_Icc Finset.mem_Icc))

/-- The five even sites of the enlarged bridge after an even translation. -/
theorem even_sites (z t : Site) (parity : oddSite z=false)
    (even : EvenPoint t) : z∈shift grid t ↔ z=t+((0,0):Site) ∨ z=t+((0,2):Site) ∨ z=t+((1,1):Site) ∨ z=t+((2,0):Site) ∨ z=t+((2,2):Site) := by
  obtain ⟨x,y⟩ := z
  obtain ⟨a,b⟩ := t
  have p : (x+y)%2≠1 := of_decide_eq_false parity
  change (a+b)%2=0 at even
  rw [bounds]
  change ((0≤x-a ∧ x-a≤2) ∧ (0≤y-b ∧ y-b≤2)) ↔ _
  simp only [Prod.ext_iff,Prod.fst_add,Prod.snd_add]
  constructor
  · rintro ⟨⟨x0,x2⟩,y0,y2⟩
    rcases (show x-a=0 ∨ x-a=1 ∨ x-a=2 by omega) with dx|dx|dx <;>
      rcases (show y-b=0 ∨ y-b=1 ∨ y-b=2 by omega) with dy|dy|dy <;> omega
  · omega

/-- The four odd sites of the enlarged bridge after an even translation. -/
theorem odd_sites (z t : Site) (parity : oddSite z=true)
    (even : EvenPoint t) : z∈shift grid t ↔ z=t+((0,1):Site) ∨ z=t+((1,0):Site) ∨ z=t+((1,2):Site) ∨ z=t+((2,1):Site) := by
  obtain ⟨x,y⟩ := z
  obtain ⟨a,b⟩ := t
  have p : (x+y)%2=1 := of_decide_eq_true parity
  change (a+b)%2=0 at even
  rw [bounds]
  change ((0≤x-a ∧ x-a≤2) ∧ (0≤y-b ∧ y-b≤2)) ↔ _
  simp only [Prod.ext_iff,Prod.fst_add,Prod.snd_add]
  constructor
  · rintro ⟨⟨x0,x2⟩,y0,y2⟩
    rcases (show x-a=0 ∨ x-a=1 ∨ x-a=2 by omega) with dx|dx|dx <;>
      rcases (show y-b=0 ∨ y-b=1 ∨ y-b=2 by omega) with dy|dy|dy <;> omega
  · omega

end FLatticePaper.Tiles.CorrectedBridgeGrid
