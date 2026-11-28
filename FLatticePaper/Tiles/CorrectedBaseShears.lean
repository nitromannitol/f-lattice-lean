import FLatticePaper.Tiles.CorrectedRegisterFaces
import FLatticePaper.Tiles.CorrectedFiniteFaces
import FLatticePaper.Tiles.CorrectedPlacedDiagram

/-! The two integral shears and the finite determinant tests for alternate base polygons. -/

namespace FLatticePaper.Tiles.CorrectedBaseShears

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open CorrectedCellsBands CorrectedRegisterDiagram CorrectedRegisterFaces CorrectedFiniteFaces CorrectedLevelTests
open CorrectedFaceBounds

/-- The long coordinate of the pure-three base is the sum of the physical coordinates.
For the pure-two base the transverse coordinate is their difference. -/
def shear (three : Bool) (z : Site) : Site := if three then (z.1+z.2,z.2) else (z.1,z.2-z.1)

theorem cross_shear (three : Bool) (a b : Site) : cross (shear three a) (shear three b)=cross a b := by
  cases three <;> dsimp [shear,cross] <;> ring

def horizontal (par : Bool) (sec : Fin 3) : Site :=
  if par then (0,1) else if sec=0 then (1,1) else (-2,0)
def vertical (par : Bool) (sec : Fin 3) : Site :=
  if !par then (0,1) else if sec=2 then (1,1) else (-2,0)

def point (b : CorrectedPlacedDiagram.Block) (z : Site) (par : Bool) (sec : Fin 3) (i : Fin 4) : Site :=
  let u := z-b.c
  let p := horizontal par sec
  let q := vertical par sec
  match i.val with
  | 0 => u+p
  | 1 => u+((-1,1):Site)-p-b.b
  | 2 => u-((1,0):Site)-mulI q
  | _ => u+((0,1):Site)+mulI q-b.a

def read (a b : Site) (Z : Fin 4 → Site) (i : Fin 4) : Probe :=
  if i.val<2 then ⟨(Z i).2,(Z i).1,a.1,a.2⟩ else ⟨(Z i).1,(Z i).2,b.2,b.1⟩

def probes (three : Bool) (b : CorrectedPlacedDiagram.Block) (z : Site) (par : Bool) (sec : Fin 3) :=
  read (shear three b.a) (shear three b.b) (fun i => shear three (point b z par sec i))

private theorem four (a b : Site) (U : Fin 4 → Site) :
    exact (read a b U) ↔ 0≤cross a (U 0) ∧ cross a (U 1)≤0 ∧ 0≤cross (U 2) b ∧ cross (U 3) b≤0 := by
  unfold exact
  constructor
  · intro h
    have a₀ := h 0; have a₁ := h 1; have b₀ := h 2; have b₁ := h 3
    norm_num [read,cross] at a₀ a₁ b₀ b₁ ⊢
    exact ⟨by linarith,by linarith,by linarith,by linarith⟩
  · rintro ⟨a₀,a₁,b₀,b₁⟩ i
    fin_cases i
    · simpa [read,cross] using a₀
    · simpa [read,cross] using a₁
    · simpa [read,cross,mul_comm] using b₀
    · simpa [read,cross,mul_comm] using b₁

/-- The displayed inequalities in shear coordinates test the physical translated polygon. -/
theorem band (three : Bool) (a b c z : Site) (par : Bool) (sec : Fin 3)
    (p : oddSite (z-c)=par)
    (A : probe a par=horizontal par sec) (B : probe (CorrectedCellsBands.transverse b) (!par)=vertical par sec) :
    Band a b 0 0 (z-c) ↔ exact (probes three ⟨c,a,b,0,0⟩ z par sec) := by
  unfold probes
  rw [four]
  simp only [cross_shear,point]
  unfold Band allowances
  rw [p,A,B]
  generalize horizontal par sec=P
  generalize vertical par sec=Q
  simp [cross,mulI]
  ring_nf
  omega

end FLatticePaper.Tiles.CorrectedBaseShears
