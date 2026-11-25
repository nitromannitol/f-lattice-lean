import FLatticePaper.Plane.Induction.CapRayGrades
import FLatticePaper.Plane.Induction.SheetMonoChild

/-! # The base cap at `n = 1` from the abstract cap

`CapRayGrades.ray_cap_NDgrades` needs only `0 < N < D`, the zero and harmonic windows of the field (here the strips of `G` in the
`(num, den)` grades, exactly its `HasStrips`) and the two sheet monotonicities (`SheetMonoChild`). For `num = 1` the ray start is
`(p, q) = (1, 0)` (`1·1 − d·0 = 2 − 1`, with `p + q = 1` odd), so the H cap of the `n = 1` frame needs no base case. -/

namespace FLatticePaper.CapBaseN1

open FLatticePaper FLatticePaper.Induction

theorem hAS_n1 {frame : ChildFrame} {G : Field} (hP : frame.Packet G)
    (hsig : ∀ w ∈ frame.closedPolygon, G w - G (w - frame.shortShift) ≤ 0)
    (hn1 : frame.child.num = 1) (K : ℕ)
    (hKr : 2 * frame.child.num * (K : ℤ) ≤ 3 * frame.child.den + 3 * frame.child.num - 1) :
    ∃ p q : ℤ, frame.child.num * p - frame.child.den * q = 2 - frame.child.num ∧
      ∀ k : ℕ, k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ G (p + (k : ℤ), q + (k : ℤ)) := by
  obtain ⟨hn0, hnd, -, -, -⟩ := frame.child_facts
  have hodd := SheetMonoChild.sheetMono_odd_of_signed frame hP hsig
  have heven := SheetMonoChild.sheetMono_even_of_signed frame hP hsig
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, (J : ℤ) = (frame.child.den - 1) / 2 :=
    ⟨((frame.child.den - 1) / 2).toNat, Int.toNat_of_nonneg (by omega)⟩
  refine ⟨1, 0, by rw [hn1]; ring, ?_⟩
  exact CapRayGrades.ray_cap_NDgrades (F := G) (frame.child.num) (frame.child.den) 2 (by norm_num) (by norm_num)
    hn0 hnd hP.binary
    (fun w h1 h2 => hP.strips.1 w h1 h2)
    (fun w h1 h2 => hP.strips.2 w h1 h2)
    (fun u v hu hv h1 h2 => hodd u v hu hv h1 h2)
    (fun u v hu hv h1 h2 => heven u v hu hv h1 h2)
    (p := 1) (q := 0) (by rw [hn1]; ring) (by norm_num) J K
    (by rw [hn1]; omega) (by rw [hn1]; omega) hKr

end FLatticePaper.CapBaseN1
