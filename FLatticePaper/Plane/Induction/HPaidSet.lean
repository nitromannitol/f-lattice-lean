import FLatticePaper.Plane.Induction.PairTranslate
import FLatticePaper.Plane.Induction.FirstExit

/-! # hpaid in the matched-pairing form (set form)

For the first exit `u` of a strict site `z` (`FirstExit.first_exit_free`), the translate `u + kU + lV` with pair `(c₀, 0)`
is own-deck free: it lies in `freeH + ℤU` or in `freeV + ℤV`. The deck vectors are `U = (d, n)` and `V = (n − d, n + d)`.
The named inputs are the drifts of `P` and `J` and the values `J = 0` on the free H sites and `P = c₀` on the free V sites. -/

namespace FLatticePaper.HPaidSet

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1

/-- The coordinate form of the span translate of a site. -/
theorem sub_smul_pair (u : Site) (k l d n : ℤ) :
    u - k • ((d, n) : Site) - l • ((n - d, n + d) : Site) =
      (u.1 - k * d - l * (n - d), u.2 - k * n - l * (n + d)) := by
  ext <;> simp

/-- **hpaid (set form).** The first exit of a strict site, translated to pair `(c₀, 0)`, is own-deck free. -/
theorem first_exit_pair (frame : ChildFrame) (P J : Site → ℤ) (η c0 : ℤ) (hη : η * η = 1)
    (hPU : ∀ z : Site, P (z + ((frame.child.den, frame.child.num) : Site)) = P z - 1)
    (hPV : ∀ z : Site, P (z + ((frame.child.num - frame.child.den, frame.child.num + frame.child.den) : Site)) = P z)
    (hJU : ∀ z : Site, J (z + ((frame.child.den, frame.child.num) : Site)) = J z)
    (hJV : ∀ z : Site, J (z + ((frame.child.num - frame.child.den, frame.child.num + frame.child.den) : Site)) =
      J z + η)
    (hJH : ∀ v ∈ frame.freeH, J v = 0) (hPF : ∀ v ∈ frame.freeV, P v = c0)
    {z u : Site} (hz : StrictInterior frame.child.num frame.child.den z) (hE : Edge u z)
    (hnot : ¬ StrictInterior frame.child.num frame.child.den u) :
    ∃ k l : ℤ, P (u + k • ((frame.child.den, frame.child.num) : Site) + l • ((frame.child.num - frame.child.den,
          frame.child.num + frame.child.den) : Site)) = c0 ∧
      J (u + k • ((frame.child.den, frame.child.num) : Site) + l • ((frame.child.num - frame.child.den,
          frame.child.num + frame.child.den) : Site)) = 0 ∧
      ((∃ m : ℤ, u + k • ((frame.child.den, frame.child.num) : Site) + l • ((frame.child.num - frame.child.den,
          frame.child.num + frame.child.den) : Site) - m • ((frame.child.den, frame.child.num) : Site) ∈ frame.freeH) ∨
       (∃ m : ℤ, u + k • ((frame.child.den, frame.child.num) : Site) + l • ((frame.child.num - frame.child.den,
          frame.child.num + frame.child.den) : Site) - m • ((frame.child.num - frame.child.den,
          frame.child.num + frame.child.den) : Site) ∈ frame.freeV)) := by
  have hfree := FirstExit.first_exit_free frame hz hE hnot
  obtain ⟨k', l', hv⟩ := hfree
  have hFree : ∃ k' l' : ℤ, (fun v : Site => v ∈ frame.freeH) (u - k' • ((frame.child.den, frame.child.num) : Site) -
      l' • ((frame.child.num - frame.child.den, frame.child.num + frame.child.den) : Site)) ∨
      (fun v : Site => v ∈ frame.freeV) (u - k' • ((frame.child.den, frame.child.num) : Site) -
        l' • ((frame.child.num - frame.child.den, frame.child.num + frame.child.den) : Site)) := by
    refine ⟨k', l', ?_⟩
    rw [sub_smul_pair]
    exact hv
  exact PairTranslate.pair_own P J ((frame.child.den, frame.child.num) : Site)
    ((frame.child.num - frame.child.den, frame.child.num + frame.child.den) : Site) η c0 hη hPU hPV hJU hJV
    (fun v : Site => v ∈ frame.freeH) (fun v : Site => v ∈ frame.freeV)
    (fun v hv => hJH v hv) (fun v hv => hPF v hv) u hFree

end FLatticePaper.HPaidSet
