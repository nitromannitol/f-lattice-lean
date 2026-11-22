import FLatticePaper.Plane.Induction.Packet
import FLatticePaper.Plane.Induction.Strips
import FLatticePaper.Plane.Induction.Reflection
import FLatticePaper.Plane.Induction.Binary
import FLatticePaper.Plane.Induction.TwosField
import FLatticePaper.Construction.LadderRotation

/-! # The packet of the twos words `2^(k+1)` (task 39)

* `ChildFrame.packet_of_stripInputs`: a field with the coherent periods, strip inputs and binarity on the closed polygon
  is a packet. This is the assembly of `ChildFrame.packet_of_sheets` without the sheet data.
* The frame of `2^(k+1)` has child `(2k+3)/(2k+5)` and coherent constants `(0, ladderEvenConstantV (2k+4))`, the
  constants of the near-one doubled ladder with `d = 2k+4`.
* Hence the packet at `2^(k+1)` reduces to the periods of its standard field and to the strip inputs and the polygon
  binarity of that field. -/

namespace FLatticePaper.Induction
open Farey Construction

/-- The packet from the coherent periods, the strip inputs and the binarity on the closed polygon. -/
theorem ChildFrame.packet_of_stripInputs (frame : ChildFrame) {F : Field}
    (hper : HasGeneratorPeriods frame.child F frame.coherentConstantU frame.coherentConstantV)
    (hS : frame.StripInputs F)
    (hbin : ∀ z ∈ frame.closedPolygon, laplacian F z = -1 ∨ laplacian F z = 0) : frame.Packet F := by
  have hagree : ∀ y ∈ frame.closedPolygon, F y = F y := fun _ _ => rfl
  have hstrips := frame.hasStrips_of_stripInputs hS hagree hper
  have hreflF := frame.reflection_of_heightInputs hS.heightInputs hagree hper
  have hbinF := frame.binary_of_strips hper hagree hbin hstrips hreflF
  exact ⟨hper, hstrips, hreflF, hbinF⟩

/-- The child of `2^(k+1)` is `(2k+3)/(2k+5)`. -/
theorem twos_child_eq (k : ℕ) :
    (frameAt (List.replicate (k + 1) Digit.two)).child = ⟨2 * (k : ℤ) + 3, 2 * (k : ℤ) + 5⟩ := by
  rw [child_replicate_two_succ, Fraction.rotate_of_odd (by show (1 + (2 * (k : ℤ) + 4)) % 2 = 1; omega)]
  have h1 : 2 * (k : ℤ) + 4 - 1 = 2 * (k : ℤ) + 3 := by ring
  have h2 : 2 * (k : ℤ) + 4 + 1 = 2 * (k : ℤ) + 5 := by ring
  show (⟨2 * (k : ℤ) + 4 - 1, 2 * (k : ℤ) + 4 + 1⟩ : Fraction) = _
  rw [h1, h2]

/-- The coherent constants of the frame of `2^(k+1)`: `c_U = 0` and `c_V` the constant of the near-one doubled ladder
with `d = 2k+4`. -/
theorem twos_coherentConstants (k : ℕ) :
    (frameAt (List.replicate (k + 1) Digit.two)).coherentConstantU = 0 ∧
      (frameAt (List.replicate (k + 1) Digit.two)).coherentConstantV = ladderEvenConstantV (2 * (k : ℤ) + 4) := by
  refine ⟨(frameAt (List.replicate (k + 1) Digit.two)).coherentConstantU_eq_zero, ?_⟩
  have h := (frameAt (List.replicate (k + 1) Digit.two)).coherentConstantV_eq
  rw [twos_child_eq k] at h
  unfold Fraction.periodDenominator at h
  dsimp only at h
  rw [ladderEvenConstantV_eq]
  linarith

/-- The packet at `2^(k+1)`, given the periods of its standard field with the constants of the near-one ladder, and
the strip inputs and the polygon binarity of that field. -/
theorem twos_packet_of_stripInputs (k : ℕ) {F : Field}
    (hper : HasGeneratorPeriods (frameAt (List.replicate (k + 1) Digit.two)).child F 0
      (ladderEvenConstantV (2 * (k : ℤ) + 4)))
    (hS : (frameAt (List.replicate (k + 1) Digit.two)).StripInputs F)
    (hbin : ∀ z ∈ (frameAt (List.replicate (k + 1) Digit.two)).closedPolygon, laplacian F z = -1 ∨
      laplacian F z = 0) :
    (frameAt (List.replicate (k + 1) Digit.two)).Packet F := by
  refine (frameAt (List.replicate (k + 1) Digit.two)).packet_of_stripInputs ?_ hS hbin
  rw [(twos_coherentConstants k).1, (twos_coherentConstants k).2]
  exact hper

/-- A translate of a field by a site `w` shifts the transverse constant by the transverse grade of `w`. -/
theorem hasGeneratorPeriods_translate_shift (fraction : Fraction) {N : Field} {c : ℤ}
    (hN : HasGeneratorPeriods fraction N 0 c) (w : Site) :
    HasGeneratorPeriods fraction (fun z => N (z - w)) 0 (c + fraction.transverseGrade w) := by
  refine ⟨fun z => ?_, fun z => ?_⟩
  · show N (z + fraction.modifiedDeck.kernel - w) = N (z - w) + 0
    rw [add_sub_right_comm, hN.1 (z - w)]
  · have h := hN.2 (z - w)
    show N (z + fraction.modifiedDeck.transverse - w) =
      N (z - w) - fraction.transverseGrade z + (c + fraction.transverseGrade w)
    rw [add_sub_right_comm, h, fraction.transverseGrade_sub z w]
    ring

/-- The transverse constant of a field with the periods of a fraction is determined by the field. -/
theorem constantV_eq_of_periods {fr : Fraction} {F : Field} {c₁ c₂ : ℤ}
    (h₁ : HasGeneratorPeriods fr F 0 c₁) (h₂ : HasGeneratorPeriods fr F 0 c₂) : c₁ = c₂ := by
  linarith [h₁.2 0, h₂.2 0]

/-- The near-one doubled ladder with the constants of `d = 2k+4`, on the child of `2^(k+1)`. -/
theorem twos_nearOne_periods (k : ℕ) :
    ∃ N : Field, HasGeneratorPeriods (frameAt (List.replicate (k + 1) Digit.two)).child N 0
      (ladderEvenConstantV (2 * (k : ℤ) + 4)) := by
  have hvalid : BaseMask.ladderEven.Valid (2 * (k : ℤ) + 4) := ⟨by omega, by omega⟩
  obtain ⟨N, -, hper, -⟩ := ladderEven_exists_extension hvalid
  exact ⟨N, by rw [child_replicate_two_succ]; exact hper⟩

/-- No translate `N(· - w)` of the near-one field has the coherent periods of the frame of `2^(k+1)` when the grade
`transverseGrade w` of the shift is nonzero. Hence a one-site translate cannot be the standard field of `2^(k+1)`. -/
theorem twos_translate_not_periods (k : ℕ) {N : Field}
    (hN : HasGeneratorPeriods (frameAt (List.replicate (k + 1) Digit.two)).child N 0
      (ladderEvenConstantV (2 * (k : ℤ) + 4)))
    (w : Site) (hw : (frameAt (List.replicate (k + 1) Digit.two)).child.transverseGrade w ≠ 0) :
    ¬ HasGeneratorPeriods (frameAt (List.replicate (k + 1) Digit.two)).child (fun z => N (z - w)) 0
      (frameAt (List.replicate (k + 1) Digit.two)).coherentConstantV := by
  intro hF
  have hshift := hasGeneratorPeriods_translate_shift _ hN w
  have hc := constantV_eq_of_periods hshift hF
  rw [(twos_coherentConstants k).2] at hc
  exact hw (by linarith)

/-- The one-site translate `(0,1)` of the near-one field is not the standard field of `2^(k+1)`: the packet of
`2^(k+1)` has the coherent periods, and `transverseGrade (0,1) = 2k+5 ≠ 0`. -/
theorem twos_standardField_ne_translate (k : ℕ) {N : Field}
    (hN : HasGeneratorPeriods (frameAt (List.replicate (k + 1) Digit.two)).child N 0
      (ladderEvenConstantV (2 * (k : ℤ) + 4)))
    (hpk : (frameAt (List.replicate (k + 1) Digit.two)).Packet (standardField (List.replicate (k + 1) Digit.two))) :
    standardField (List.replicate (k + 1) Digit.two) ≠ fun z => N (z - (0, 1)) := by
  intro hid
  apply twos_translate_not_periods k hN (0, 1)
  · rw [twos_child_eq k]
    simp [Fraction.transverseGrade]
    omega
  · rw [← hid, (twos_coherentConstants k).2]
    have hp := hpk.periods
    rw [(twos_coherentConstants k).1, (twos_coherentConstants k).2] at hp
    exact hp

end FLatticePaper.Induction
