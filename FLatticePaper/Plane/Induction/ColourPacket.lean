import FLatticePaper.Plane.Induction.StrongInduction
import FLatticePaper.Plane.Induction.SheetPieces
import FLatticePaper.Plane.Induction.StripColours
import FLatticePaper.Plane.Induction.W1Constructor
import FLatticePaper.Plane.Induction.W1OffCollar
import FLatticePaper.Plane.Induction.W1MSheet
import FLatticePaper.Plane.Induction.CollarOneOne
import FLatticePaper.Plane.Induction.Exceptions

/-! # The colours of the sheet minimum from the standard field of the word

The periods of `MW word` on the whole plane are not available (the sheet minimum is a chart on the closed polygon with an
affine correction elsewhere). The colour facts used at the top square are therefore stated for the standard field of the
word, whose strips and periods come from its packet (`packet_of_openInputs_step`), and transferred to `MW word` at the
stencils of the three points, which lie in the closed polygon.

The three points: `(d - 1, n)` (the bottom-right meeting), `vLast + (1,0) = (n - d + 2, n + d - 1)`, and `R - (1,1) = (n, 2n + d - 2)`. -/

namespace FLatticePaper.ColourPacket

open FLatticePaper FLatticePaper.W1 FLatticePaper.W1OffCollar FLatticePaper.W1Phase FLatticePaper.Induction
  FLatticePaper.W1MSheet FLatticePaper.StripColours FLatticePaper.Farey

/-- The standard field of the word has its packet (strips and periods) from the conjugate packet and the open inputs. -/
theorem std_packet {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word)) :
    (frameAt word).Packet (standardField word) :=
  packet_of_openInputs_step h hSE.packet (openInputs_of_strong h hSE)

theorem mem_closed_iff (word : Word) (x : Site) :
    x ∈ (frameAt word).closedPolygon ↔ closedRect (frameAt word).child.num (frameAt word).child.den x := by
  rw [closedPolygon_eq_closedRect]
  rfl

/-- The Laplacian of the sheet minimum at `x` is the Laplacian of the standard field, when its stencil lies in the polygon. -/
theorem lap_MW_eq_std {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    {x : Site} (h0 : x ∈ (frameAt word).closedPolygon) (h1 : incomingNeg x ∈ (frameAt word).closedPolygon)
    (h2 : incomingPos x ∈ (frameAt word).closedPolygon) :
    laplacian (MW word) x = laplacian (standardField word) x := by
  have e : ∀ y ∈ (frameAt word).closedPolygon, MW word y = standardField word y := fun y hy =>
    (standardField_eq_sheetMin_of_strong h hSE hy).symm
  unfold laplacian
  rw [e _ h1, e _ h2, e _ h0]

theorem incomingNeg_of_odd {x : Site} (h : ¬ EvenSite x) : incomingNeg x = (x.1, x.2 - 1) := by
  unfold incomingNeg; rw [if_neg h]

theorem incomingPos_of_odd {x : Site} (h : ¬ EvenSite x) : incomingPos x = (x.1, x.2 + 1) := by
  unfold incomingPos; rw [if_neg h]

theorem incomingNeg_of_even {x : Site} (h : EvenSite x) : incomingNeg x = (x.1 - 1, x.2) := by
  unfold incomingNeg; rw [if_pos h]

theorem incomingPos_of_even {x : Site} (h : EvenSite x) : incomingPos x = (x.1 + 1, x.2) := by
  unfold incomingPos; rw [if_pos h]

/-! ## The stencil facts: the closed rectangle at the three points and their incoming neighbours -/

section Stencil

variable {n d : ℤ}

/-- `(d-1, n)`: odd, with grades `(-n, T - d - n)`. -/
theorem closed_dn1 (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d)
    (hT : 4 * (d + n) - 3 ≤ w1T n d) : closedRect n d (d - 1, n) := by
  have e1 : w1t n d (d - 1, n) = -n := by unfold w1t; ring
  have e2 : w1s n d (d - 1, n) = w1T n d - d - n := by unfold w1s w1T; ring
  have hp : ¬ EvenSite (d - 1, n) := by unfold EvenSite; simp only; omega
  rw [closedRect_iff]
  right
  refine ⟨hp, ?_⟩
  rw [e1, e2]; omega

theorem closed_dn_m (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d)
    (hT : 4 * (d + n) - 3 ≤ w1T n d) : closedRect n d (d - 1, n - 1) := by
  have e1 : w1t n d (d - 1, n - 1) = d - n := by unfold w1t; ring
  have e2 : w1s n d (d - 1, n - 1) = w1T n d - 2 * d := by unfold w1s w1T; ring
  have hp : EvenSite (d - 1, n - 1) := by unfold EvenSite; simp only; omega
  rw [closedRect_iff]
  left
  refine ⟨hp, ?_⟩
  rw [e1, e2]; omega

theorem closed_dn_p (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d)
    (hT : 4 * (d + n) - 3 ≤ w1T n d) : closedRect n d (d - 1, n + 1) := by
  have e1 : w1t n d (d - 1, n + 1) = -n - d := by unfold w1t; ring
  have e2 : w1s n d (d - 1, n + 1) = w1T n d - 2 * n := by unfold w1s w1T; ring
  have hp : EvenSite (d - 1, n + 1) := by unfold EvenSite; simp only; omega
  rw [closedRect_iff]
  left
  refine ⟨hp, ?_⟩
  rw [e1, e2]; omega

/-- `vLast + (1,0) = (n - d + 2, n + d - 1)`: odd, grades `(-T + 2n + d, 3n + d)`. -/
theorem closed_v0 (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d)
    (hT : 4 * (d + n) - 3 ≤ w1T n d) : closedRect n d (n - d + 2, n + d - 1) := by
  have e1 : w1t n d (n - d + 2, n + d - 1) = -w1T n d + 2 * n + d := by unfold w1t w1T; ring
  have e2 : w1s n d (n - d + 2, n + d - 1) = 3 * n + d := by unfold w1s; ring
  have hp : ¬ EvenSite (n - d + 2, n + d - 1) := by unfold EvenSite; simp only; omega
  rw [closedRect_iff]
  right
  refine ⟨hp, ?_⟩
  rw [e1, e2]; omega

theorem closed_v_m (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d)
    (hT : 4 * (d + n) - 3 ≤ w1T n d) : closedRect n d (n - d + 2, n + d - 2) := by
  have e1 : w1t n d (n - d + 2, n + d - 2) = -w1T n d + 2 * n + 2 * d := by unfold w1t w1T; ring
  have e2 : w1s n d (n - d + 2, n + d - 2) = 4 * n := by unfold w1s; ring
  have hp : EvenSite (n - d + 2, n + d - 2) := by unfold EvenSite; simp only; omega
  rw [closedRect_iff]
  left
  refine ⟨hp, ?_⟩
  rw [e1, e2]; omega

theorem closed_v_p (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d)
    (hT : 4 * (d + n) - 3 ≤ w1T n d) : closedRect n d (n - d + 2, n + d) := by
  have e1 : w1t n d (n - d + 2, n + d) = -w1T n d + 2 * n := by unfold w1t w1T; ring
  have e2 : w1s n d (n - d + 2, n + d) = 2 * d + 2 * n := by unfold w1s; ring
  have hp : EvenSite (n - d + 2, n + d) := by unfold EvenSite; simp only; omega
  rw [closedRect_iff]
  left
  refine ⟨hp, ?_⟩
  rw [e1, e2]; omega

/-- `R - (1,1) = (n, 2n + d - 2)`: even, grades `(-T + 2d, T - 2d)`. -/
theorem closed_r0 (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d)
    (hT : 4 * (d + n) - 3 ≤ w1T n d) : closedRect n d (n, 2 * n + d - 2) := by
  have e1 : w1t n d (n, 2 * n + d - 2) = -w1T n d + 2 * d := by unfold w1t w1T; ring
  have e2 : w1s n d (n, 2 * n + d - 2) = w1T n d - 2 * d + 2 * n := by unfold w1s w1T; ring
  have hp : EvenSite (n, 2 * n + d - 2) := by unfold EvenSite; simp only; omega
  rw [closedRect_iff]
  left
  refine ⟨hp, ?_⟩
  rw [e1, e2]; omega

theorem closed_rm (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d)
    (hT : 4 * (d + n) - 3 ≤ w1T n d) : closedRect n d (n - 1, 2 * n + d - 2) := by
  have e1 : w1t n d (n - 1, 2 * n + d - 2) = -w1T n d - n + 2 * d := by unfold w1t w1T; ring
  have e2 : w1s n d (n - 1, 2 * n + d - 2) = w1T n d - 3 * d + n := by unfold w1s w1T; ring
  have hp : ¬ EvenSite (n - 1, 2 * n + d - 2) := by unfold EvenSite; simp only; omega
  rw [closedRect_iff]
  right
  refine ⟨hp, ?_⟩
  rw [e1, e2]; omega

theorem closed_rp (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d)
    (hT : 4 * (d + n) - 3 ≤ w1T n d) : closedRect n d (n + 1, 2 * n + d - 2) := by
  have e1 : w1t n d (n + 1, 2 * n + d - 2) = -w1T n d + n + 2 * d := by unfold w1t w1T; ring
  have e2 : w1s n d (n + 1, 2 * n + d - 2) = w1T n d - d + 3 * n := by unfold w1s w1T; ring
  have hp : ¬ EvenSite (n + 1, 2 * n + d - 2) := by unfold EvenSite; simp only; omega
  rw [closedRect_iff]
  right
  refine ⟨hp, ?_⟩
  rw [e1, e2]; omega

end Stencil

/-! ## The three colours of the sheet minimum -/

/-- `laplacian (MW word) (d - 1, n) = -1`. -/
theorem lap_MW_dn1 {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word)) :
    laplacian (MW word) ((frameAt word).child.den - 1, (frameAt word).child.num) = -1 := by
  obtain ⟨hnO, hdO⟩ := (frameAt word).child_odd
  obtain ⟨hn0, hnd1, hd2, -, -⟩ := (frameAt word).child_facts
  have hn1 : 1 ≤ (frameAt word).child.num := by omega
  have hnd : (frameAt word).child.num + 2 ≤ (frameAt word).child.den := by omega
  have hT := FLatticePaper.Exceptions.period_ge4 hn1 hnd
  have hp : ¬ EvenSite ((frameAt word).child.den - 1, (frameAt word).child.num) := by
    unfold EvenSite; simp only; omega
  have h0 : ((frameAt word).child.den - 1, (frameAt word).child.num) ∈ (frameAt word).closedPolygon :=
    (mem_closed_iff word _).mpr (closed_dn1 hnO hdO hn1 hnd hT)
  have h1 : incomingNeg ((frameAt word).child.den - 1, (frameAt word).child.num) ∈
      (frameAt word).closedPolygon := by
    rw [incomingNeg_of_odd hp, mem_closed_iff]; exact closed_dn_m hnO hdO hn1 hnd hT
  have h2 : incomingPos ((frameAt word).child.den - 1, (frameAt word).child.num) ∈
      (frameAt word).closedPolygon := by
    rw [incomingPos_of_odd hp, mem_closed_iff]; exact closed_dn_p hnO hdO hn1 hnd hT
  rw [lap_MW_eq_std h hSE h0 h1 h2]
  exact lap_den_sub_one (frameAt word) (std_packet h hSE).strips (std_packet h hSE).periods

/-- `laplacian (MW word) (vLast.1 + 1, vLast.2) = -1`, the black point `(n - d + 2, n + d - 1)`. -/
theorem lap_MW_vLast {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word)) :
    laplacian (MW word) ((frameAt word).vLast.1 + 1, (frameAt word).vLast.2) = -1 := by
  obtain ⟨hnO, hdO⟩ := (frameAt word).child_odd
  obtain ⟨hn0, hnd1, hd2, -, -⟩ := (frameAt word).child_facts
  have hn1 : 1 ≤ (frameAt word).child.num := by omega
  have hnd : (frameAt word).child.num + 2 ≤ (frameAt word).child.den := by omega
  have hT := FLatticePaper.Exceptions.period_ge4 hn1 hnd
  have hP : ((frameAt word).vLast.1 + 1, (frameAt word).vLast.2) =
      ((frameAt word).child.num - (frameAt word).child.den + 2,
        (frameAt word).child.num + (frameAt word).child.den - 1) :=
    Prod.ext (by simp only [ChildFrame.vLast]; ring) (by simp only [ChildFrame.vLast])
  rw [hP]
  have hp : ¬ EvenSite ((frameAt word).child.num - (frameAt word).child.den + 2,
      (frameAt word).child.num + (frameAt word).child.den - 1) := by
    unfold EvenSite; simp only; omega
  have h0 : ((frameAt word).child.num - (frameAt word).child.den + 2,
      (frameAt word).child.num + (frameAt word).child.den - 1) ∈ (frameAt word).closedPolygon :=
    (mem_closed_iff word _).mpr (closed_v0 hnO hdO hn1 hnd hT)
  have h1 : incomingNeg ((frameAt word).child.num - (frameAt word).child.den + 2,
      (frameAt word).child.num + (frameAt word).child.den - 1) ∈ (frameAt word).closedPolygon := by
    have e : (frameAt word).child.num + (frameAt word).child.den - 1 - 1 =
        (frameAt word).child.num + (frameAt word).child.den - 2 := by ring
    rw [incomingNeg_of_odd hp, mem_closed_iff, e]; exact closed_v_m hnO hdO hn1 hnd hT
  have h2 : incomingPos ((frameAt word).child.num - (frameAt word).child.den + 2,
      (frameAt word).child.num + (frameAt word).child.den - 1) ∈ (frameAt word).closedPolygon := by
    have e : (frameAt word).child.num + (frameAt word).child.den - 1 + 1 =
        (frameAt word).child.num + (frameAt word).child.den := by ring
    rw [incomingPos_of_odd hp, mem_closed_iff, e]; exact closed_v_p hnO hdO hn1 hnd hT
  rw [lap_MW_eq_std h hSE h0 h1 h2]
  have hl := lap_vLast_east (frameAt word) (std_packet h hSE).strips (std_packet h hSE).periods
  rw [hP] at hl
  exact hl

/-- `laplacian (MW word) (num, 2 num + den - 2) = -1`, the black point `R - (1,1)`. -/
theorem lap_MW_R {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word)) :
    laplacian (MW word) ((frameAt word).child.num, 2 * (frameAt word).child.num + (frameAt word).child.den - 2) = -1 := by
  obtain ⟨hnO, hdO⟩ := (frameAt word).child_odd
  obtain ⟨hn0, hnd1, hd2, -, -⟩ := (frameAt word).child_facts
  have hn1 : 1 ≤ (frameAt word).child.num := by omega
  have hnd : (frameAt word).child.num + 2 ≤ (frameAt word).child.den := by omega
  have hT := FLatticePaper.Exceptions.period_ge4 hn1 hnd
  have hp : EvenSite ((frameAt word).child.num, 2 * (frameAt word).child.num + (frameAt word).child.den - 2) := by
    unfold EvenSite; simp only; omega
  have h0 : ((frameAt word).child.num, 2 * (frameAt word).child.num + (frameAt word).child.den - 2) ∈
      (frameAt word).closedPolygon :=
    (mem_closed_iff word _).mpr (closed_r0 hnO hdO hn1 hnd hT)
  have h1 : incomingNeg ((frameAt word).child.num, 2 * (frameAt word).child.num + (frameAt word).child.den - 2) ∈
      (frameAt word).closedPolygon := by
    rw [incomingNeg_of_even hp, mem_closed_iff]; exact closed_rm hnO hdO hn1 hnd hT
  have h2 : incomingPos ((frameAt word).child.num, 2 * (frameAt word).child.num + (frameAt word).child.den - 2) ∈
      (frameAt word).closedPolygon := by
    rw [incomingPos_of_even hp, mem_closed_iff]; exact closed_rp hnO hdO hn1 hnd hT
  rw [lap_MW_eq_std h hSE h0 h1 h2]
  exact lap_R_sub_one_one (frameAt word) (std_packet h hSE).strips (std_packet h hSE).periods

end FLatticePaper.ColourPacket
