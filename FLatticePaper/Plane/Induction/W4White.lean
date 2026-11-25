import FLatticePaper.Plane.Induction.W4Reduction
import FLatticePaper.Plane.Induction.RotatedCap
import FLatticePaper.Plane.Induction.SheetPieces
import FLatticePaper.Plane.Induction.W1OffCollar
import FLatticePaper.Plane.Induction.Binary
import FLatticePaper.Plane.Induction.DeckParentSquare
import FLatticePaper.Plane.Induction.W4Boundary

/-! # W4 (Q35): the white condition `hwhite` of the retained edge, from the strict interior and the A-contact

For a strictly interior white `c` of the word with `Ψ(c) = C(c) − A(c) ≥ 0`: the word's field is `min(A, C)` on the closed polygon, so
`F(c) = A(c)` and `F ≤ A` at both inputs of `c` (which lie in the closed polygon since `c` is strict). The white `lap F(c) = 0` then gives
`lap A(c) = Σ_inputs (A − F) ≥ 0`. Since `lap A(c) = lap G(Z(c − lv))` (the quarter turn and the even translation by `lv`) and the
packet of the conjugate has laplacians in `{−1, 0}`, `lap G(Z(c − lv)) = 0`. -/

namespace FLatticePaper.W4White

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1

/-- The Laplacian of a translate by an even site. -/
theorem laplacian_translate_even (F : Field) {s : Site} (hs : EvenSite s) (c : Site) :
    laplacian (fun z => F (z - s)) c = laplacian F (c - s) := by
  unfold laplacian
  rw [FLatticePaper.DeckParentSquare.incomingNeg_sub_even hs, FLatticePaper.DeckParentSquare.incomingPos_sub_even hs]

/-- The Laplacian of the quarter turn is the Laplacian of the field at `Z x = zTurn x`. -/
theorem laplacian_quarterTurn_zTurn (G : Field) (x : Site) :
    laplacian (quarterTurnField G) x = laplacian G (zTurn x) :=
  FLatticePaper.RotatedCap.laplacian_quarterTurnField G x

/-- `w1s` is even when `n + d` and `d − n` are even. -/
theorem w1s_even_of (n d : ℤ) (h1 : (n + d) % 2 = 0) (h2 : (d - n) % 2 = 0) (z : Site) :
    w1s n d z % 2 = 0 := by
  obtain ⟨m, hm⟩ : ∃ m, d + n = 2 * m := ⟨(d + n) / 2, by omega⟩
  obtain ⟨m', hm'⟩ : ∃ m', d - n = 2 * m' := ⟨(d - n) / 2, by omega⟩
  have e : w1s n d z = 2 * (m * z.1 + m' * z.2) := by
    unfold w1s
    rw [hm, hm']
    ring
  rw [e]
  omega

/-- `w1t` has the parity of `z₁ + z₂` when `n` and `d` are odd. -/
theorem w1t_parity_odd (n d : ℤ) (hn : n % 2 = 1) (hd : d % 2 = 1) (z : Site) :
    w1t n d z % 2 = (z.1 + z.2) % 2 := by
  obtain ⟨a, ha⟩ : ∃ a, n = 2 * a + 1 := ⟨n / 2, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, d = 2 * b + 1 := ⟨d / 2, by omega⟩
  have e : w1t n d z = 2 * (a * z.1 - b * z.2) + (z.1 - z.2) := by
    unfold w1t
    rw [ha, hb]
    ring
  rw [e]
  omega

/-- The left neighbour `(z₁ − 1, z₂)`: `w1t` drops by `n`, `w1s` by `d + n`. -/
theorem w1t_left' (n d : ℤ) (z : Site) : w1t n d (z.1 - 1, z.2) = w1t n d z - n := by
  unfold w1t; ring

theorem w1s_left' (n d : ℤ) (z : Site) : w1s n d (z.1 - 1, z.2) = w1s n d z - (d + n) := by
  unfold w1s; ring

/-- The right neighbour `(z₁ + 1, z₂)`. -/
theorem w1t_right' (n d : ℤ) (z : Site) : w1t n d (z.1 + 1, z.2) = w1t n d z + n := by
  unfold w1t; ring

theorem w1s_right' (n d : ℤ) (z : Site) : w1s n d (z.1 + 1, z.2) = w1s n d z + (d + n) := by
  unfold w1s; ring

/-- The lower neighbour `(z₁, z₂ − 1)`: `w1t` rises by `d`, `w1s` drops by `d − n`. -/
theorem w1t_down' (n d : ℤ) (z : Site) : w1t n d (z.1, z.2 - 1) = w1t n d z + d := by
  unfold w1t; ring

theorem w1s_down' (n d : ℤ) (z : Site) : w1s n d (z.1, z.2 - 1) = w1s n d z - (d - n) := by
  unfold w1s; ring

/-- The upper neighbour `(z₁, z₂ + 1)`. -/
theorem w1t_up' (n d : ℤ) (z : Site) : w1t n d (z.1, z.2 + 1) = w1t n d z - d := by
  unfold w1t; ring

theorem w1s_up' (n d : ℤ) (z : Site) : w1s n d (z.1, z.2 + 1) = w1s n d z + (d - n) := by
  unfold w1s; ring

/-- **The inputs of a strictly interior site lie in the closed polygon.** -/
theorem strict_neighbours_mem (frame : ChildFrame) {c : Site}
    (hSI : FLatticePaper.W1.StrictInterior frame.child.num frame.child.den c) :
    incomingNeg c ∈ frame.closedPolygon ∧ incomingPos c ∈ frame.closedPolygon := by
  obtain ⟨hn0, hnd, hd2, hd3, -⟩ := frame.child_facts
  obtain ⟨hnO, hdO⟩ := frame.child_odd
  have hTe := frame.T_even
  rw [frame_periodDenominator_eq frame] at hTe
  rw [closedPolygon_eq_closedRect frame]
  show closedRect frame.child.num frame.child.den (incomingNeg c) ∧
    closedRect frame.child.num frame.child.den (incomingPos c)
  by_cases hev : EvenSite c
  · obtain ⟨h1, h2, h3, h4⟩ := (FLatticePaper.W1OffCollar.strict_even _ _ c hev).1 hSI
    have hsev : w1s frame.child.num frame.child.den c % 2 = 0 :=
      w1s_even_of _ _ (by omega) (by omega) c
    have hin : incomingNeg c = (c.1 - 1, c.2) := by
      unfold incomingNeg
      rw [if_pos hev]
    have hip : incomingPos c = (c.1 + 1, c.2) := by
      unfold incomingPos
      rw [if_pos hev]
    have hnegE : ¬ EvenSite (c.1 - 1, c.2) := by
      unfold EvenSite at hev ⊢
      simp only
      omega
    have hposE : ¬ EvenSite (c.1 + 1, c.2) := by
      unfold EvenSite at hev ⊢
      simp only
      omega
    rw [hin, hip]
    constructor
    · unfold closedRect
      rw [if_neg hnegE, w1t_left', w1s_left']
      omega
    · unfold closedRect
      rw [if_neg hposE, w1t_right', w1s_right']
      omega
  · obtain ⟨h1, h2, h3, h4⟩ := (FLatticePaper.W1OffCollar.strict_odd _ _ c hev).1 hSI
    have ht : w1t frame.child.num frame.child.den c % 2 = 1 := by
      rw [w1t_parity_odd _ _ hnO hdO c]
      unfold EvenSite at hev
      omega
    have hsev : w1s frame.child.num frame.child.den c % 2 = 0 :=
      w1s_even_of _ _ (by omega) (by omega) c
    have hin : incomingNeg c = (c.1, c.2 - 1) := by
      unfold incomingNeg
      rw [if_neg hev]
    have hip : incomingPos c = (c.1, c.2 + 1) := by
      unfold incomingPos
      rw [if_neg hev]
    have hnegE : EvenSite (c.1, c.2 - 1) := by
      unfold EvenSite at hev ⊢
      simp only
      omega
    have hposE : EvenSite (c.1, c.2 + 1) := by
      unfold EvenSite at hev ⊢
      simp only
      omega
    rw [hin, hip]
    constructor
    · unfold closedRect
      rw [if_pos hnegE, w1t_down', w1s_down']
      omega
    · unfold closedRect
      rw [if_pos hposE, w1t_up', w1s_up']
      omega

/-- The even shift of the sheet offset: `sheetShift = (1 − W) U_q` is even. -/
theorem evenSite_sheetShift' {word : Word} : EvenSite (frameAt word).sheetShift := by
  have hpe := (frameAt word).valid.even_parity
  unfold Fraction.Even at hpe
  have hk : (frameAt word).parents.even.unmodifiedDeck.kernel =
      ((frameAt word).parents.even.den, (frameAt word).parents.even.num) := rfl
  unfold ChildFrame.sheetShift EvenSite
  rw [hk]
  simp only [Prod.smul_mk, smul_eq_mul]
  have e : (1 - (frameAt word).phaseW) * (frameAt word).parents.even.den +
      (1 - (frameAt word).phaseW) * (frameAt word).parents.even.num =
      (1 - (frameAt word).phaseW) * ((frameAt word).parents.even.num + (frameAt word).parents.even.den) := by ring
  rw [e, Int.mul_emod, hpe]
  simp

/-- **The white condition of the retained edge (`hwhite`), from the strict interior and the A-contact.** -/
theorem hwhite_of_strict {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    {c : Site} (hSI : FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c)
    (hc : c ∈ (frameAt word).closedPolygon)
    (hlap : laplacian (standardField word) c = 0)
    (hΨ : 0 ≤ FLatticePaper.W1Step.sheetPsi word c) :
    laplacian (standardField (conjWord word)) (zTurn (c - (frameAt word).sheetShift)) = 0 := by
  have hse := evenSite_sheetShift' (word := word)
  set s := (frameAt word).sheetShift with hs
  set Fq := quarterTurnField (standardField (conjWord word)) with hFq
  have hmin : ∀ z ∈ (frameAt word).closedPolygon,
      standardField word z = min ((frameAt word).sheetA Fq z) ((frameAt word).sheetC Fq z) := by
    intro z hz
    rw [standardField_eq_sheetMin_of_strong h hSE hz]
    rfl
  have hpsi : FLatticePaper.W1Step.sheetPsi word c = (frameAt word).sheetC Fq c - (frameAt word).sheetA Fq c := rfl
  have hFc : standardField word c = Fq (c - s) := by
    rw [hmin c hc, min_eq_left (by rw [hpsi] at hΨ; linarith)]
    rfl
  obtain ⟨hnin, hpin⟩ := strict_neighbours_mem (frameAt word) hSI
  have hle : ∀ z ∈ (frameAt word).closedPolygon, standardField word z ≤ Fq (z - s) := by
    intro z hz
    rw [hmin z hz]
    exact min_le_left _ _
  have hAlap : laplacian (fun z => Fq (z - s)) c = laplacian (standardField (conjWord word)) (zTurn (c - s)) := by
    rw [laplacian_translate_even Fq hse c, laplacian_quarterTurn_zTurn]
  have hnonneg : 0 ≤ laplacian (fun z => Fq (z - s)) c := by
    have hlap' := hlap
    unfold laplacian at hlap' ⊢
    have h1 := hle _ hnin
    have h2 := hle _ hpin
    simp only at hlap' ⊢
    linarith
  have hbin := hSE.packet.binary (zTurn (c - s))
  omega

end FLatticePaper.W4White
