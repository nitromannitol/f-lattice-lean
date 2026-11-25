import FLatticePaper.Plane.Induction.EndpointDeck

/-! Task w3, step 2(c): the labelled cut is symmetric under `z ↦ (1,−1) + V' − z`, and the raw slip reflects.

* `refl_cut`: `(1,−1) + V' − vAt j = vAt (L' − 1 − j)`. The reflected point has the same parity, its `s` is `2n' − s`,
  which exchanges each parity window with itself, and it has ordinate `L' − 1 − j`; so `row_unique` identifies it.
* `Dq_reflect`: `D_+(z) = D_−((1,−1) − z)` (the field is symmetric about `reflectionI = (1,−1)`).
* With the period rule, `D_+(V_j) = D_−(V_{L'−1−j}) + 2`. -/

namespace FLatticePaper.CutReflect

open Farey FLatticePaper FLatticePaper.Induction

/-- **The cut reflection.** `(1,−1) + V' − vAt j = vAt (L' − 1 − j)`. -/
theorem refl_cut (C : ChildFrame) (base : ℤ → Site)
    (hbase : ∀ r : ℤ, 0 ≤ r → r < FreeEnum.period C → base r ∈ C.freeV ∧ (base r).2 = r) (j : ℤ) :
    ((1 : ℤ), (-1 : ℤ)) + Vdeck C - FreeEnum.vAt C base j = FreeEnum.vAt C base (FreeEnum.period C - 1 - j) := by
  obtain ⟨hn0, hnd, hdn, hd3, -⟩ := C.child_facts
  have hwj := VWindow.vAt_window C base hbase j
  have hwr := VWindow.vAt_window C base hbase (FreeEnum.period C - 1 - j)
  have hord := FreeEnum.vAt_snd C base (fun r h0 h1 => (hbase r h0 h1).2) j
  have hordr := FreeEnum.vAt_snd C base (fun r h0 h1 => (hbase r h0 h1).2) (FreeEnum.period C - 1 - j)
  -- the reflected site
  have hsum : C.sGrade (((1 : ℤ), (-1 : ℤ)) + Vdeck C - FreeEnum.vAt C base j) =
      2 * C.child.num - C.sGrade (FreeEnum.vAt C base j) := by
    unfold ChildFrame.sGrade Vdeck
    simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add]
    ring
  have hpar : EvenSite (((1 : ℤ), (-1 : ℤ)) + Vdeck C - FreeEnum.vAt C base j) ↔
      EvenSite (FreeEnum.vAt C base j) := by
    unfold EvenSite Vdeck
    simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add]
    constructor <;> intro h <;> omega
  have hw : (EvenSite (((1 : ℤ), (-1 : ℤ)) + Vdeck C - FreeEnum.vAt C base j) →
        0 ≤ C.sGrade (((1 : ℤ), (-1 : ℤ)) + Vdeck C - FreeEnum.vAt C base j) ∧
        C.sGrade (((1 : ℤ), (-1 : ℤ)) + Vdeck C - FreeEnum.vAt C base j) ≤ 2 * C.child.num) ∧
      (¬ EvenSite (((1 : ℤ), (-1 : ℤ)) + Vdeck C - FreeEnum.vAt C base j) →
        2 - C.child.den + C.child.num ≤ C.sGrade (((1 : ℤ), (-1 : ℤ)) + Vdeck C - FreeEnum.vAt C base j) ∧
        C.sGrade (((1 : ℤ), (-1 : ℤ)) + Vdeck C - FreeEnum.vAt C base j) ≤ C.child.den + C.child.num - 2) := by
    rw [hsum]
    constructor
    · intro he
      have he' := hpar.mp he
      have h1 := hwj.1 he'
      constructor <;> omega
    · intro hn
      have hn' : ¬ EvenSite (FreeEnum.vAt C base j) := fun h => hn (hpar.mpr h)
      have h1 := hwj.2 hn'
      constructor <;> omega
  have hord2 : (((1 : ℤ), (-1 : ℤ)) + Vdeck C - FreeEnum.vAt C base j).2 = FreeEnum.period C - 1 - j := by
    simp only [Prod.snd_sub, Prod.snd_add, hord, Vdeck, FreeEnum.period]
    ring
  exact VWindow.row_unique C (hord2.trans hordr.symm) hw hwr

/-- The raw slip `D_+` is the raw slip `D_−` at the reflected site (`G` symmetric about `(1,−1)`). -/
theorem Dq_reflect (C : ChildFrame) {G : Field} (hI : ∀ z, G (reflectionI - z) = G z) (z : Site) :
    EndpointDeck.Dq C G 1 z = EndpointDeck.Dq C G (-1) (reflectionI - z) := by
  unfold EndpointDeck.Dq
  have e : reflectionI - z + (-1 : ℤ) • C.shortShift = reflectionI - (z + (1 : ℤ) • C.shortShift) := by
    unfold reflectionI
    ext <;> simp <;> ring
  rw [e, hI z, hI (z + (1 : ℤ) • C.shortShift)]

end FLatticePaper.CutReflect
