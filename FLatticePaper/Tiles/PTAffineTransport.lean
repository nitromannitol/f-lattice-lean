import FLatticePaper.Tiles.FirstSentenceSurgical
import FLatticePaper.Tiles.SurgicalAffineChain
import FLatticePaper.Tiles.RespectsLetters

/-! The affine analogue of `PTFamily.translate` (FirstSentenceSurgical): adding a common affine function `x ↦ a·x + c` to every
odometer of a family.

The affine factors are shifted by `a` and the constants by `c`, so the `k`-th odometer becomes `o_k(x) + a·x + c`. The slope of
a family's tile is the average gradient over its unit squares, and adding `a·x + c` adds exactly `a` to every square's gradient
(`slopeOf_translate_affine` with the zero translation), whatever the tile. Hence slope differences between consecutive tiles
are unchanged, and so is the boundary clause, which compares values after the shared affine factor `a_k`. Therefore `Respects`
is invariant under adding a common affine function. -/

namespace FLatticePaper.Tiles

/-- Adding the affine function `x ↦ a·x + c` to every odometer of a family. -/
def PTFamily.affineAdd (F : PTFamily) (a : GInt) (c : ℤ) : PTFamily :=
  { ts := F.ts, a := fun k => F.a k + a, b := fun k => F.b k + c }

theorem PTFamily.affineAdd_n (F : PTFamily) (a : GInt) (c : ℤ) : (F.affineAdd a c).n = F.n := by
  simp [PTFamily.n, PTFamily.affineAdd]

theorem PTFamily.affineAdd_dom (F : PTFamily) (a : GInt) (c : ℤ) (k : ℕ) :
    (F.affineAdd a c).dom k = F.dom k := by
  simp [PTFamily.dom, PTFamily.tile, PTFamily.affineAdd]

theorem PTFamily.affineAdd_odo (F : PTFamily) (a : GInt) (c : ℤ) (k : ℕ) (x : GInt) :
    (F.affineAdd a c).odo k x = F.odo k x + a.1 * x.1 + a.2 * x.2 + c := by
  unfold PTFamily.odo PTFamily.affineAdd PTFamily.tile
  simp only [Prod.fst_add, Prod.snd_add]
  ring

/-- The unit squares of every placed tile are nonempty (its shape has a unit square, translated by its position). -/
theorem PTFamily.dom_unitSquares_ne (F : PTFamily) (k : ℕ) : unitSquares (F.dom k) ≠ [] := by
  unfold PTFamily.dom
  rw [unitSquares_map_add]
  intro h
  exact tileShape_unitSquares_ne_zt (F.tile k).1 (List.map_eq_nil_iff.mp h)

/-- The slope of the odometer plus the affine term `a·x + c` is the slope plus `a`. -/
theorem slopeOf_affineAdd (g : GInt → ℤ) (L : List GInt) (a : GInt) (c : ℤ) (hne : unitSquares L ≠ []) :
    slopeOf (fun x => g x + a.1 * x.1 + a.2 * x.2 + c) L = slopeOf g L + ((a.1 : ℚ), (a.2 : ℚ)) := by
  have h := slopeOf_translate_affine g L 0 a c hne
  simpa using h

/-- **Respects is invariant under adding a common affine function.** -/
theorem PTFamily.affineAdd_respects (F : PTFamily) (o : Orientation) (rev : Bool) (a : GInt) (c : ℤ)
    (h : F.Respects o rev) : (F.affineAdd a c).Respects o rev := by
  intro k hk
  rw [PTFamily.affineAdd_n] at hk
  have hk' : k < F.n := by omega
  have hk1 : k + 1 < F.n := hk
  obtain ⟨hsl, hcl⟩ := h k hk
  refine ⟨?_, ?_⟩
  · have f1 : (F.affineAdd a c).odo (k + 1) = fun x => F.odo (k + 1) x + a.1 * x.1 + a.2 * x.2 + c :=
      funext (PTFamily.affineAdd_odo F a c (k + 1))
    have f0 : (F.affineAdd a c).odo k = fun x => F.odo k x + a.1 * x.1 + a.2 * x.2 + c :=
      funext (PTFamily.affineAdd_odo F a c k)
    rw [f1, f0, PTFamily.affineAdd_dom F a c (k + 1), PTFamily.affineAdd_dom F a c k]
    rw [slopeOf_affineAdd _ _ a c (F.dom_unitSquares_ne (k + 1)),
      slopeOf_affineAdd _ _ a c (F.dom_unitSquares_ne k)]
    rw [show ∀ p q r : ℚ × ℚ, p + r - (q + r) = p - q from fun p q r => by abel]
    exact hsl
  · intro hno x hx y hy hu
    have hno' : ¬ ∃ z, z ∈ F.dom k ∧ z ∈ F.dom (k + 1) := by
      rintro ⟨z, h1, h2⟩
      apply hno
      refine ⟨z, ?_, ?_⟩
      · rw [PTFamily.affineAdd_dom F a c k]; exact h1
      · rw [PTFamily.affineAdd_dom F a c (k + 1)]; exact h2
    have hx' : x ∈ F.dom k := by rw [← PTFamily.affineAdd_dom F a c k]; exact hx
    have hy' : y ∈ F.dom (k + 1) := by rw [← PTFamily.affineAdd_dom F a c (k + 1)]; exact hy
    obtain ⟨hH, hV⟩ := hcl hno' x hx' y hy' hu
    refine ⟨fun h0 => ?_, fun h0 => ?_⟩
    · have key := hH h0
      rw [PTFamily.affineAdd_odo F a c k x, PTFamily.affineAdd_odo F a c (k + 1) y]
      simp only [PTFamily.affineAdd, ptDot, Prod.fst_add, Prod.snd_add] at key ⊢
      linarith
    · have key := hV h0
      rw [PTFamily.affineAdd_odo F a c k x, PTFamily.affineAdd_odo F a c (k + 1) y]
      simp only [PTFamily.affineAdd, ptDot, Prod.fst_add, Prod.snd_add] at key ⊢
      linarith

end FLatticePaper.Tiles
