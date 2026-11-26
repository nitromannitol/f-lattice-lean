import FLatticePaper.Plane.Induction.FortMinRep
import FLatticePaper.Plane.Induction.PairTranslate

/-! # The restricted fort translates so that its minimal pair is `(c₀, 0)`

`FortMinRep.exists_fort_translate_min_rep` translates a restricted fort so that its minimum of `K = P + J` is at a representative `r`.
A second span translate `s = combine a b` with `a = c₀ − P r` and `b = η J r` moves `r` to the pair `(c₀, 0)`: `P` drops by `a` and
`J` rises by `b η = J r` along `s` (the deck drifts), so `K` shifts by a constant and the minimum stays at the same site. The translated
set is again a restricted fort (`isRestrictedFort_shiftSet` along the even span element `s`). -/

namespace FLatticePaper.FortPairMin

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.AuxRankQ1 FLatticePaper.RestrictedFortShift

theorem exists_fort_translate_c0 (frame : ChildFrame) (F : Field) (η : ℤ) (hη : η = 1 ∨ η = -1)
    (hPD : ∀ z, frame.price F (z + frame.child.modifiedDeck.kernel) = frame.price F z + -1 ∧
      frame.price F (z + frame.child.modifiedDeck.transverse) = frame.price F z + 0)
    (hSD : ∀ z, frame.slip F η (z + frame.child.modifiedDeck.kernel) = frame.slip F η z + 0 ∧
      frame.slip F η (z + frame.child.modifiedDeck.transverse) = frame.slip F η z + 2 * η)
    (hL : ∀ (c : Site) (i j : ℤ), laplacian F (c + frame.child.modifiedDeck.combine i j) = laplacian F c)
    {S : Set Site} (hres : IsRestrictedFort F (permitsQ1 frame F η) S) (hne : S.Nonempty) (level : ℤ)
    (hlev : ∀ z ∈ S, level ≤ frame.price F z + frame.roundedSlip F η z) :
    ∃ T ∈ frame.child.modifiedDeck.span, IsRestrictedFort F (permitsQ1 frame F η) (shiftSet S T) ∧
      (∃ r' ∈ shiftSet S T, frame.price F r' = frame.cutPrice ∧ frame.roundedSlip F η r' = 0) ∧
      ∀ z ∈ shiftSet S T, frame.cutPrice ≤ frame.price F z + frame.roundedSlip F η z := by
  obtain ⟨t0, ht0, hres0, r, hrSq, hrS0, hmin0⟩ :=
    FortMinRep.exists_fort_translate_min_rep frame F η hPD hSD hL hres hne level hlev
  have hηη : η * η = 1 := by rcases hη with rfl | rfl <;> norm_num
  -- the drifts of the rounded slip along the kernel and the transverse vector
  have hJk : ∀ z, frame.roundedSlip F η (z + frame.child.modifiedDeck.kernel) = frame.roundedSlip F η z := by
    intro z
    have h := (hSD z).1
    unfold ChildFrame.roundedSlip
    rw [h]
    omega
  have hJv : ∀ z, frame.roundedSlip F η (z + frame.child.modifiedDeck.transverse) =
      frame.roundedSlip F η z + η := by
    intro z
    have h := (hSD z).2
    unfold ChildFrame.roundedSlip
    rw [h]
    omega
  -- the drifts of P and J along combine i j
  have hc : ∀ i j : ℤ, frame.child.modifiedDeck.combine i j =
      i • frame.child.modifiedDeck.kernel + j • frame.child.modifiedDeck.transverse := by
    intro i j
    ext <;> simp [PeriodDeck.combine, zsmul_eq_mul]
  have hcombP : ∀ (z : Site) (i j : ℤ), frame.price F (z + frame.child.modifiedDeck.combine i j) =
      frame.price F z - i := by
    intro z i j
    rw [hc, ← add_assoc]
    have h1 := PairTranslate.drift_zsmul (frame.price F) _ (-1) (fun w => (hPD w).1) i z
    have h2 := PairTranslate.drift_zsmul (frame.price F) _ 0 (fun w => (hPD w).2) j (z + i • frame.child.modifiedDeck.kernel)
    rw [h2, h1]
    ring
  have hcombJ : ∀ (z : Site) (i j : ℤ), frame.roundedSlip F η (z + frame.child.modifiedDeck.combine i j) =
      frame.roundedSlip F η z + j * η := by
    intro z i j
    rw [hc, ← add_assoc]
    have h1 := PairTranslate.drift_zsmul (frame.roundedSlip F η) _ 0 (fun w => by rw [hJk w]; ring) i z
    have h2 := PairTranslate.drift_zsmul (frame.roundedSlip F η) _ η hJv j (z + i • frame.child.modifiedDeck.kernel)
    rw [h2, h1]
    ring
  -- the second translate
  obtain ⟨i0, j0, hi0⟩ := ht0
  set P0 := frame.price F r with hP0
  set J0 := frame.roundedSlip F η r with hJ0
  set a : ℤ := frame.cutPrice - P0 with ha
  set b : ℤ := η * J0 with hb
  set s : Site := frame.child.modifiedDeck.combine a b with hs
  have hsspan : s ∈ frame.child.modifiedDeck.span := ⟨a, b, rfl⟩
  have hEs : EvenSite s := FreePolicy.span_even frame hsspan
  have hLs : ∀ z, laplacian F (z + s) = laplacian F z := fun z => hL z a b
  have hPs : ∀ c i', permitsQ1 frame F η (c + s) (i' + s) ↔ permitsQ1 frame F η c i' :=
    fun c i' => permitsQ1_shift frame F η hL s hsspan c i'
  -- the translate `T = t0 + s` is a span element
  have hT : t0 + s ∈ frame.child.modifiedDeck.span := by
    refine ⟨i0 + a, j0 + b, ?_⟩
    rw [hi0, hs]
    ext <;> simp [PeriodDeck.combine] <;> ring
  -- `shiftSet S (t0 + s) = shiftSet (shiftSet S t0) s`
  have hset : shiftSet S (t0 + s) = shiftSet (shiftSet S t0) s := by
    ext z
    show z + (t0 + s) ∈ S ↔ z + s + t0 ∈ S
    rw [show z + (t0 + s) = z + s + t0 by abel]
  have hfort : IsRestrictedFort F (permitsQ1 frame F η) (shiftSet S (t0 + s)) := by
    rw [hset]
    exact isRestrictedFort_shiftSet hEs hLs hPs hres0
  refine ⟨t0 + s, hT, hfort, ⟨r - s, ?_, ?_, ?_⟩, ?_⟩
  · -- `r − s + (t0 + s) = r + t0 ∈ S`
    show (r - s) + (t0 + s) ∈ S
    rw [show r - s + (t0 + s) = r + t0 by abel]
    exact hrS0
  · -- the price at `r − s` is `c₀`
    have hrs : r - s = r + frame.child.modifiedDeck.combine (-a) (-b) := by
      rw [hs]
      ext <;> simp [PeriodDeck.combine] <;> ring
    rw [hrs, hcombP]
    simp only [ha, hP0]
    ring
  · -- the rounded slip at `r − s` is `0`
    have hrs : r - s = r + frame.child.modifiedDeck.combine (-a) (-b) := by
      rw [hs]
      ext <;> simp [PeriodDeck.combine] <;> ring
    rw [hrs, hcombJ]
    simp only [hb, hJ0]
    linear_combination (-J0) * hηη
  · -- the minimum of `K` on the translate is `c₀`
    intro z hz
    have hy : z + s ∈ shiftSet S t0 := by
      show z + s + t0 ∈ S
      have hz' : z + (t0 + s) ∈ S := hz
      rw [show z + s + t0 = z + (t0 + s) by abel]
      exact hz'
    have hmin := hmin0 (z + s) hy
    have hPz := hcombP z a b
    have hJz := hcombJ z a b
    rw [← hs] at hPz hJz
    rw [hPz, hJz] at hmin
    have hbη : b * η = J0 := by
      rw [hb]
      linear_combination J0 * hηη
    linarith [hmin, hbη, ha, hP0, hJ0]

end FLatticePaper.FortPairMin
