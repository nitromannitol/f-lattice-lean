import FLatticePaper.Plane.Induction.FreeOrbit
import FLatticePaper.Plane.Induction.FreeVOrdinate
import FLatticePaper.Plane.Induction.PriceDeck
import FLatticePaper.Plane.Induction.StrongPriceValues

/-! hfreeP, the V case in full (the lead's order: V price first).

For a free V site `c` the prescribed input `c + prescribedV η c` has `sGrade` in the harmonic window `[3 − 2d, 2L − 1]` (both signs), so the
harmonic strip gives `F = harmonicGrid` at the input and at `input − parentShift` (`sGrade parentShift = 2`), and the price is `cutPrice`
(`price_eq_cutPrice_of_harmonic`). The free V site itself has price `cutPrice` (`price_on_freeV`). So the prescribed V input has the same
price as the free V white. The only nontrivial case is the even corner `s = 0` with `d − n = 2`, which is `vFirst` by the ordinate bound. -/

namespace FLatticePaper.FreeVCover

open Farey FLatticePaper FLatticePaper.Induction

/-- The even corner: `(d + n) x + (d − n) y = 0` with `d = n + 2`, `0 ≤ y ≤ L − 1` and `x + y` even forces `x = y = 0`. -/
theorem zero_case_aux (n d x y : ℤ) (hn : n % 2 = 1) (hn0 : 0 < n) (hd : d = n + 2)
    (hs : (d + n) * x + (d - n) * y = 0) (hy0 : 0 ≤ y) (hyL : y ≤ d + n - 1) (he : (x + y) % 2 = 0) :
    x = 0 ∧ y = 0 := by
  subst hd
  rcases lt_trichotomy x 0 with hx | hx | hx
  · rcases (show x = -1 ∨ x ≤ -2 by omega) with rfl | hx2
    · exfalso
      have hy : y = n + 1 := by linarith
      omega
    · exfalso
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ 2 * n + 2 by linarith) (show (0 : ℤ) ≤ -x - 2 by linarith)]
  · subst hx
    exact ⟨rfl, by linarith⟩
  · exfalso
    nlinarith [mul_pos (show (0 : ℤ) < 2 * n + 2 by linarith) (show (0 : ℤ) < x by linarith)]

/-- The even corner at the frame: an even free V site with `s = 0` and `d − n = 2` is `vFirst`. -/
theorem even_zero_eq_vFirst (frame : ChildFrame) {c : Site} (hc : c ∈ frame.freeV) (he : EvenSite c)
    (hs : frame.sGrade c = 0) (hdn : frame.child.den - frame.child.num = 2) : c = vFirst := by
  obtain ⟨hn0, hnd, -, -, -⟩ := frame.child_facts
  obtain ⟨hy0, hyL, -⟩ := FLatticePaper.FreeVOrdinate.freeV_even_ordinate frame hc he
  obtain ⟨hodd, -⟩ := frame.child_odd
  have hd : frame.child.den = frame.child.num + 2 := by omega
  unfold ChildFrame.sGrade at hs
  unfold EvenSite at he
  obtain ⟨hx, hy⟩ := zero_case_aux frame.child.num frame.child.den c.1 c.2 (by omega) hn0 hd
    hs hy0 (by omega) he
  exact Prod.ext hx hy

/-- The grade of a shift by a literal pair. -/
theorem sGrade_add_lit (frame : ChildFrame) (z : Site) (a b : ℤ) :
    frame.sGrade (z + (a, b)) = frame.sGrade z + ((frame.child.den + frame.child.num) * a + (frame.child.den - frame.child.num) * b) :=
  frame.sGrade_add z (a, b)

/-- The primitive grade of the vFirst vertex vanishes. -/
theorem sGrade_vFirst (frame : ChildFrame) : frame.sGrade vFirst = 0 := by
  unfold ChildFrame.sGrade vFirst
  ring

/-- **The coverage.** For a free V site `c`, the prescribed input `c + prescribedV η c` has `sGrade` in `[3 − 2d, 2L − 1]`. -/
theorem prescribedV_grade (frame : ChildFrame) {c : Site} (hc : c ∈ frame.freeV) {η : ℤ} (hη : η = 1 ∨ η = -1) :
    3 - 2 * frame.child.den ≤ frame.sGrade (c + frame.prescribedV η c) ∧
      frame.sGrade (c + frame.prescribedV η c) ≤ 2 * (frame.child.den + frame.child.num) - 1 := by
  obtain ⟨hn0, hnd, hdn, hd3, hT⟩ := frame.child_facts
  obtain ⟨hl, hh⟩ := FLatticePaper.FreeOrbit.freeV_s_range frame hc
  have hs0 : EvenSite c → 0 ≤ frame.sGrade c := by
    intro he
    have h := hc.1
    unfold ChildFrame.closedPolygon at h
    simp only [Set.mem_setOf_eq, if_pos he] at h
    exact h.2.2.1
  have hvLeven : EvenSite frame.vLast := by
    dsimp only [EvenSite, ChildFrame.vLast]
    omega
  rcases hη with rfl | rfl
  · by_cases h1 : c = vFirst
    · subst h1
      have hsum : frame.sGrade (vFirst + frame.prescribedV 1 vFirst) =
          frame.sGrade vFirst + (frame.child.den + frame.child.num) := by
        rw [frame.prescribedV_vFirst 1, sGrade_add_lit]
        ring
      rw [hsum, sGrade_vFirst]
      constructor <;> omega
    · by_cases he : EvenSite c
      · have hp : frame.prescribedV 1 c = (1, 0) := by
          unfold ChildFrame.prescribedV
          by_cases h2 : c = frame.vLast
          · simp [h2]
          · simp [h2, he]
        have hsum : frame.sGrade (c + frame.prescribedV 1 c) =
            frame.sGrade c + (frame.child.den + frame.child.num) := by
          rw [hp, sGrade_add_lit]
          ring
        rw [hsum]
        constructor <;> omega
      · have hp : frame.prescribedV 1 c = (0, -1) := by
          unfold ChildFrame.prescribedV
          have h2 : c ≠ frame.vLast := fun h => he (h ▸ hvLeven)
          simp [h1, h2, he]
        have hsum : frame.sGrade (c + frame.prescribedV 1 c) =
            frame.sGrade c - (frame.child.den - frame.child.num) := by
          rw [hp, sGrade_add_lit]
          ring
        rw [hsum]
        constructor <;> omega
  · by_cases h1 : c = vFirst
    · subst h1
      have hsum : frame.sGrade (vFirst + frame.prescribedV (-1) vFirst) =
          frame.sGrade vFirst + (frame.child.den + frame.child.num) := by
        rw [frame.prescribedV_vFirst (-1), sGrade_add_lit]
        ring
      rw [hsum, sGrade_vFirst]
      constructor <;> omega
    · by_cases he : EvenSite c
      · have hp : frame.prescribedV (-1) c = (-1, 0) := by
          unfold ChildFrame.prescribedV
          rw [if_neg h1]
          by_cases h2 : c = frame.vLast
          · rw [if_pos h2]
          · rw [if_neg h2, if_pos he]
        have hsum : frame.sGrade (c + frame.prescribedV (-1) c) =
            frame.sGrade c - (frame.child.den + frame.child.num) := by
          rw [hp, sGrade_add_lit]
          ring
        rw [hsum]
        have hcov : frame.child.den - frame.child.num = 2 → 0 < frame.sGrade c := by
          intro hdn2
          have hz : frame.sGrade c ≠ 0 := fun hs => h1 (even_zero_eq_vFirst frame hc he hs hdn2)
          have := hs0 he
          omega
        by_cases hdn2 : frame.child.den - frame.child.num = 2
        · have := hcov hdn2
          constructor <;> omega
        · have := hs0 he
          constructor <;> omega
      · have hp : frame.prescribedV (-1) c = (0, 1) := by
          unfold ChildFrame.prescribedV
          have h2 : c ≠ frame.vLast := fun h => he (h ▸ hvLeven)
          rw [if_neg h1, if_neg h2, if_neg he]
          norm_num
        have hsum : frame.sGrade (c + frame.prescribedV (-1) c) =
            frame.sGrade c + (frame.child.den - frame.child.num) := by
          rw [hp, sGrade_add_lit]
          ring
        rw [hsum]
        constructor <;> omega

/-- `sGrade` is linear: the grade of a difference. -/
theorem sGrade_sub_lin (frame : ChildFrame) (z u : Site) : frame.sGrade (z - u) = frame.sGrade z - frame.sGrade u := by
  unfold ChildFrame.sGrade
  simp only [Prod.fst_sub, Prod.snd_sub]
  ring

/-- **The V price, for every prescribed input.** The prescribed input of a free V site has the price of the site (both are `cutPrice`):
the harmonic strip holds at the input and at its parent-shift translate (the coverage), and `price_eq_cutPrice_of_harmonic` applies. -/
theorem freeV_prescribed_price (frame : ChildFrame) {F : Field} (hS : frame.HasStrips F) {c : Site}
    (hc : c ∈ frame.freeV) {η : ℤ} (hη : η = 1 ∨ η = -1) :
    frame.price F (c + frame.prescribedV η c) = frame.price F c := by
  obtain ⟨h1, h2⟩ := prescribedV_grade frame hc hη
  have hF : F (c + frame.prescribedV η c) = harmonicGrid (c + frame.prescribedV η c) :=
    hS.2 _ (by omega) h2
  have hsub : frame.sGrade (c + frame.prescribedV η c - frame.parentShift) =
      frame.sGrade (c + frame.prescribedV η c) - 2 := by
    rw [sGrade_sub_lin, FLatticePaper.PriceDeck.sGrade_parentShift]
  have hF' : F (c + frame.prescribedV η c - frame.parentShift) =
      harmonicGrid (c + frame.prescribedV η c - frame.parentShift) :=
    hS.2 _ (by rw [hsub]; omega) (by rw [hsub]; omega)
  rw [FLatticePaper.PriceDeck.price_on_freeV frame F hS hc, StrongPriceValues.price_eq_cutPrice_of_harmonic frame F _ hF hF']

end FLatticePaper.FreeVCover
