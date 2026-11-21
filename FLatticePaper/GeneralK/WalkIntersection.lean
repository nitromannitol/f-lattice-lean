import FLatticePaper.GeneralK.AxisPotential
import FLatticePaper.GeneralK.AxisWalkFlux
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

namespace FLatticePaper.GeneralK

private theorem sum_shift {n : ℕ} [NeZero n] (f : ZMod n → ℤ) (shift : ZMod n) :
    ∑ i : ZMod n, f (i + shift) = ∑ i : ZMod n, f i :=
  Equiv.sum_comp (Equiv.addRight shift) f

private theorem sum_cast_range {n : ℕ} [NeZero n] (f : ZMod n → ℤ) :
    ∑ i ∈ Finset.range n, f (i : ZMod n) = ∑ i : ZMod n, f i := by
  classical
  calc
    _ = ∑ i : Fin n, f (i.val : ZMod n) := by
      symm
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i hi
      rw [dif_pos (Finset.mem_range.mp hi)]
    _ = ∑ i : Fin n, f (ZMod.finEquiv n i) := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      rw [← ZMod.natCast_zmod_val (ZMod.finEquiv n i)]
      congr 1
      cases n with
      | zero => exact Fin.elim0 i
      | succ n => rfl
    _ = _ := Equiv.sum_comp (ZMod.finEquiv n).toEquiv f

private theorem constant_of_add_one {n : ℕ} [NeZero n] (f : ZMod n → ℤ)
    (h : ∀ point, f (point + 1) = f point) (point : ZMod n) : f point = f 0 := by
  have hnat (i : ℕ) : f (i : ZMod n) = f 0 := by
    induction i with
    | zero => simp
    | succ i ih => simpa only [Nat.cast_succ] using (h (i : ZMod n)).trans ih
  simpa only [ZMod.natCast_zmod_val] using hnat point.val

private theorem lineFlux_constant {n : ℕ} [NeZero n] {horizontal vertical : ZMod n → ZMod n → ℤ}
    (hdiv : ∀ x y, horizontal x y - horizontal (x - 1) y + (vertical x y - vertical x (y - 1)) = 0) :
    (∀ y, ∑ x : ZMod n, vertical x y = ∑ x : ZMod n, vertical x 0) ∧
    (∀ x, ∑ y : ZMod n, horizontal x y = ∑ y : ZMod n, horizontal 0 y) := by
  constructor
  · apply constant_of_add_one (fun y => ∑ x : ZMod n, vertical x y)
    intro y
    have h : (∑ x : ZMod n, (horizontal x (y + 1) - horizontal (x - 1) (y + 1) +
        (vertical x (y + 1) - vertical x ((y + 1) - 1)))) = 0 := by
      simp only [hdiv, Finset.sum_const_zero]
    have hshift : ∑ x : ZMod n, horizontal (x - 1) (y + 1) = ∑ x : ZMod n, horizontal x (y + 1) :=
      by simpa only [sub_eq_add_neg] using sum_shift (fun x => horizontal x (y + 1)) (-1)
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib, hshift, sub_self, zero_add, add_sub_cancel_right] at h
    exact sub_eq_zero.mp h
  · apply constant_of_add_one (fun x => ∑ y : ZMod n, horizontal x y)
    intro x
    have h : (∑ y : ZMod n, (horizontal (x + 1) y - horizontal ((x + 1) - 1) y +
        (vertical (x + 1) y - vertical (x + 1) (y - 1)))) = 0 := by
      simp only [hdiv, Finset.sum_const_zero]
    have hshift : ∑ y : ZMod n, vertical (x + 1) (y - 1) = ∑ y : ZMod n, vertical (x + 1) y :=
      by simpa only [sub_eq_add_neg] using sum_shift (vertical (x + 1)) (-1)
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib, hshift, sub_self, add_zero, add_sub_cancel_right] at h
    exact sub_eq_zero.mp h

private theorem displacement_of_squarePeriod {n : ℕ} [NeZero n] {start last : Site} {a b : ℤ}
    (h : last = start + ((n : ℤ) * a, (n : ℤ) * b)) : residueVertex n last = residueVertex n start := by
  rw [h]
  simp [residueVertex]

/-- On the square quotient, closed walks of independent lifted winding have
a common vertex. The proof integrates the signed net crossings of the first
walk on the translated grid and uses its constant flux through each cut. -/
theorem determinant_eq_zero_of_disjoint_squareWalks {n : ℕ} [NeZero n] (first second : Site)
    (walk₁ walk₂ : List AxisStep) (a b c d : ℤ)
    (hw₁ : walkEnd first walk₁ = first + ((n : ℤ) * a, (n : ℤ) * b))
    (hw₂ : walkEnd second walk₂ = second + ((n : ℤ) * c, (n : ℤ) * d))
    (hdisjoint : ∀ x ∈ walkVertices first walk₁, ∀ y ∈ walkVertices second walk₂,
      residueVertex n x ≠ residueVertex n y) : a * d - b * c = 0 := by
  let horizontal := horizontalWalkCount n first walk₁
  let vertical := verticalWalkCount n first walk₁
  have hdiv (x y : ZMod n) : horizontal x y - horizontal (x - 1) y +
      (vertical x y - vertical x (y - 1)) = 0 :=
    walkCount_divergence_eq_zero (displacement_of_squarePeriod hw₁ : residueVertex n (walkEnd first walk₁) = _) x y
  obtain ⟨hvline, hhline⟩ := lineFlux_constant hdiv
  have hn₀ : (n : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hhflux : ∑ y : ZMod n, horizontal 0 y = a := by
    have h := sum_horizontalWalkCount (period := n) first walk₁
    change ∑ x : ZMod n, ∑ y : ZMod n, horizontal x y = _ at h
    simp only [hhline, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, hw₁, Prod.fst_add, add_sub_cancel_left] at h
    exact mul_left_cancel₀ hn₀ h
  have hvflux : ∑ x : ZMod n, vertical x 0 = b := by
    have h := sum_verticalWalkCount (period := n) first walk₁
    change ∑ x : ZMod n, ∑ y : ZMod n, vertical x y = _ at h
    rw [Finset.sum_comm] at h
    simp only [hvline, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, hw₁, Prod.snd_add, add_sub_cancel_left] at h
    exact mul_left_cancel₀ hn₀ h
  let dx (x y : ℤ) := -vertical ((x : ZMod n) + 1) (y : ZMod n)
  let dy (x y : ℤ) := horizontal (x : ZMod n) ((y : ZMod n) + 1)
  let potential := axisPotential dx dy
  have hcurl (x y : ℤ) : dy (x + 1) y - dy x y = dx x (y + 1) - dx x y := by
    have h := hdiv ((x : ZMod n) + 1) ((y : ZMod n) + 1)
    simp only [add_sub_cancel_right] at h
    simp only [dx, dy, Int.cast_add, Int.cast_one]
    change horizontal _ _ - horizontal _ _ + (vertical _ _ - vertical _ _) = 0 at h
    omega
  have hpx : potential ((n : ℤ), 0) = -b := by
    change axisPotential dx dy ((n : ℤ), 0) = -b
    rw [axisPotential_nat_horizontal]
    simp only [dx, Int.cast_natCast, Int.cast_zero, Finset.sum_neg_distrib]
    rw [sum_cast_range (fun x => vertical (x + 1) 0), sum_shift (fun x => vertical x 0), hvflux]
  have hpy : potential (0, (n : ℤ)) = a := by
    change axisPotential dx dy (0, (n : ℤ)) = a
    rw [axisPotential_nat_vertical]
    simp only [dy, Int.cast_natCast, Int.cast_zero]
    rw [sum_cast_range (fun y => horizontal 0 (y + 1)), sum_shift (horizontal 0), hhflux]
  have hX (site : Site) : potential (site + ((n : ℤ), 0)) = potential site - b := by
    have h := axisPotential_shift hcurl ((n : ℤ), 0) (by intros; simp [dx]) (by intros; simp [dy]) site
    change potential _ - potential site = potential _ at h
    rw [hpx] at h
    omega
  have hY (site : Site) : potential (site + (0, (n : ℤ))) = potential site + a := by
    have h := axisPotential_shift hcurl (0, (n : ℤ)) (by intros; simp [dx]) (by intros; simp [dy]) site
    change potential _ - potential site = potential _ at h
    rw [hpy] at h
    omega
  have htranslate (site : Site) (step : Site) (difference : ℤ) (hstep : ∀ z, potential (z + step) = potential z + difference)
      (i : ℤ) : potential (site + i • step) = potential site + i * difference := by
    refine Int.inductionOn' i 0 (by simp) ?_ ?_
    · intro j _ ih
      rw [add_zsmul, one_zsmul, ← add_assoc, hstep, ih, add_mul, one_mul, add_assoc]
    · intro j _ ih
      have h := hstep (site + (j - 1) • step)
      have heq : site + (j - 1) • step + step = site + j • step := by
        rw [sub_zsmul, one_zsmul]
        abel
      rw [heq, ih] at h
      rw [sub_mul, one_mul]
      omega
  have hchange : potential (walkEnd second walk₂) = potential second + (a * d - b * c) := by
    rw [hw₂]
    have heq : ((n : ℤ) * c, (n : ℤ) * d) = c • ((n : ℤ), (0 : ℤ)) + d • ((0 : ℤ), (n : ℤ)) := by
      apply Prod.ext <;> simp <;> ring
    rw [heq, ← add_assoc, htranslate _ _ a hY, htranslate _ _ (-b) (by simpa [sub_eq_add_neg] using hX)]
    ring
  have hconstant (second : Site) (walk₂ : List AxisStep)
      (hdisjoint : ∀ x ∈ walkVertices first walk₁, ∀ y ∈ walkVertices second walk₂,
        residueVertex n x ≠ residueVertex n y) : potential (walkEnd second walk₂) = potential second := by
    induction walk₂ generalizing second with
    | nil => rfl
    | cons direction rest ih =>
      let next := second + direction.vector
      have htail : ∀ x ∈ walkVertices first walk₁, ∀ y ∈ walkVertices next rest,
          residueVertex n x ≠ residueVertex n y :=
        fun x hx y hy => hdisjoint x hx y (Finset.mem_insert_of_mem hy)
      have hzero (site : Site) (hsite : site ∈ walkVertices second (direction :: rest)) :
          horizontal (site.1 : ZMod n) (site.2 : ZMod n) = 0 ∧
          vertical (site.1 : ZMod n) (site.2 : ZMod n) = 0 :=
        walkCount_eq_zero_of_not_visited first walk₁ _ _ (fun x hx heq => hdisjoint x hx site hsite heq.symm)
      have hhere := hzero second (start_mem_walkVertices ..)
      have hnext := hzero next (Finset.mem_insert_of_mem (start_mem_walkVertices ..))
      have hone : potential next = potential second := by
        obtain ⟨x, y⟩ := second
        cases direction
        · have h := axisPotential_add_horizontal hcurl x y
          change potential (x + 1, y) - potential (x, y) = -vertical ((x : ZMod n) + 1) (y : ZMod n) at h
          have hz : vertical ((x : ZMod n) + 1) (y : ZMod n) = 0 := by simpa [next, AxisStep.vector] using hnext.2
          rw [hz, neg_zero] at h
          simpa [next, AxisStep.vector] using sub_eq_zero.mp h
        · have h := axisPotential_add_horizontal hcurl (x - 1) y
          rw [sub_add_cancel] at h
          change potential (x, y) - potential (x - 1, y) = -vertical (((x - 1 : ℤ) : ZMod n) + 1) (y : ZMod n) at h
          rw [Int.cast_sub, Int.cast_one, sub_add_cancel, hhere.2, neg_zero] at h
          simpa [next, AxisStep.vector, sub_eq_add_neg] using (sub_eq_zero.mp h).symm
        · have h := axisPotential_add_vertical dx dy x y
          change potential (x, y + 1) - potential (x, y) = horizontal (x : ZMod n) ((y : ZMod n) + 1) at h
          have hz : horizontal (x : ZMod n) ((y : ZMod n) + 1) = 0 := by simpa [next, AxisStep.vector] using hnext.1
          rw [hz] at h
          simpa [next, AxisStep.vector] using sub_eq_zero.mp h
        · have h := axisPotential_add_vertical dx dy x (y - 1)
          rw [sub_add_cancel] at h
          change potential (x, y) - potential (x, y - 1) = horizontal (x : ZMod n) (((y - 1 : ℤ) : ZMod n) + 1) at h
          rw [Int.cast_sub, Int.cast_one, sub_add_cancel, hhere.1] at h
          simpa [next, AxisStep.vector, sub_eq_add_neg] using (sub_eq_zero.mp h).symm
      exact (ih next htail).trans hone
  rw [hconstant second walk₂ hdisjoint] at hchange
  omega

end FLatticePaper.GeneralK
