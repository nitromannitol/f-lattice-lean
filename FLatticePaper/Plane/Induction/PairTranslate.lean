import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination

/-! # The pair translate (hpaid, matched pairing)

For functions `P, J` on an additive group with the deck drifts `P (z + U) = P z − 1`, `P (z + V) = P z`, `J (z + U) = J z`,
`J (z + V) = J z + η` (`η = ±1`), every point `e` has a span translate `e + kU + lV` with pair `(c₀, 0)`: take
`k = P e − c₀` and `l = −η J e`. If `e` is `v + k'U + l'V` with `v` free, the translate is own-deck free: a free H point
translated by `U` (its `J` is `0`), or a free V point translated by `V` (its `P` is `c₀`). -/

namespace FLatticePaper.PairTranslate

/-- Integer iteration of a drift: `G (z + k • v) = G z + k c` for every integer `k`. -/
theorem drift_zsmul {A : Type*} [AddCommGroup A] (G : A → ℤ) (v : A) (c : ℤ)
    (h : ∀ z, G (z + v) = G z + c) (k : ℤ) (z : A) : G (z + k • v) = G z + k * c := by
  induction k using Int.induction_on with
  | zero => simp
  | succ k ih =>
    have e1 : z + ((k : ℤ) + 1) • v = (z + (k : ℤ) • v) + v := by
      rw [add_zsmul, one_zsmul]; abel
    rw [e1, h, ih]; ring
  | pred k ih =>
    have h1 := h (z + (-(k : ℤ) - 1) • v)
    have e2 : z + (-(k : ℤ) - 1) • v + v = z + (-(k : ℤ)) • v := by
      rw [sub_zsmul, one_zsmul]; abel
    rw [e2, ih] at h1
    linear_combination (-1 : ℤ) * h1

/-- **The pair translate.** With the deck drifts and `η² = 1`, the translate `e + kU + lV` has pair `(c₀, 0)` for
`k = P e − c₀`, `l = −η J e`. -/
theorem pair_translate {A : Type*} [AddCommGroup A] (P J : A → ℤ) (U V : A) (η c0 : ℤ) (hη : η * η = 1)
    (hPU : ∀ z, P (z + U) = P z - 1) (hPV : ∀ z, P (z + V) = P z)
    (hJU : ∀ z, J (z + U) = J z) (hJV : ∀ z, J (z + V) = J z + η) (e : A) :
    ∃ k l : ℤ, P (e + k • U + l • V) = c0 ∧ J (e + k • U + l • V) = 0 := by
  refine ⟨P e - c0, -(η * J e), ?_, ?_⟩
  · have hPU' : ∀ z, P (z + U) = P z + (-1) := fun z => by rw [hPU z]; ring
    have hPV' : ∀ z, P (z + V) = P z + 0 := fun z => by rw [hPV z]; ring
    rw [drift_zsmul P V 0 hPV' (-(η * J e)), mul_zero, add_zero, drift_zsmul P U (-1) hPU' (P e - c0)]
    ring
  · have hJU' : ∀ z, J (z + U) = J z + 0 := fun z => by rw [hJU z]; ring
    rw [drift_zsmul J V η hJV (-(η * J e)), drift_zsmul J U 0 hJU' (P e - c0)]
    linear_combination (-(J e)) * hη

/-- **Own-deck membership of the translate.** If `e = v + k'U + l'V` with `v` free (H or V), `J = 0` on the free H sites and
`P = c₀` on the free V sites, then the pair translate `x = e + kU + lV` lies in `FH + ℤU` or in `FV + ℤV`. -/
theorem pair_own {A : Type*} [AddCommGroup A] (P J : A → ℤ) (U V : A) (η c0 : ℤ) (hη : η * η = 1)
    (hPU : ∀ z, P (z + U) = P z - 1) (hPV : ∀ z, P (z + V) = P z)
    (hJU : ∀ z, J (z + U) = J z) (hJV : ∀ z, J (z + V) = J z + η)
    (FH FV : A → Prop) (hJH : ∀ v, FH v → J v = 0) (hPF : ∀ v, FV v → P v = c0)
    (e : A) (hFree : ∃ k' l' : ℤ, FH (e - k' • U - l' • V) ∨ FV (e - k' • U - l' • V)) :
    ∃ k l : ℤ, P (e + k • U + l • V) = c0 ∧ J (e + k • U + l • V) = 0 ∧
      ((∃ m : ℤ, FH (e + k • U + l • V - m • U)) ∨ (∃ m : ℤ, FV (e + k • U + l • V - m • V))) := by
  obtain ⟨k', l', hv⟩ := hFree
  have hPU' : ∀ z, P (z + U) = P z + (-1) := fun z => by rw [hPU z]; ring
  have hPV' : ∀ z, P (z + V) = P z + 0 := fun z => by rw [hPV z]; ring
  have hJU' : ∀ z, J (z + U) = J z + 0 := fun z => by rw [hJU z]; ring
  have pval : ∀ (w : A) (a b : ℤ), P (w + a • U + b • V) = P w - a := by
    intro w a b
    rw [drift_zsmul P V 0 hPV' b, drift_zsmul P U (-1) hPU' a]; ring
  have jval : ∀ (w : A) (a b : ℤ), J (w + a • U + b • V) = J w + b * η := by
    intro w a b
    rw [drift_zsmul J V η hJV b, drift_zsmul J U 0 hJU' a]; ring
  set v := e - k' • U - l' • V with hvdef
  have he : e = v + k' • U + l' • V := by rw [hvdef]; abel
  obtain ⟨k, l, hP0, hJ0⟩ := pair_translate P J U V η c0 hη hPU hPV hJU hJV e
  have hx : e + k • U + l • V = v + (k' + k) • U + (l' + l) • V := by
    rw [he, add_zsmul, add_zsmul]; abel
  have hPx : P (e + k • U + l • V) = P v - (k' + k) := by rw [hx, pval]
  have hJx : J (e + k • U + l • V) = J v + (l' + l) * η := by rw [hx, jval]
  rcases hv with hFH | hFV
  · have hJv := hJH v hFH
    have hmul : (l' + l) * η = 0 := by linarith [hJ0, hJx]
    have hl0 : l' + l = 0 := by
      rcases mul_eq_zero.mp hmul with h | h
      · exact h
      · rw [h, mul_zero] at hη; exact absurd hη (by norm_num)
    refine ⟨k, l, hP0, hJ0, Or.inl ⟨k' + k, ?_⟩⟩
    have hsub : e + k • U + l • V - (k' + k) • U = v := by
      rw [hx, hl0, zero_zsmul, add_zero, add_sub_cancel_right]
    rw [hsub]; exact hFH
  · have hPv := hPF v hFV
    have hk0 : k' + k = 0 := by linarith [hP0, hPx]
    refine ⟨k, l, hP0, hJ0, Or.inr ⟨l' + l, ?_⟩⟩
    have hsub : e + k • U + l • V - (l' + l) • V = v := by
      rw [hx, hk0, zero_zsmul, add_zero, add_sub_cancel_right]
    rw [hsub]; exact hFV

end FLatticePaper.PairTranslate
