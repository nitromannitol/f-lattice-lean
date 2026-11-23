import FLatticePaper.Plane.Induction.W1Forcing

/-! Task 61, §5: at an `M`-white tie both inputs tie (W1_CONSTRUCTOR §5).

Setting. Two binary sheets `A`, `C` on the square around a site `c`, the field `F = min(A, C)` on `c` and on its two inputs, and
the sheet difference `Ψ = C − A` with unit increments along edges. A tie is a site with `Ψ(c) = 0` (so `A(c) = C(c) = F(c)`).
The claim: if `F` is white at `c` (`laplacian F c = 0`), then `Ψ(i) = 0` at both inputs `i` of `c`.

Proof (algebra only). Put `a_j = A(i_j) − A(c)`, `c_j = C(i_j) − C(c)`. Then `F(i_j) − F(c) = min(a_j, c_j)`, the white condition
says `min(a_1, c_1) + min(a_2, c_2) = 0`, binarity says `a_1 + a_2 ∈ {−1, 0}` and `c_1 + c_2 ∈ {−1, 0}`, and unit increments of `Ψ`
say `|c_j − a_j| ≤ 1`. These four facts force `c_j = a_j` (exhaustive check; `omega` after unfolding `min`), i.e. `Ψ(i_j) = Ψ(c) = 0`.
-/

namespace FLatticePaper.W1Ties

/-- The integer core: binarity of the two sums, unit difference, and whiteness of the minimum force the two differences to agree. -/
theorem tie_core (a1 a2 c1 c2 : ℤ) (ha : a1 + a2 = -1 ∨ a1 + a2 = 0) (hc : c1 + c2 = -1 ∨ c1 + c2 = 0)
    (hd1 : c1 - a1 ≤ 1 ∧ a1 - c1 ≤ 1) (hd2 : c2 - a2 ≤ 1 ∧ a2 - c2 ≤ 1)
    (hw : min a1 c1 + min a2 c2 = 0) : c1 = a1 ∧ c2 = a2 := by
  omega

/-- The field form at a site `c` of the child: the sheets `A`, `C` binary at `c`, `F = min(A, C)` at `c` and its inputs, `Ψ = C − A`
with unit increments at the inputs, and `F` white at `c`. Then `Ψ` vanishes at both inputs whenever `c` is a tie. -/
theorem tie_inputs_of_white (A C F : Site → ℤ) (c : Site)
    (hA : laplacian A c = -1 ∨ laplacian A c = 0) (hC : laplacian C c = -1 ∨ laplacian C c = 0)
    (htie : A c = C c) (hFc : F c = min (A c) (C c))
    (hFi : ∀ i, (i = incomingNeg c ∨ i = incomingPos c) → F i = min (A i) (C i))
    (hΨ : ∀ i, (i = incomingNeg c ∨ i = incomingPos c) →
      (C i - A i) - (C c - A c) ≤ 1 ∧ (C c - A c) - (C i - A i) ≤ 1)
    (hw : laplacian F c = 0) :
    ∀ i, (i = incomingNeg c ∨ i = incomingPos c) → C i - A i = C c - A c := by
  intro i hi
  have h1 := hFi (incomingNeg c) (Or.inl rfl)
  have h2 := hFi (incomingPos c) (Or.inr rfl)
  have hΨ1 := hΨ (incomingNeg c) (Or.inl rfl)
  have hΨ2 := hΨ (incomingPos c) (Or.inr rfl)
  unfold laplacian at hA hC hw
  have key := tie_core (A (incomingNeg c) - A c) (A (incomingPos c) - A c) (C (incomingNeg c) - C c)
    (C (incomingPos c) - C c) (by omega) (by omega) (by omega) (by omega)
    (by omega)
  rcases hi with h | h <;> subst h <;> omega

end FLatticePaper.W1Ties
