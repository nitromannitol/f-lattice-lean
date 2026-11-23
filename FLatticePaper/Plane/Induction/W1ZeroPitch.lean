import FLatticePaper.Plane.Induction.ChildFrame

/-! # Task 77 (hagree, first step): the zero-pitch rank as a Lean object

The zero-pitch rank of `.work/fields/canonical/ZERO_PITCH_RANK_REPLACES_NOWRAP.md` is built from the drifts of the primitive price `P` and of
a second function `J_η` on the child lattice `U` (kernel), `V` (transverse):

* `P(z + U) = P(z) − 1`, `P(z + V) = P(z)`; `J_η(z + U) = J_η(z)`, `J_η(z + V) = J_η(z) + η`;
* `K = P + 2 J_η` then has `K(z + U) = K(z) − 1`, `K(z + V) = K(z) + 2η`, and `K(z + W) = K(z)` for `W = 2η U + V`;
* the rank `R = H K + b` with `b` periodic under `U` and `V` satisfies `R(z + W) = R(z)` exactly (`H` is arbitrary).

This is the periodicity identity of the note (`R(z+W) = R(z)`). The existence of a strict rank with these properties on the canonical
graph, which the note's argument needs, is NOT proved here: it is the named hypothesis of the rank descent. -/

namespace FLatticePaper.W1ZeroPitch

open FLatticePaper FLatticePaper.Induction

/-- A function that moves by the constant `c` along a vector `v` moves by `k c` along `k • v`. -/
theorem shift_zsmul {f : Site → ℤ} {v : Site} {c : ℤ} (h : ∀ z, f (z + v) = f z + c) (k : ℤ) (z : Site) :
    f (z + k • v) = f z + k * c := by
  induction k using Int.induction_on with
  | zero => simp
  | succ i ih =>
    have hs : z + ((i : ℤ) + 1) • v = (z + (i : ℤ) • v) + v := by
      rw [add_smul, one_smul, add_assoc]
    rw [hs, h, ih]
    ring
  | pred i ih =>
    have h2 := h (z + (-(i : ℤ) - 1) • v)
    have hs : z + (-(i : ℤ) - 1) • v + v = z + (-(i : ℤ)) • v := by
      rw [add_assoc]
      congr 1
      rw [sub_smul, one_smul, sub_add_cancel]
    rw [hs, ih] at h2
    linarith

/-- The drifts of the zero-pitch pair `(P, J_η)` along the child kernel `U` and transverse `V`. -/
structure ZeroPitchDrift (frame : ChildFrame) (P J : Site → ℤ) (η : ℤ) : Prop where
  P_U : ∀ z, P (z + frame.child.modifiedDeck.kernel) = P z - 1
  P_V : ∀ z, P (z + frame.child.modifiedDeck.transverse) = P z
  J_U : ∀ z, J (z + frame.child.modifiedDeck.kernel) = J z
  J_V : ∀ z, J (z + frame.child.modifiedDeck.transverse) = J z + η

/-- `K = P + 2 J_η` has the drifts `−1` on `U` and `2η` on `V`. -/
theorem zeroPitch_K_drift {frame : ChildFrame} {P J : Site → ℤ} {η : ℤ} (hD : ZeroPitchDrift frame P J η) :
    (∀ z, (P + 2 • J) (z + frame.child.modifiedDeck.kernel) = (P + 2 • J) z - 1) ∧
      (∀ z, (P + 2 • J) (z + frame.child.modifiedDeck.transverse) = (P + 2 • J) z + 2 * η) := by
  constructor
  · intro z
    simp only [Pi.add_apply, Pi.smul_apply]
    rw [hD.P_U, hD.J_U]
    ring
  · intro z
    simp only [Pi.add_apply, Pi.smul_apply]
    rw [hD.P_V, hD.J_V]
    ring

/-- **The zero-pitch rank is periodic along `W = 2η U + V`** (task 77): for `R = H K + b` with `b` periodic under `U` and `V`,
`R(z + W) = R(z)`. -/
theorem zeroPitch_rank_periodic {frame : ChildFrame} {P J b : Site → ℤ} {η : ℤ} (H : ℤ)
    (hD : ZeroPitchDrift frame P J η) (hbU : ∀ z, b (z + frame.child.modifiedDeck.kernel) = b z)
    (hbV : ∀ z, b (z + frame.child.modifiedDeck.transverse) = b z) (z : Site) :
    (H • (P + 2 • J) + b) (z + ((2 * η) • frame.child.modifiedDeck.kernel + frame.child.modifiedDeck.transverse)) =
      (H • (P + 2 • J) + b) z := by
  obtain ⟨hKU, hKV⟩ := zeroPitch_K_drift hD
  have hK : ∀ k : ℤ, ∀ w, (P + 2 • J) (w + k • frame.child.modifiedDeck.kernel) = (P + 2 • J) w - k := by
    intro k w
    have := shift_zsmul (f := P + 2 • J) (v := frame.child.modifiedDeck.kernel) (c := -1) hKU k w
    rw [this]
    ring
  have hb : ∀ k : ℤ, ∀ w, b (w + k • frame.child.modifiedDeck.kernel) = b w := by
    intro k w
    have := shift_zsmul (f := b) (v := frame.child.modifiedDeck.kernel) (c := 0)
      (fun w' => by rw [hbU w']; ring) k w
    rw [this]
    ring
  have hw : z + ((2 * η) • frame.child.modifiedDeck.kernel + frame.child.modifiedDeck.transverse) =
      (z + (2 * η) • frame.child.modifiedDeck.kernel) + frame.child.modifiedDeck.transverse := by
    rw [add_assoc]
  rw [hw]
  show H • (P + 2 • J) ((z + (2 * η) • frame.child.modifiedDeck.kernel) + frame.child.modifiedDeck.transverse) +
      b ((z + (2 * η) • frame.child.modifiedDeck.kernel) + frame.child.modifiedDeck.transverse) =
    H • (P + 2 • J) z + b z
  rw [hKV, hbV, hK (2 * η) z, hb (2 * η) z]
  simp only [smul_eq_mul]
  ring

end FLatticePaper.W1ZeroPitch
