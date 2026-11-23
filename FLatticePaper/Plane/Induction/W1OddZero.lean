import FLatticePaper.Plane.Induction.W1VShift
import FLatticePaper.Plane.Induction.W1ZeroStrip
import FLatticePaper.Plane.Induction.StrongEstimates
import FLatticePaper.Plane.Induction.W1Exit

/-! # Task 74 (odd_zero): the odd seed is one orbit, and the seed value reduces the claim to one point

For a word `u` with child `(n, d)`, `parentN u = (d − n)/2` and `parentD u = (d + n)/2` (`StrongEstimates`), and the odd zero claim
(`SeedFields.odd_zero`) asks that `quarterTurnField (standardField u) x = 0` on the even sites of the line
`parentN x₁ − parentD x₂ = 1 − d`.

* The quarter turn is `g ∘ Z` with `g = F − h₀` and `Z x = (−x₂, x₁ − 1)` (`quarterTurn_eq_sub`).
* `g` is invariant under the transverse shift `V = (n − d, n + d) = (−2 parentN, 2 parentD)`: `F` and `h₀` both move by
  `t + c_V` (the packet's transverse period, and the harmonic identity `h₀(x + V) = h₀(x) + t(x) + c_V`).
* The even sites of the line are the seed `z` shifted by `2m·(parentD, parentN)`, and `Z` carries that shift to `m·V`.
So the whole line has the value of the seed `z`. This module proves these three steps and the reduction
`odd_zero_of_seed`: the claim follows from its value at one even point of the line. -/

namespace FLatticePaper.W1OddZero

open Farey FLatticePaper FLatticePaper.Induction

/-- The harmonic V-shift: `h₀(x + V) = h₀(x) + t(x) + c_V`, with `V = (n − d, n + d)` and `c_V` the coherent constant. -/
theorem harmonicGrid_add_V (frame : ChildFrame) (x : Site) :
    harmonicGrid (x + (frame.child.num - frame.child.den, frame.child.num + frame.child.den)) =
      harmonicGrid x + frame.tGrade x + frame.coherentConstantV := by
  have e1 : 4 * harmonicGrid (x + (frame.child.num - frame.child.den, frame.child.num + frame.child.den)) =
      (x.1 + (frame.child.num - frame.child.den)) ^ 2 +
        2 * (x.1 + (frame.child.num - frame.child.den)) * (x.2 + (frame.child.num + frame.child.den)) -
        (x.2 + (frame.child.num + frame.child.den)) ^ 2 - 2 * (x.2 + (frame.child.num + frame.child.den)) -
        (x.1 + (frame.child.num - frame.child.den) + (x.2 + (frame.child.num + frame.child.den))) % 2 :=
    harmonicGrid_exact _
  have e0 := harmonicGrid_exact x
  have hpar : (x.1 + (frame.child.num - frame.child.den) + (x.2 + (frame.child.num + frame.child.den))) % 2 =
      (x.1 + x.2) % 2 := by omega
  rw [hpar] at e1
  have hc := frame.coherentConstantV_eq
  obtain ⟨-, -, -, -, hTeq⟩ := frame.child_facts
  rw [hTeq] at hc
  unfold ChildFrame.tGrade
  have key : 4 * (harmonicGrid (x + (frame.child.num - frame.child.den, frame.child.num + frame.child.den)) -
      harmonicGrid x - (frame.child.num * x.1 - frame.child.den * x.2) - frame.coherentConstantV) = 0 := by
    linear_combination e1 - e0 - 2 * hc
  have := (mul_eq_zero.mp key).resolve_left (by norm_num)
  linarith

/-- The shift identity of `g = F − h₀` along `V`, for any packet `F` of the frame. -/
theorem g_add_V (frame : ChildFrame) {F : Field} (hP : frame.Packet F) (x : Site) :
    F (x + (frame.child.num - frame.child.den, frame.child.num + frame.child.den)) -
        harmonicGrid (x + (frame.child.num - frame.child.den, frame.child.num + frame.child.den)) =
      F x - harmonicGrid x := by
  rw [FLatticePaper.W1VShift.packet_V_step frame hP, harmonicGrid_add_V]
  ring

/-- `g` is invariant under all integer multiples of `V`. -/
theorem g_add_zsmul_V (frame : ChildFrame) {F : Field} (hP : frame.Packet F) (x : Site) (m : ℤ) :
    F (x + m • (frame.child.num - frame.child.den, frame.child.num + frame.child.den)) -
        harmonicGrid (x + m • (frame.child.num - frame.child.den, frame.child.num + frame.child.den)) =
      F x - harmonicGrid x := by
  induction m using Int.induction_on with
  | zero => simp
  | succ i ih =>
    have hs : x + ((i : ℤ) + 1) • (frame.child.num - frame.child.den, frame.child.num + frame.child.den) =
        (x + (i : ℤ) • (frame.child.num - frame.child.den, frame.child.num + frame.child.den)) +
          (frame.child.num - frame.child.den, frame.child.num + frame.child.den) := by
      rw [add_smul, one_smul, add_assoc]
    rw [hs, g_add_V frame hP, ih]
  | pred i ih =>
    have hs : x + (-(i : ℤ) - 1) • (frame.child.num - frame.child.den, frame.child.num + frame.child.den) +
        (frame.child.num - frame.child.den, frame.child.num + frame.child.den) =
        x + (-(i : ℤ)) • (frame.child.num - frame.child.den, frame.child.num + frame.child.den) := by
      rw [add_assoc, FLatticePaper.W1VShift.smul_add_self_site,
        show -(i : ℤ) - 1 + 1 = -(i : ℤ) by ring]
    have h2 := g_add_V frame hP (x + (-(i : ℤ) - 1) • (frame.child.num - frame.child.den, frame.child.num + frame.child.den))
    rw [hs, ih] at h2
    exact h2.symm

/-- The lattice step: if `N δ₁ = D δ₂`, `gcd(D, N) = 1`, `D ≠ 0`, `D + N` odd, and `δ₁ + δ₂` even, then `δ = 2m (D, N)`. -/
theorem lattice_line {N D δ1 δ2 : ℤ} (hcop : IsCoprime D N) (hD0 : D ≠ 0) (hodd : (D + N) % 2 = 1)
    (hrel : N * δ1 = D * δ2) (hpar : (δ1 + δ2) % 2 = 0) :
    ∃ m : ℤ, δ1 = 2 * m * D ∧ δ2 = 2 * m * N := by
  obtain ⟨a, b, hab⟩ := hcop
  obtain ⟨k, hk1⟩ : ∃ k, δ1 = D * k :=
    ⟨a * δ1 + b * δ2, by linear_combination (-δ1) * hab + b * hrel⟩
  have hk2 : δ2 = N * k := by
    have h : D * δ2 = D * (N * k) := by linear_combination (-1 : ℤ) * hrel + N * hk1
    exact mul_left_cancel₀ hD0 h
  have hsum : δ1 + δ2 = (D + N) * k := by rw [hk1, hk2]; ring
  have hE : Even ((D + N) * k) := Int.even_iff.mpr (by rw [← hsum]; exact hpar)
  rcases Int.even_mul.mp hE with h | h
  · exfalso
    have := Int.even_iff.mp h
    omega
  · obtain ⟨r, hr⟩ := h
    refine ⟨r, ?_, ?_⟩
    · rw [hk1, hr]; ring
    · rw [hk2, hr]; ring

/-- **The odd zero from one seed point** (task 74, odd_zero): if the quarter-turn field of `u` vanishes at one even point `z` of the
line `parentN x₁ − parentD x₂ = 1 − d`, it vanishes at every even point of that line. -/
theorem odd_zero_of_seed (u : Word) (hpk : (frameAt u).Packet (standardField u)) (z x : Site)
    (hz : EvenSite z) (hzl : parentN u * z.1 - parentD u * z.2 = 1 - (parentD u + parentN u))
    (hx : EvenSite x) (hxl : parentN u * x.1 - parentD u * x.2 = 1 - (parentD u + parentN u))
    (hz0 : quarterTurnField (standardField u) z = 0) :
    quarterTurnField (standardField u) x = 0 := by
  have he : ((frameAt u).child.num + (frameAt u).child.den) % 2 = 0 := (frameAt u).child_even
  obtain ⟨hnodd, hdodd⟩ := FLatticePaper.W1Exit.child_parity (frameAt u)
  have h1 : (frameAt u).child.den - (frameAt u).child.num = 2 * parentN u := by
    unfold parentN; omega
  have h2 : (frameAt u).child.num + (frameAt u).child.den = 2 * parentD u := by
    unfold parentD; omega
  have hnum : (frameAt u).child.num = parentD u - parentN u := by omega
  have hden : (frameAt u).child.den = parentD u + parentN u := by omega
  have hcop : IsCoprime (parentD u) (parentN u) := by
    obtain ⟨a, b, hab⟩ := (frameAt u).child_reduced
    rw [hnum, hden] at hab
    exact ⟨a + b, b - a, by linear_combination hab⟩
  have hD0 : parentD u ≠ 0 := by
    obtain ⟨hn0, -, -, hd3, -⟩ := (frameAt u).child_facts
    omega
  have hodd : (parentD u + parentN u) % 2 = 1 := by omega
  have hrel : parentN u * (x.1 - z.1) = parentD u * (x.2 - z.2) := by
    linear_combination hxl - hzl
  have hpar : ((x.1 - z.1) + (x.2 - z.2)) % 2 = 0 := by
    unfold EvenSite at hx hz
    omega
  obtain ⟨m, hm1, hm2⟩ := lattice_line hcop hD0 hodd hrel hpar
  have hshift : (-x.2, x.1 - 1) = (-z.2, z.1 - 1) +
      m • ((frameAt u).child.num - (frameAt u).child.den, (frameAt u).child.num + (frameAt u).child.den) := by
    ext
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      rw [show (frameAt u).child.num - (frameAt u).child.den = -2 * parentN u by omega]
      linear_combination (-1 : ℤ) * hm2
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      rw [h2]
      linear_combination hm1
  rw [FLatticePaper.W1ZeroStrip.quarterTurn_eq_sub] at hz0 ⊢
  rw [hshift]
  rw [g_add_zsmul_V (frameAt u) hpk (-z.2, z.1 - 1) m]
  exact hz0

end FLatticePaper.W1OddZero
