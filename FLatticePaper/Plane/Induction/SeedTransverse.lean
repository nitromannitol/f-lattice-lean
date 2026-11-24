import FLatticePaper.Plane.Induction.Packet
import FLatticePaper.Plane.Induction.Bands
import FLatticePaper.Plane.Induction.StarClassify
import FLatticePaper.Plane.Induction.PriceDeck

/-!
# The odd seed line by the transverse reduction (STRONG_PRICE / NO_ODD_SLIP §2)

For a standard field `F` with a packet, the difference `D = F − harmonicGrid` is invariant under the transverse vector
`V = (n − d, n + d)` of the child deck: the packet gives `F(z + V) = F z + tGrade z + coherentConstantV`, and
`harmonicGrid (z + V) = harmonicGrid z + tGrade z − (T + L)/2` with `coherentConstantV = −(T + L)/2`. The odd sites of the seed line
`sGrade = 2 − 3d + n` form a single transverse class: `z0 + Z·V` (the sGrade-zero lattice is `Z·(−(d−n)/2, (d+n)/2)`, coprime since
`n/d` is reduced, and `V` is twice that generator, with odd coordinate sum `n`). Hence the seed holds on the whole odd seed line once it
holds at one odd seed site `z0` (`seed_of_check`).
-/

namespace FLatticePaper.Induction.SeedTransverse

open Farey FLatticePaper FLatticePaper.Induction

section Transverse

variable (frame : ChildFrame)

theorem div4_shift (A B K : ℤ) (hK : K % 2 = 0) : (A + 4 * B - 2 * K) / 4 = A / 4 + B - K / 2 := by
  omega

theorem const_eq (L T : ℤ) (hL : L % 2 = 0) (hT : T % 2 = 0) : (L - T) / 2 - (-T + L) + -T = -((T + L) / 2) := by
  omega

/-- The harmonic grid along the transverse vector: `H(z + V) = H z + tGrade z − (T + L)/2`. -/
theorem harmonicGrid_transverse (hpar : (frame.child.num + frame.child.den) % 2 = 0)
    (hTL : (frame.child.periodDenominator + (frame.child.den + frame.child.num)) % 2 = 0) (z : Site) :
    harmonicGrid (z + frame.child.modifiedDeck.transverse) =
      harmonicGrid z + frame.tGrade z - (frame.child.periodDenominator + (frame.child.den + frame.child.num)) / 2 := by
  unfold harmonicGrid
  rw [StrongUnitPrice.transverse_eq frame]
  simp only [Prod.fst_add, Prod.snd_add]
  have hp : (z.1 + (frame.child.num - frame.child.den) + (z.2 + (frame.child.num + frame.child.den))) % 2
      = (z.1 + z.2) % 2 := by omega
  rw [hp]
  have e : (z.1 + (frame.child.num - frame.child.den)) ^ 2
      + 2 * (z.1 + (frame.child.num - frame.child.den)) * (z.2 + (frame.child.num + frame.child.den))
      - (z.2 + (frame.child.num + frame.child.den)) ^ 2 - 2 * (z.2 + (frame.child.num + frame.child.den))
      - (z.1 + z.2) % 2
      = (z.1 ^ 2 + 2 * z.1 * z.2 - z.2 ^ 2 - 2 * z.2 - (z.1 + z.2) % 2)
        + 4 * frame.tGrade z
        - 2 * (frame.child.periodDenominator + (frame.child.den + frame.child.num)) := by
    unfold ChildFrame.tGrade Fraction.periodDenominator
    ring
  rw [e]
  exact div4_shift _ _ _ hTL

/-- The coherent transverse constant is `−(T + L)/2`, the harmonic constant. -/
theorem coherentConstantV_eq (hL : (frame.child.den + frame.child.num) % 2 = 0)
    (hT : frame.child.periodDenominator % 2 = 0) :
    frame.coherentConstantV = -((frame.child.periodDenominator + (frame.child.den + frame.child.num)) / 2) := by
  have hc : frame.tGrade frame.centre = -frame.child.periodDenominator + (frame.child.den + frame.child.num) := by
    unfold ChildFrame.centre ChildFrame.tGrade
    rw [StrongUnitPrice.kernel_eq frame (by omega), StrongUnitPrice.transverse_eq frame]
    simp only [Prod.fst_add, Prod.snd_add]
    unfold Fraction.periodDenominator
    ring
  have hv : frame.tGrade frame.child.modifiedDeck.transverse = -frame.child.periodDenominator := by
    unfold ChildFrame.tGrade Fraction.periodDenominator
    rw [StrongUnitPrice.transverse_eq frame]
    ring
  unfold ChildFrame.coherentConstantV ChildFrame.symmetryConstant
  rw [hc, hv]
  exact const_eq _ _ hL hT

/-- The packet's transverse law for `F − harmonicGrid`: the difference is invariant under the transverse vector. -/
theorem diff_transverse (F : Field) (hP : frame.Packet F)
    (hpar : (frame.child.num + frame.child.den) % 2 = 0)
    (hTL : (frame.child.periodDenominator + (frame.child.den + frame.child.num)) % 2 = 0)
    (hL : (frame.child.den + frame.child.num) % 2 = 0) (hT : frame.child.periodDenominator % 2 = 0) (z : Site) :
    F (z + frame.child.modifiedDeck.transverse) - harmonicGrid (z + frame.child.modifiedDeck.transverse) =
      F z - harmonicGrid z := by
  obtain ⟨-, hV⟩ := hP.periods
  have h1 := hV z
  have htg : Fraction.transverseGrade frame.child z = -frame.tGrade z := by
    unfold Fraction.transverseGrade ChildFrame.tGrade
    ring
  rw [htg, coherentConstantV_eq frame hL hT] at h1
  rw [h1, harmonicGrid_transverse frame hpar hTL z]
  ring

/-- Iterates of the transverse invariance: the difference is invariant under integer multiples of `V`. -/
theorem diff_transverse_iter (F : Field) (hP : frame.Packet F)
    (hpar : (frame.child.num + frame.child.den) % 2 = 0)
    (hTL : (frame.child.periodDenominator + (frame.child.den + frame.child.num)) % 2 = 0)
    (hL : (frame.child.den + frame.child.num) % 2 = 0) (hT : frame.child.periodDenominator % 2 = 0)
    (k : ℤ) (z : Site) :
    F (z + (k * frame.child.modifiedDeck.transverse.1, k * frame.child.modifiedDeck.transverse.2)) -
        harmonicGrid (z + (k * frame.child.modifiedDeck.transverse.1, k * frame.child.modifiedDeck.transverse.2)) =
      F z - harmonicGrid z := by
  induction k using Int.induction_on with
  | zero =>
    have e : z + ((0 : ℤ) * frame.child.modifiedDeck.transverse.1, (0 : ℤ) * frame.child.modifiedDeck.transverse.2) = z := by
      ext <;> simp
    rw [e]
  | succ i ih =>
    have h : z + (((i : ℤ) + 1) * frame.child.modifiedDeck.transverse.1,
        ((i : ℤ) + 1) * frame.child.modifiedDeck.transverse.2) =
        (z + ((i : ℤ) * frame.child.modifiedDeck.transverse.1, (i : ℤ) * frame.child.modifiedDeck.transverse.2)) +
          frame.child.modifiedDeck.transverse := by
      ext <;> simp <;> ring
    rw [h, diff_transverse frame F hP hpar hTL hL hT, ih]
  | pred i ih =>
    have h := diff_transverse frame F hP hpar hTL hL hT
      (z + ((-(i : ℤ) - 1) * frame.child.modifiedDeck.transverse.1, (-(i : ℤ) - 1) * frame.child.modifiedDeck.transverse.2))
    have e : z + ((-(i : ℤ) - 1) * frame.child.modifiedDeck.transverse.1,
        (-(i : ℤ) - 1) * frame.child.modifiedDeck.transverse.2) + frame.child.modifiedDeck.transverse =
        z + (-(i : ℤ) * frame.child.modifiedDeck.transverse.1, -(i : ℤ) * frame.child.modifiedDeck.transverse.2) := by
      ext <;> simp <;> ring
    rw [e] at h
    linarith

end Transverse

section Lattice

/-- Two odd sites of the seed line differ by an integer multiple of the transverse vector `V = (n − d, n + d)`. -/
theorem odd_seed_class (frame : ChildFrame) (a : ℤ) (ha : frame.child.num = 2 * a + 1)
    (z0 z : Site) (hz0 : frame.sGrade z0 = 2 - 3 * frame.child.den + frame.child.num)
    (hz : frame.sGrade z = 2 - 3 * frame.child.den + frame.child.num) (hz0o : ¬ EvenSite z0) (hzo : ¬ EvenSite z) :
    ∃ k : ℤ, z = z0 + (k * frame.child.modifiedDeck.transverse.1, k * frame.child.modifiedDeck.transverse.2) := by
  have hcop : IsCoprime frame.child.den frame.child.num :=
    (frame.child_reduced : IsCoprime frame.child.num frame.child.den).symm
  obtain ⟨-, -, -, hd3, -⟩ := frame.child_facts
  have hdpos : (0 : ℤ) < frame.child.den := by omega
  set w1 := z.1 - z0.1 with hw1
  set w2 := z.2 - z0.2 with hw2
  -- the difference has sGrade zero: den (w1 + w2) + num (w1 − w2) = 0
  have hs0 : frame.child.den * (w1 + w2) + frame.child.num * (w1 - w2) = 0 := by
    have e1 : frame.sGrade z - frame.sGrade z0 =
        frame.child.den * (w1 + w2) + frame.child.num * (w1 - w2) := by
      unfold ChildFrame.sGrade
      rw [hw1, hw2]
      ring
    linarith
  -- den divides num · (w1 − w2), hence den divides w1 − w2
  have hdvd : frame.child.den ∣ (w1 - w2) * frame.child.num := ⟨-(w1 + w2), by linear_combination hs0⟩
  obtain ⟨k0, hk0⟩ := hcop.dvd_of_dvd_mul_right hdvd
  -- hk0 : w1 − w2 = den * k0, and then w1 + w2 = −num * k0
  have hsum : w1 + w2 = -(frame.child.num * k0) := by
    have hm : frame.child.den * (w1 + w2 + frame.child.num * k0) = 0 := by
      linear_combination hs0 - frame.child.num * hk0
    rcases mul_eq_zero.mp hm with h | h
    · omega
    · linarith
  -- the sum is even (both sites are odd), and the numerator is odd, so k0 is even
  have hpar2 : (w1 + w2) % 2 = 0 := by
    unfold EvenSite at hz0o hzo
    omega
  have hk0e : k0 % 2 = 0 := by
    have hnk : frame.child.num * k0 = 2 * (a * k0) + k0 := by
      rw [ha]
      ring
    rw [hnk] at hsum
    omega
  obtain ⟨j, hj⟩ : ∃ j, k0 = 2 * j := ⟨k0 / 2, by omega⟩
  rw [hj] at hk0 hsum
  have e1 : z.1 - z0.1 = -j * (frame.child.num - frame.child.den) := by
    have h2 : 2 * (z.1 - z0.1) = 2 * (-j * (frame.child.num - frame.child.den)) := by
      linear_combination hk0 + hsum
    exact mul_left_cancel₀ two_ne_zero h2
  have e2 : z.2 - z0.2 = -j * (frame.child.num + frame.child.den) := by
    have h2 : 2 * (z.2 - z0.2) = 2 * (-j * (frame.child.num + frame.child.den)) := by
      linear_combination hsum - hk0
    exact mul_left_cancel₀ two_ne_zero h2
  refine ⟨-j, ?_⟩
  rw [StrongUnitPrice.transverse_eq frame]
  ext
  · simp only [Prod.fst_add]
    linarith
  · simp only [Prod.snd_add]
    linarith

/-- **The odd seed line by one check.** If `F` equals the harmonic grid at one odd site `z0` of the seed line, then it does on
every odd site of the seed line: the difference is invariant under the transverse vector and the odd seed line is one transverse class. -/
theorem seed_of_check (frame : ChildFrame) (F : Field) (hP : frame.Packet F) (a : ℤ) (ha : frame.child.num = 2 * a + 1)
    (z0 : Site) (hz0 : frame.sGrade z0 = 2 - 3 * frame.child.den + frame.child.num)
    (hz0o : ¬ EvenSite z0) (hcheck : F z0 = harmonicGrid z0)
    (hpar : (frame.child.num + frame.child.den) % 2 = 0)
    (hTL : (frame.child.periodDenominator + (frame.child.den + frame.child.num)) % 2 = 0)
    (hL : (frame.child.den + frame.child.num) % 2 = 0) (hT : frame.child.periodDenominator % 2 = 0) :
    ∀ w : Site, ¬ EvenSite w → frame.sGrade w = 2 - 3 * frame.child.den + frame.child.num →
      F w = harmonicGrid w := by
  intro w hw hsw
  obtain ⟨k, hk⟩ := odd_seed_class frame a ha z0 w hz0 hsw hz0o hw
  have hd := diff_transverse_iter frame F hP hpar hTL hL hT k z0
  rw [← hk] at hd
  have : F w - harmonicGrid w = 0 := by
    rw [hd, hcheck, sub_self]
  linarith


end Lattice

end FLatticePaper.Induction.SeedTransverse
