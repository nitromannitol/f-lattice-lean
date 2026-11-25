import FLatticePaper.Plane.Induction.Packet
import FLatticePaper.Plane.Induction.Potentials
import FLatticePaper.Plane.Induction.RepInputs

/-! Task 72 / Q28, the chain-level deck facts from the packet `hpk : frame.Packet F`: the grade and parity of the deck vectors
`combine i j`, the vector form of the modified deck, and the price drift `P(x + combine i j) = P x − i` (`price_kernel`, `price_transverse`).
The Laplacian is invariant under deck vectors (`ChildFrame.laplacian_add_lattice`). -/

namespace FLatticePaper.ChainDeck

open FLatticePaper FLatticePaper.Induction

/-- The modified kernel has the multiplicity `μ`, and the multiplicity is one when `n + d` is even (always, for a child frame). -/
theorem periodMultiplicity_eq_one (frame : ChildFrame) :
    Farey.Fraction.periodMultiplicity frame.child = 1 := by
  unfold Farey.Fraction.periodMultiplicity
  have hev : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  rw [if_pos hev]

/-- The deck vector in coordinates: `combine i j = (i d + j (n − d), i n + j (n + d))`. -/
theorem combine_eq_vec (frame : ChildFrame) (i j : ℤ) :
    frame.child.modifiedDeck.combine i j =
      (i * frame.child.den + j * (frame.child.num - frame.child.den),
        i * frame.child.num + j * (frame.child.num + frame.child.den)) := by
  unfold Farey.PeriodDeck.combine
  simp only [Farey.Fraction.modifiedDeck, Farey.Fraction.unmodifiedDeck, periodMultiplicity_eq_one frame, one_mul]

/-- Deck vectors have even coordinate sum. -/
theorem combine_even (frame : ChildFrame) (i j : ℤ) :
    ((frame.child.modifiedDeck.combine i j).1 + (frame.child.modifiedDeck.combine i j).2) % 2 = 0 := by
  rw [combine_eq_vec]
  have he : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  obtain ⟨e, hd⟩ : ∃ e, frame.child.den + frame.child.num = 2 * e := ⟨(frame.child.den + frame.child.num) / 2, by omega⟩
  have key : (i * frame.child.den + j * (frame.child.num - frame.child.den)) +
      (i * frame.child.num + j * (frame.child.num + frame.child.den)) =
      2 * (i * e + j * frame.child.num) := by
    linear_combination i * hd
  dsimp only
  rw [key]
  exact Int.mul_emod_right 2 _

/-- The price drift of a kernel multiple: `P(x + n K) = P x − n`. -/
theorem price_kernel_mul (frame : ChildFrame) {F : Field} (hP : frame.Packet F) (n : ℤ) (x : Site) :
    frame.price F (x + n • frame.child.modifiedDeck.kernel) = frame.price F x - n := by
  induction n using Int.induction_on generalizing x with
  | zero => simp
  | succ k ih =>
    have e : x + (↑k + 1 : ℤ) • frame.child.modifiedDeck.kernel =
        (x + (k : ℤ) • frame.child.modifiedDeck.kernel) + frame.child.modifiedDeck.kernel := by
      rw [add_smul, one_smul, add_assoc]
    rw [e, frame.price_kernel F hP.periods, ih x]
    ring
  | pred k ih =>
    have e : x + (-(k : ℤ) - 1) • frame.child.modifiedDeck.kernel =
        (x + (-(k : ℤ)) • frame.child.modifiedDeck.kernel) - frame.child.modifiedDeck.kernel := by
      rw [sub_smul, one_smul, add_sub_assoc]
    have h1 := frame.price_kernel F hP.periods (x + (-(k : ℤ) - 1) • frame.child.modifiedDeck.kernel)
    have e2 : x + (-(k : ℤ) - 1) • frame.child.modifiedDeck.kernel + frame.child.modifiedDeck.kernel =
        x + (-(k : ℤ)) • frame.child.modifiedDeck.kernel := by
      rw [sub_smul, one_smul]
      abel
    rw [e2] at h1
    rw [ih x] at h1
    linarith

/-- The price is invariant along the transverse deck vector. -/
theorem price_transverse_mul (frame : ChildFrame) {F : Field} (hP : frame.Packet F) (m : ℤ) (x : Site) :
    frame.price F (x + m • frame.child.modifiedDeck.transverse) = frame.price F x := by
  induction m using Int.induction_on generalizing x with
  | zero => simp
  | succ k ih =>
    have e : x + (↑k + 1 : ℤ) • frame.child.modifiedDeck.transverse =
        (x + (k : ℤ) • frame.child.modifiedDeck.transverse) + frame.child.modifiedDeck.transverse := by
      rw [add_smul, one_smul, add_assoc]
    rw [e, frame.price_transverse F hP.periods, ih x]
  | pred k ih =>
    have e2 : x + (-(k : ℤ) - 1) • frame.child.modifiedDeck.transverse + frame.child.modifiedDeck.transverse =
        x + (-(k : ℤ)) • frame.child.modifiedDeck.transverse := by
      rw [sub_smul, one_smul]
      abel
    have h1 := frame.price_transverse F hP.periods (x + (-(k : ℤ) - 1) • frame.child.modifiedDeck.transverse)
    rw [e2, ih x] at h1
    exact h1.symm

/-- **The price drift along a deck vector:** `P(x + combine i j) = P x − i`. -/
theorem price_combine (frame : ChildFrame) {F : Field} (hP : frame.Packet F) (i j : ℤ) (x : Site) :
    frame.price F (x + frame.child.modifiedDeck.combine i j) = frame.price F x - i := by
  have e : frame.child.modifiedDeck.combine i j =
      i • frame.child.modifiedDeck.kernel + j • frame.child.modifiedDeck.transverse := by
    unfold Farey.PeriodDeck.combine
    ext <;> simp
  rw [e, ← add_assoc, price_transverse_mul frame hP j, price_kernel_mul frame hP i x]

/-- The price drift along the negated deck vector: `P(x − combine i j) = P x + i`. -/
theorem price_sub_combine (frame : ChildFrame) {F : Field} (hP : frame.Packet F) (i j : ℤ) (x : Site) :
    frame.price F (x - frame.child.modifiedDeck.combine i j) = frame.price F x + i := by
  have h := price_combine frame hP (-i) (-j) x
  have hc : frame.child.modifiedDeck.combine (-i) (-j) = -frame.child.modifiedDeck.combine i j := by
    unfold Farey.PeriodDeck.combine
    ext <;> simp <;> ring
  rw [hc, ← sub_eq_add_neg] at h
  linarith

/-- Combinations of deck vectors are additive: `combine (i − k + p) (j − l + q) = combine i j − combine k l + combine p q`. -/
theorem combine_lin (frame : ChildFrame) (i j k l p q : ℤ) :
    frame.child.modifiedDeck.combine (i - k + p) (j - l + q) =
      frame.child.modifiedDeck.combine i j - frame.child.modifiedDeck.combine k l +
        frame.child.modifiedDeck.combine p q := by
  unfold Farey.PeriodDeck.combine
  ext <;> simp <;> ring

/-- Deck vectors subtract coordinatewise: `combine (i − k) (j − l) = combine i j − combine k l`. -/
theorem combine_sub_eq (frame : ChildFrame) (i j k l : ℤ) :
    frame.child.modifiedDeck.combine (i - k) (j - l) =
      frame.child.modifiedDeck.combine i j - frame.child.modifiedDeck.combine k l := by
  unfold Farey.PeriodDeck.combine
  ext <;> simp <;> ring

/-- The two inputs of a centre sum to twice the centre. -/
theorem incomingNeg_add_incomingPos (z : Site) : incomingNeg z + incomingPos z = z + z := by
  unfold incomingNeg incomingPos
  split_ifs <;> ext <;> simp

/-- The other input of a centre: distinct inputs `u`, `v` of `z` satisfy `v = z + z − u`. -/
theorem other_input (z u v : Site) (hu : u = incomingNeg z ∨ u = incomingPos z)
    (hv : v = incomingNeg z ∨ v = incomingPos z) (hne : v ≠ u) : v = z + z - u := by
  have hsum := incomingNeg_add_incomingPos z
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact absurd rfl hne
  · rw [← hsum]; abel
  · rw [← hsum]; abel
  · exact absurd rfl hne

end FLatticePaper.ChainDeck
