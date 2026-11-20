import FLatticePaper.Farey.MatrixLattice
import FLatticePaper.Farey.Rotation

namespace FLatticePaper.Farey

/-- A creator of an odd donor uses digit one or two. The subsequent threes
retain that donor and advance the even parent. -/
def donorWord (origin : Word) (replaceEven : Bool) (steps : ℕ) : Word :=
  origin ++ [if replaceEven then .one else .two] ++ List.replicate steps .three

theorem Parents.walk_threes (parents : Parents) (steps : ℕ) :
    parents.walk (List.replicate steps .three) =
      ⟨parents.odd, parents.combine (2 * steps) 1⟩ := by
  induction steps with
  | zero => cases parents; simp [Parents.walk, Parents.combine]
  | succ steps ih =>
    rw [List.replicate_succ', Parents.walk_append, ih]
    change (Parents.mk _ _).step .three = _
    simp only [Parents.step, Parents.current]
    congr 1
    apply Fraction.ext <;> simp only [Parents.combine, Int.natCast_succ, one_mul] <;> ring

theorem parentsAt_donorWord_odd (origin : Word) (replaceEven : Bool) (steps : ℕ) :
    (parentsAt (donorWord origin replaceEven steps)).odd = (parentsAt origin).current .odd := by
  unfold donorWord parentsAt
  rw [Parents.walk_append, Parents.walk_threes, Parents.walk_append]
  cases replaceEven <;> rfl

/-- The consumed even parent, in each of the two actual creator roles. -/
theorem parentsAt_donorWord_even (origin : Word) (replaceEven : Bool) (steps : ℕ) :
    let parents := parentsAt origin
    let donor := parents.current .odd
    let sign : ℤ := if replaceEven then -1 else 1
    let advance : ℤ := (steps : ℤ) + if replaceEven then 1 else 0
    (parentsAt (donorWord origin replaceEven steps)).even =
      ⟨2 * advance * donor.num + sign * parents.even.num,
        2 * advance * donor.den + sign * parents.even.den⟩ := by
  dsimp only
  unfold donorWord parentsAt
  rw [Parents.walk_append, Parents.walk_threes]
  cases replaceEven <;>
    apply Fraction.ext <;> simp [Parents.walk, Parents.step, Parents.current, Parents.combine] <;> ring

theorem parentsAt_donorWord_det (origin : Word) (replaceEven : Bool) (steps : ℕ) :
    let old := parentsAt origin
    let current := parentsAt (donorWord origin replaceEven steps)
    current.odd.det current.even = (if replaceEven then -1 else 1) * old.odd.det old.even := by
  dsimp only
  rw [parentsAt_donorWord_odd, parentsAt_donorWord_even]
  cases replaceEven <;> simp [Parents.current, Parents.combine, Fraction.det] <;> ring

/-- Twice the change in the rotated even-parent vector removes division by
two from the earlier chain's signed gradient identity. -/
theorem earlierChain_signed_gradient (origin : Word) (replaceEven : Bool) (steps : ℕ) :
    let old := parentsAt origin
    let current := parentsAt (donorWord origin replaceEven steps)
    let earlier := parentsAt (origin.map Digit.swapTwoThree)
    let orientation := current.odd.det current.even
    let oldOrientation := old.odd.det old.even
    let advance : ℤ := (steps : ℤ) + if replaceEven then 1 else 0
    (orientation * (current.even.den + current.even.num) - 2 * oldOrientation * earlier.odd.den =
        2 * orientation * advance * (earlier.current .even).den) ∧
    (orientation * (current.even.den - current.even.num) - 2 * oldOrientation * earlier.odd.num =
        2 * orientation * advance * (earlier.current .even).num) := by
  dsimp only
  have hrot := rotate_parentsAt origin
  have hparent := (congrArg Parents.odd hrot).symm
  have hdonor := (congrArg (fun parents => parents.current .even) hrot).symm.trans
    (parentsAt_valid origin).rotate_current_odd.symm
  change (parentsAt (origin.map Digit.swapTwoThree)).odd = (parentsAt origin).even.rotate at hparent
  rw [Fraction.rotate_of_even (parentsAt_valid origin).even_parity] at hparent
  rw [Fraction.rotate_of_odd (parentsAt_valid origin).current_odd_parity] at hdonor
  have hp : ((parentsAt origin).even.num + (parentsAt origin).even.den) % 2 = 0 :=
    (parentsAt_valid origin).even_parity
  rw [hparent, hdonor, parentsAt_donorWord_det, parentsAt_donorWord_even]
  have hden : 2 * (((parentsAt origin).even.den + (parentsAt origin).even.num) / 2) =
      (parentsAt origin).even.den + (parentsAt origin).even.num := by omega
  have hnum : 2 * (((parentsAt origin).even.den - (parentsAt origin).even.num) / 2) =
      (parentsAt origin).even.den - (parentsAt origin).even.num := by omega
  cases replaceEven <;> constructor <;> dsimp <;>
    first | linear_combination -((parentsAt origin).odd.det (parentsAt origin).even) * hden
          | linear_combination -((parentsAt origin).odd.det (parentsAt origin).even) * hnum

/-- Pulling back the negative of `Vq + ε Uq` through the quarter-turn
gives this physical displacement in the earlier field's coordinates. -/
def rotatedTransverseShift (evenParent : Fraction) (orientation : ℤ) : Site :=
  (evenParent.num + evenParent.den + orientation * evenParent.num,
    -(evenParent.num - evenParent.den + orientation * evenParent.den))

/-- The earlier chain uses `η σ' - v'` in its actual rotated frame. -/
def earlierChainShift (oddParent : Fraction) (oldOrientation orientation : ℤ) : Site :=
  (2 * orientation * oldOrientation * oddParent.den - oldOrientation * (oddParent.num - oddParent.den),
    2 * orientation * oldOrientation * oddParent.num - oldOrientation * (oddParent.num + oddParent.den))

/-- The earlier even field is the rotated birth of the actual odd donor. Its
two shifts differ by a period whose transverse index includes the creator's
extra step precisely when digit one also replaced the even parent. -/
theorem earlierChain_shift_eq (origin : Word) (replaceEven : Bool) (steps : ℕ) :
    let old := parentsAt origin
    let current := parentsAt (donorWord origin replaceEven steps)
    let earlier := parentsAt (origin.map Digit.swapTwoThree)
    let rotatedDonor := earlier.current .even
    let orientation := current.odd.det current.even
    let oldOrientation := old.odd.det old.even
    let advance : ℤ := (steps : ℤ) + if replaceEven then 1 else 0
    ∃ kernel : ℤ,
      rotatedTransverseShift current.even orientation =
        earlierChainShift earlier.odd oldOrientation orientation +
          rotatedDonor.unmodifiedDeck.combine kernel (-orientation * advance) := by
  let current := parentsAt (donorWord origin replaceEven steps)
  let old := parentsAt origin
  let donor := old.current .odd
  let earlier := parentsAt (origin.map Digit.swapTwoThree)
  let rotatedDonor := earlier.current .even
  let orientation := current.odd.det current.even
  let oldOrientation := (parentsAt origin).odd.det (parentsAt origin).even
  let advance : ℤ := (steps : ℤ) + if replaceEven then 1 else 0
  let h := rotatedTransverseShift current.even orientation
  let w := earlierChainShift earlier.odd oldOrientation orientation
  let v := rotatedDonor.unmodifiedDeck.combine 0 (-orientation * advance)
  have hrot := rotate_parentsAt origin
  have hparent : earlier.odd = (parentsAt origin).even.rotate :=
    (congrArg Parents.odd hrot).symm
  have hdonor : rotatedDonor = ((parentsAt origin).current .odd).rotate :=
    (congrArg (fun parents => parents.current .even) hrot).symm.trans
      (parentsAt_valid origin).rotate_current_odd.symm
  rw [Fraction.rotate_of_even (parentsAt_valid origin).even_parity] at hparent
  rw [Fraction.rotate_of_odd (parentsAt_valid origin).current_odd_parity] at hdonor
  have hnum : 2 * earlier.odd.num = (parentsAt origin).even.den - (parentsAt origin).even.num := by
    rw [hparent]
    have hp : ((parentsAt origin).even.num + (parentsAt origin).even.den) % 2 = 0 :=
      (parentsAt_valid origin).even_parity
    dsimp
    omega
  have hden : 2 * earlier.odd.den = (parentsAt origin).even.den + (parentsAt origin).even.num := by
    rw [hparent]
    have hp : ((parentsAt origin).even.num + (parentsAt origin).even.den) % 2 = 0 :=
      (parentsAt_valid origin).even_parity
    dsimp
    omega
  have hrotDet : earlier.odd.det rotatedDonor = oldOrientation := by
    rw [hdonor]
    apply (mul_right_inj' (show (2 : ℤ) ≠ 0 by decide)).mp
    change 2 * (earlier.odd.num * (donor.den + donor.num) - (donor.den - donor.num) * earlier.odd.den) =
      2 * oldOrientation
    have hdet : donor.det old.even = oldOrientation := by
      simp only [donor, old, oldOrientation, Parents.current, Parents.combine, Fraction.det, one_mul]
      ring
    change donor.num * old.even.den - old.even.num * donor.den = oldOrientation at hdet
    linear_combination (donor.den + donor.num) * hnum - (donor.den - donor.num) * hden + 2 * hdet
  have hgrade : rotatedDonor.transverseGrade (h - w) = rotatedDonor.periodDenominator * (-orientation * advance) := by
    have hodd : current.odd = (parentsAt origin).current .odd := parentsAt_donorWord_odd ..
    have hdet : orientation = ((parentsAt origin).current .odd).det current.even := by
      change current.odd.det current.even = _
      rw [hodd]
    have heven := parentsAt_donorWord_even origin replaceEven steps
    change current.even = _ at heven
    have hsign := parentsAt_donorWord_det origin replaceEven steps
    change orientation = _ at hsign
    have hold : oldOrientation = 1 ∨ oldOrientation = -1 := (parentsAt_valid origin).unit_det
    let price (q : Fraction) := donor.den * (q.den + q.num) + donor.num * (q.den - q.num)
    have hh : rotatedDonor.transverseGrade h = 2 * orientation - orientation * price current.even := by
      rw [hdonor]
      change orientation = donor.num * current.even.den - current.even.num * donor.den at hdet
      dsimp [Fraction.transverseGrade, h, rotatedTransverseShift, price]
      linear_combination -2 * hdet
    have hw : rotatedDonor.transverseGrade w = 2 * orientation - oldOrientation * price old.even := by
      rw [hdonor]
      rw [hdonor] at hrotDet
      change earlier.odd.num * (donor.den + donor.num) - (donor.den - donor.num) * earlier.odd.den =
        oldOrientation at hrotDet
      have hsq : oldOrientation * oldOrientation = 1 := by rcases hold with hp | hp <;> rw [hp] <;> decide
      dsimp [w, earlierChainShift, Fraction.transverseGrade, price]
      linear_combination 2 * orientation * oldOrientation * hrotDet + 2 * orientation * hsq -
        oldOrientation * donor.den * hden - oldOrientation * donor.num * hnum
    rw [Fraction.transverseGrade_sub, hh, hw, hdonor, heven]
    change orientation = (if replaceEven then -1 else 1) * oldOrientation at hsign
    rw [hsign]
    cases replaceEven <;> dsimp [price, advance, Fraction.periodDenominator] <;> ring
  have hkernel : rotatedDonor.transverseGrade (h - w - v) = 0 := by
    rw [Fraction.transverseGrade_sub, hgrade]
    dsimp only [v]
    rw [Fraction.transverseGrade_combine, sub_self]
  obtain ⟨kernel, hk⟩ := Fraction.exists_kernel_multiple
    ((parentsAt_valid (origin.map Digit.swapTwoThree)).current_reduced .even) hkernel
  change h - w - v = rotatedDonor.unmodifiedDeck.combine kernel 0 at hk
  refine ⟨kernel, ?_⟩
  change h = w + rotatedDonor.unmodifiedDeck.combine kernel (-orientation * advance)
  apply Prod.ext
  · have hp := congrArg Prod.fst hk
    simp only [v, PeriodDeck.combine, Prod.fst_sub, Prod.fst_add, zero_mul, zero_add, add_zero] at hp ⊢
    omega
  · have hp := congrArg Prod.snd hk
    simp only [v, PeriodDeck.combine, Prod.snd_sub, Prod.snd_add, zero_mul, zero_add, add_zero] at hp ⊢
    omega

/-- The earlier displacement is a difference of actual modified-deck
period representatives. The rotated donor is even so its kernel is primitive. -/
theorem earlierChain_shift_eq_modified (origin : Word) (replaceEven : Bool) (steps : ℕ) :
    let old := parentsAt origin
    let current := parentsAt (donorWord origin replaceEven steps)
    let earlier := parentsAt (origin.map Digit.swapTwoThree)
    let rotatedDonor := earlier.current .even
    let orientation := current.odd.det current.even
    let oldOrientation := old.odd.det old.even
    let advance : ℤ := (steps : ℤ) + if replaceEven then 1 else 0
    ∃ kernel : ℤ,
      rotatedTransverseShift current.even orientation =
        earlierChainShift earlier.odd oldOrientation orientation +
          rotatedDonor.modifiedDeck.combine kernel (-orientation * advance) := by
  have hp : ((parentsAt (origin.map Digit.swapTwoThree)).current .even).Even :=
    (parentsAt_valid (origin.map Digit.swapTwoThree)).current_even_parity
  dsimp only
  obtain ⟨kernel, hk⟩ := earlierChain_shift_eq origin replaceEven steps
  refine ⟨kernel, ?_⟩
  change (_ + _) % 2 = 0 at hp
  rw [Fraction.modifiedDeck_combine, Fraction.periodMultiplicity, if_pos hp, one_mul]
  exact hk

end FLatticePaper.Farey
