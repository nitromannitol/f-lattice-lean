import FLatticePaper.Farey.Birth

namespace FLatticePaper.Farey

/-- The parity-reduced arithmetic rotation of a fraction in the unit interval. -/
def Fraction.rotate (fraction : Fraction) : Fraction :=
  if (fraction.num + fraction.den) % 2 = 1 then
    ⟨fraction.den - fraction.num, fraction.den + fraction.num⟩
  else
    ⟨(fraction.den - fraction.num) / 2, (fraction.den + fraction.num) / 2⟩

theorem Fraction.rotate_of_odd {fraction : Fraction} (h : fraction.Odd) :
    fraction.rotate = ⟨fraction.den - fraction.num, fraction.den + fraction.num⟩ := if_pos h

theorem Fraction.rotate_of_even {fraction : Fraction} (h : fraction.Even) :
    fraction.rotate = ⟨(fraction.den - fraction.num) / 2, (fraction.den + fraction.num) / 2⟩ := by
  have heq : (fraction.num + fraction.den) % 2 = 0 := h
  exact if_neg (by omega)

theorem Fraction.rotate_even_of_odd {fraction : Fraction} (h : fraction.Odd) :
    fraction.rotate.Even := by
  rw [rotate_of_odd h]
  unfold Even
  dsimp
  omega

theorem Fraction.rotate_odd_of_even {fraction : Fraction} (heven : fraction.Even)
    (hreduced : fraction.Reduced) : fraction.rotate.Odd := by
  have hparity : (fraction.num + fraction.den) % 2 = 0 := heven
  have hden : fraction.den % 2 = 1 := by
    by_contra! h
    have hdn : fraction.den = 2 * (fraction.den / 2) := by omega
    have hnm : fraction.num = 2 * (fraction.num / 2) := by omega
    obtain ⟨numCoeff, denCoeff, hbezout⟩ := hreduced
    have hdvd : (2 : ℤ) ∣ 1 := by
      refine ⟨numCoeff * (fraction.num / 2) + denCoeff * (fraction.den / 2), ?_⟩
      conv_lhs => rw [← hbezout, mul_comm numCoeff, mul_comm denCoeff]
      calc
        _ = (2 * (fraction.num / 2)) * numCoeff + (2 * (fraction.den / 2)) * denCoeff := by
          congr 1
          · exact congrArg (· * numCoeff) hnm
          · exact congrArg (· * denCoeff) hdn
        _ = _ := by ring
    omega
  rw [rotate_of_even heven]
  unfold Odd
  dsimp
  omega

def Parents.rotate (parents : Parents) : Parents := ⟨parents.even.rotate, parents.odd.rotate⟩

def Digit.swapTwoThree : Digit → Digit
  | .one => .one
  | .two => .three
  | .three => .two

@[simp]
theorem Digit.swapTwoThree_swapTwoThree (digit : Digit) :
    digit.swapTwoThree.swapTwoThree = digit := by cases digit <;> rfl

theorem Parents.ValidFrame.rotate_current_even {parents : Parents} (h : parents.ValidFrame) :
    (parents.current .even).rotate = parents.rotate.current .odd := by
  rw [Fraction.rotate_of_even h.current_even_parity]
  have hparity : (parents.even.num + parents.even.den) % 2 = 0 := h.even_parity
  simp only [Parents.rotate, Fraction.rotate_of_even h.even_parity,
    Fraction.rotate_of_odd h.odd_parity, Parents.current, Parents.combine]
  apply Fraction.ext <;> dsimp <;> omega

theorem Parents.ValidFrame.rotate_current_odd {parents : Parents} (h : parents.ValidFrame) :
    (parents.current .odd).rotate = parents.rotate.current .even := by
  rw [Fraction.rotate_of_odd h.current_odd_parity]
  have hparity : (parents.even.num + parents.even.den) % 2 = 0 := h.even_parity
  simp only [Parents.rotate, Fraction.rotate_of_even h.even_parity,
    Fraction.rotate_of_odd h.odd_parity, Parents.current, Parents.combine]
  apply Fraction.ext <;> dsimp <;> omega

/-- Rotation leaves digit one fixed and exchanges the two other steps. -/
theorem Parents.ValidFrame.rotate_step {parents : Parents} (h : parents.ValidFrame)
    (digit : Digit) : (parents.step digit).rotate = parents.rotate.step digit.swapTwoThree := by
  cases digit
  · exact congrArg₂ Parents.mk h.rotate_current_even h.rotate_current_odd
  · exact congrArg (Parents.mk parents.even.rotate) h.rotate_current_odd
  · exact congrArg (fun odd => Parents.mk odd parents.odd.rotate) h.rotate_current_even

theorem Parents.ValidFrame.rotate_walk {parents : Parents} (h : parents.ValidFrame)
    (word : Word) : (parents.walk word).rotate = parents.rotate.walk (word.map Digit.swapTwoThree) := by
  induction word generalizing parents with
  | nil => rfl
  | cons digit tail ih =>
    rw [Parents.walk_cons, ih (h.step digit), List.map_cons, Parents.walk_cons, h.rotate_step]

theorem root_rotate : root.rotate = root := rfl

theorem rotate_parentsAt (word : Word) :
    (parentsAt word).rotate = parentsAt (word.map Digit.swapTwoThree) := by
  unfold parentsAt
  rw [root_valid.rotate_walk, root_rotate]

def Birth.rotate (birth : Birth) : Birth :=
  (birth.1.map Digit.swapTwoThree, birth.2.flip)

theorem Birth.rotate_fraction (birth : Birth) :
    birth.fraction.rotate = birth.rotate.fraction := by
  obtain ⟨word, parity⟩ := birth
  have h := parentsAt_valid word
  cases parity
  · unfold Birth.fraction Birth.rotate
    exact h.rotate_current_odd.trans (congrArg (fun parents => parents.current .even)
      (rotate_parentsAt word))
  · unfold Birth.fraction Birth.rotate
    exact h.rotate_current_even.trans (congrArg (fun parents => parents.current .odd)
      (rotate_parentsAt word))

theorem Birth.rotate_length (birth : Birth) : birth.rotate.1.length = birth.1.length :=
  List.length_map ..

theorem Birth.rotate_rotate (birth : Birth) : birth.rotate.rotate = birth := by
  obtain ⟨word, parity⟩ := birth
  apply Prod.ext
  · change (word.map Digit.swapTwoThree).map Digit.swapTwoThree = word
    induction word with
    | nil => rfl
    | cons digit tail ih => simp only [List.map_cons, Digit.swapTwoThree_swapTwoThree, ih]
  · cases parity <;> rfl

theorem phase_rotate_word (word : Word) : phase (word.map Digit.swapTwoThree) = phase word := by
  have counts : (word.map Digit.swapTwoThree).count .one = word.count .one := by
    induction word with
    | nil => rfl
    | cons digit tail ih => cases digit <;> simp [Digit.swapTwoThree, ih]
  unfold phase
  rw [counts]

theorem Fraction.rotate_reduced {fraction : Fraction} (hinterval : fraction.InUnitInterval)
    (hreduced : fraction.Reduced) : fraction.rotate.Reduced := by
  obtain ⟨hden, hlo, hhi⟩ := hinterval
  by_cases hzero : fraction.num = 0
  · have hdvd : fraction.den ∣ (1 : ℤ) := by
      obtain ⟨_, denomCoeff, hbezout⟩ := hreduced
      exact ⟨denomCoeff, by simpa [hzero, mul_comm] using hbezout.symm⟩
    have hend : fraction = (⟨0, 1⟩ : Fraction) :=
      Fraction.ext hzero (Int.eq_one_of_dvd_one hden.le hdvd)
    rw [hend]
    exact root_valid.even_reduced
  · by_cases htop : fraction.num = fraction.den
    · have hdvd : fraction.den ∣ (1 : ℤ) := by
        obtain ⟨numCoeff, denomCoeff, hbezout⟩ := hreduced
        refine ⟨numCoeff + denomCoeff, ?_⟩
        rw [← hbezout, htop]
        ring
      have hdenOne := Int.eq_one_of_dvd_one hden.le hdvd
      have hend : fraction = (⟨1, 1⟩ : Fraction) := Fraction.ext (htop.trans hdenOne) hdenOne
      rw [hend]
      exact root_valid.odd_reduced
    · have hinterior : fraction.Interior := ⟨by omega, by omega⟩
      rw [← fraction_birthOf fraction hinterior hreduced, Birth.rotate_fraction]
      exact Birth.reduced _

end FLatticePaper.Farey
