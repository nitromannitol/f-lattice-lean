import FLatticePaper.Construction.Offsets

namespace FLatticePaper.Construction

open Farey

/-! The offset tables of Section 7 of the paper, `eq:offsets_w1_odd`, `eq:offsets_w1_even`, `eq:alt_offsets`,
the doubling vectors `eq:alt_doubled` and the seventh alternate position, against `standardJets`,
`alternateJets` and `seventhAlternateJet`. The paper's generator vectors are `v_{n/d,1} = 2 𝔳_{n/d,1}` for odd `n/d`
and `v_{n/d,2} = 𝔳_{n/d,2}`, with `𝔳_{n/d,1} = (d, n)` and `𝔳_{n/d,2} = (n - d, n + d)`. Here `p` is the odd parent
and `q` the even parent of the word. Only translations are compared, since the paper's tables have no slopes. -/

/-- The paper's `v_{p,1}` for an odd parent `p`. -/
def texV1Odd (p : Fraction) : Site := (2 * p.den, 2 * p.num)

/-- The paper's `v_{q,1}` for an even parent `q`. -/
def texV1Even (q : Fraction) : Site := (q.den, q.num)

/-- The paper's `v_{n/d,2}` for either parent. -/
def texV2 (f : Fraction) : Site := (f.num - f.den, f.num + f.den)

/-! ### Standard tiles. Phase 0 is W1 even (`eq:offsets_w1_even`), phase 1 is W1 odd (`eq:offsets_w1_odd`). -/

/-- Odd child, phase 0 (W1 even), `c(T) - c(T(p_0))`: `T^d(q)^+` at 0, `T^d(q)^-` at `v_{p,1} + v_{p,2}`,
`T(p)^+` at `2 v_{q,1}`, `T(p)^-` at `v_{q,2}`; the second pieces of the doubled tiles sit at `+ v_{q,1}`. -/
theorem standard_odd_phase0 (word : Word) (h : phase word = 0) :
    (standardJets word .odd 0).1 = 0 ∧
    (standardJets word .odd 1).1 = texV1Even (parentsAt word).even ∧
    (standardJets word .odd 2).1 = texV1Odd (parentsAt word).odd + texV2 (parentsAt word).odd ∧
    (standardJets word .odd 3).1 =
      texV1Odd (parentsAt word).odd + texV2 (parentsAt word).odd + texV1Even (parentsAt word).even ∧
    (standardJets word .odd 4).1 = 2 • texV1Even (parentsAt word).even ∧
    (standardJets word .odd 5).1 = texV2 (parentsAt word).even := by
  simp only [standardJets, h, if_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (0 : TileJet).1 = 0
    rfl
  · show (0 + kernelJet (parentsAt word).even).1 = _
    simp [kernelJet, texV1Even]
  · show (2 • kernelJet (parentsAt word).odd + transverseJet (parentsAt word).odd).1 = _
    refine Prod.ext ?_ ?_ <;> simp [kernelJet, transverseJet, texV1Odd, texV2]
  · show (2 • kernelJet (parentsAt word).odd + transverseJet (parentsAt word).odd +
      kernelJet (parentsAt word).even).1 = _
    refine Prod.ext ?_ ?_ <;> simp [kernelJet, transverseJet, texV1Odd, texV1Even, texV2]
  · show (2 • kernelJet (parentsAt word).even).1 = _
    refine Prod.ext ?_ ?_ <;> simp [kernelJet, texV1Even]
  · show (transverseJet (parentsAt word).even).1 = _
    simp [transverseJet, texV2]

/-- Odd child, phase 1 (W1 odd), `c(T) - c(T(p_0))`: `T^d(q)^+` at `v_{p,1}`, `T^d(q)^-` at `v_{p,2}`,
`T(p)^+` at 0, `T(p)^-` at `2 v_{q,1} + v_{q,2}`. -/
theorem standard_odd_phase1 (word : Word) (h : phase word = 1) :
    (standardJets word .odd 0).1 = texV1Odd (parentsAt word).odd ∧
    (standardJets word .odd 1).1 = texV1Odd (parentsAt word).odd + texV1Even (parentsAt word).even ∧
    (standardJets word .odd 2).1 = texV2 (parentsAt word).odd ∧
    (standardJets word .odd 3).1 = texV2 (parentsAt word).odd + texV1Even (parentsAt word).even ∧
    (standardJets word .odd 4).1 = 0 ∧
    (standardJets word .odd 5).1 = 2 • texV1Even (parentsAt word).even + texV2 (parentsAt word).even := by
  simp only [standardJets, h, Nat.one_ne_zero, ↓reduceIte]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (2 • kernelJet (parentsAt word).odd).1 = _
    refine Prod.ext ?_ ?_ <;> simp [kernelJet, texV1Odd]
  · show (2 • kernelJet (parentsAt word).odd + kernelJet (parentsAt word).even).1 = _
    refine Prod.ext ?_ ?_ <;> simp [kernelJet, texV1Odd, texV1Even]
  · show (transverseJet (parentsAt word).odd).1 = _
    simp [transverseJet, texV2]
  · show (transverseJet (parentsAt word).odd + kernelJet (parentsAt word).even).1 = _
    refine Prod.ext ?_ ?_ <;> simp [kernelJet, transverseJet, texV2, texV1Even]
  · show (0 : TileJet).1 = 0
    rfl
  · show (2 • kernelJet (parentsAt word).even + transverseJet (parentsAt word).even).1 = _
    refine Prod.ext ?_ ?_ <;> simp [kernelJet, transverseJet, texV1Even, texV2]

/-! ### Standard tiles, even child: `c(T) - c(T(q_0))`. Phase 0 is W1 even, phase 1 is W1 odd. -/

/-- Even child, phase 0 (W1 even): `T(q)^+` at 0, `T(q)^-` at `v_{p,1} + 2 v_{p,2}`, `T^d(p)^+` at `v_{q,1}`,
`T^d(p)^-` at `v_{q,2}`; the second pieces of `T^d(p)` sit at `+ v_{p,2}`. -/
theorem standard_even_phase0 (word : Word) (h : phase word = 0) :
    (standardJets word .even 0).1 = 0 ∧
    (standardJets word .even 1).1 = texV1Odd (parentsAt word).odd + 2 • texV2 (parentsAt word).odd ∧
    (standardJets word .even 2).1 = texV1Even (parentsAt word).even ∧
    (standardJets word .even 3).1 = texV1Even (parentsAt word).even + texV2 (parentsAt word).odd ∧
    (standardJets word .even 4).1 = texV2 (parentsAt word).even ∧
    (standardJets word .even 5).1 = texV2 (parentsAt word).even + texV2 (parentsAt word).odd := by
  simp only [standardJets, h, if_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (0 : TileJet).1 = 0
    rfl
  · show (2 • kernelJet (parentsAt word).odd + 2 • transverseJet (parentsAt word).odd).1 = _
    refine Prod.ext ?_ ?_ <;> simp [kernelJet, transverseJet, texV1Odd, texV2]
  · show (kernelJet (parentsAt word).even).1 = _
    simp [kernelJet, texV1Even]
  · show (kernelJet (parentsAt word).even + transverseJet (parentsAt word).odd).1 = _
    refine Prod.ext ?_ ?_ <;> simp [kernelJet, transverseJet, texV1Even, texV2]
  · show (transverseJet (parentsAt word).even).1 = _
    simp [transverseJet, texV2]
  · show (transverseJet (parentsAt word).even + transverseJet (parentsAt word).odd).1 = _
    refine Prod.ext ?_ ?_ <;> simp [transverseJet, texV2]

/-- Even child, phase 1 (W1 odd): `T(q)^+` at `v_{p,1}`, `T(q)^-` at `2 v_{p,2}`, `T^d(p)^+` at 0,
`T^d(p)^-` at `v_{q,1} + v_{q,2}`; the second pieces sit at `+ v_{p,2}`. -/
theorem standard_even_phase1 (word : Word) (h : phase word = 1) :
    (standardJets word .even 0).1 = texV1Odd (parentsAt word).odd ∧
    (standardJets word .even 1).1 = 2 • texV2 (parentsAt word).odd ∧
    (standardJets word .even 2).1 = 0 ∧
    (standardJets word .even 3).1 = texV2 (parentsAt word).odd ∧
    (standardJets word .even 4).1 = texV1Even (parentsAt word).even + texV2 (parentsAt word).even ∧
    (standardJets word .even 5).1 =
      texV1Even (parentsAt word).even + texV2 (parentsAt word).even + texV2 (parentsAt word).odd := by
  simp only [standardJets, h, Nat.one_ne_zero, ↓reduceIte]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (2 • kernelJet (parentsAt word).odd).1 = _
    refine Prod.ext ?_ ?_ <;> simp [kernelJet, texV1Odd]
  · show (2 • transverseJet (parentsAt word).odd).1 = _
    refine Prod.ext ?_ ?_ <;> simp [transverseJet, texV2]
  · show (0 : TileJet).1 = 0
    rfl
  · show (0 + transverseJet (parentsAt word).odd).1 = _
    simp [transverseJet, texV2]
  · show (transverseJet (parentsAt word).even + kernelJet (parentsAt word).even).1 = _
    refine Prod.ext (by simp [kernelJet, transverseJet, texV1Even, texV2])
      (by simp [kernelJet, transverseJet, texV1Even, texV2]; ring)
  · show (transverseJet (parentsAt word).even + kernelJet (parentsAt word).even +
      transverseJet (parentsAt word).odd).1 = _
    refine Prod.ext (by simp [kernelJet, transverseJet, texV1Even, texV2])
      (by simp [kernelJet, transverseJet, texV1Even, texV2]; ring)

/-! ### Alternate tiles. The doubling vectors are `S_p = v_{q,1} + v_{p,2}` (W1 even) and `S_q` from `eq:alt_doubled`. -/

/-- Odd alternate, phase 0 (W1 even, `eq:alt_offsets`, `c(T) - c(T̂(p_0))`): `T(q)^+` at 0, `T(q)^-` at
`v_{p,1} + 2 v_{p,2} + v_{q,1}`, `T^{ds}(p)^+` at `v_{q,1}`, `T^{ds}(p)^-` at `v_{q,2}`, second pieces at `+ S_p`. -/
theorem alternate_odd_phase0 (word : Word) (h : phase word = 0) :
    (alternateJets word .odd 0).1 = 0 ∧
    (alternateJets word .odd 1).1 =
      texV1Odd (parentsAt word).odd + 2 • texV2 (parentsAt word).odd + texV1Even (parentsAt word).even ∧
    (alternateJets word .odd 2).1 = texV1Even (parentsAt word).even ∧
    (alternateJets word .odd 3).1 =
      texV1Even (parentsAt word).even + (texV1Even (parentsAt word).even + texV2 (parentsAt word).odd) ∧
    (alternateJets word .odd 4).1 = texV2 (parentsAt word).even ∧
    (alternateJets word .odd 5).1 =
      texV2 (parentsAt word).even + (texV1Even (parentsAt word).even + texV2 (parentsAt word).odd) := by
  simp only [alternateJets, h, if_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (0 : TileJet).1 = 0
    rfl
  · show (2 • kernelJet (parentsAt word).odd + 2 • transverseJet (parentsAt word).odd +
      kernelJet (parentsAt word).even).1 = _
    refine Prod.ext ?_ ?_ <;> simp [kernelJet, transverseJet, texV1Odd, texV1Even, texV2]
  · show (kernelJet (parentsAt word).even).1 = _
    simp [kernelJet, texV1Even]
  · show (kernelJet (parentsAt word).even +
      (kernelJet (parentsAt word).even + transverseJet (parentsAt word).odd)).1 = _
    refine Prod.ext ?_ ?_ <;> simp [kernelJet, transverseJet, texV1Even, texV2]
  · show (transverseJet (parentsAt word).even).1 = _
    simp [transverseJet, texV2]
  · show (transverseJet (parentsAt word).even +
      (kernelJet (parentsAt word).even + transverseJet (parentsAt word).odd)).1 = _
    refine Prod.ext ?_ ?_ <;> simp [kernelJet, transverseJet, texV1Even, texV2]

/-- Odd alternate, phase 1 (W1 odd): `T(q)^+` at `v_{p,1}`, `T(q)^-` at `2 v_{p,2} - v_{q,1}`, `T^{ds}(p)^+` at 0,
`T^{ds}(p)^-` at `v_{q,1} + v_{q,2}`, second pieces at `+ S_p` with `S_p = -v_{q,1} + v_{p,2}`. -/
theorem alternate_odd_phase1 (word : Word) (h : phase word = 1) :
    (alternateJets word .odd 0).1 = texV1Odd (parentsAt word).odd ∧
    (alternateJets word .odd 1).1 = 2 • texV2 (parentsAt word).odd - texV1Even (parentsAt word).even ∧
    (alternateJets word .odd 2).1 = 0 ∧
    (alternateJets word .odd 3).1 = texV2 (parentsAt word).odd - texV1Even (parentsAt word).even ∧
    (alternateJets word .odd 4).1 = texV1Even (parentsAt word).even + texV2 (parentsAt word).even ∧
    (alternateJets word .odd 5).1 =
      texV1Even (parentsAt word).even + texV2 (parentsAt word).even +
        (texV2 (parentsAt word).odd - texV1Even (parentsAt word).even) := by
  simp only [alternateJets, h, Nat.one_ne_zero, ↓reduceIte]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (2 • kernelJet (parentsAt word).odd).1 = _
    refine Prod.ext ?_ ?_ <;> simp [kernelJet, texV1Odd]
  · show (2 • transverseJet (parentsAt word).odd - kernelJet (parentsAt word).even).1 = _
    refine Prod.ext ?_ ?_ <;> simp [kernelJet, transverseJet, texV1Even, texV2]
  · show (0 : TileJet).1 = 0
    rfl
  · show (0 + (-kernelJet (parentsAt word).even + transverseJet (parentsAt word).odd)).1 = _
    refine Prod.ext ?_ ?_ <;> simp [kernelJet, transverseJet, texV1Even, texV2] <;> ring
  · show (kernelJet (parentsAt word).even + transverseJet (parentsAt word).even).1 = _
    refine Prod.ext ?_ ?_ <;> simp [kernelJet, transverseJet, texV1Even, texV2]
  · show (kernelJet (parentsAt word).even + transverseJet (parentsAt word).even +
      (-kernelJet (parentsAt word).even + transverseJet (parentsAt word).odd)).1 = _
    refine Prod.ext ?_ ?_ <;> simp [kernelJet, transverseJet, texV1Even, texV2] <;> ring

/-! ### Alternate tiles, even child: `c(T) - c(T̂(q_0))`. -/

/-- Even alternate, phase 0 (W1 even): `T^{ds}(q)^+` at 0, `T^{ds}(q)^-` at `v_{p,1} + v_{p,2}`, `T(p)^+` at
`v_{q,1}`, `T(p)^-` at `v_{p,2} + v_{q,2} - v_{q,1}`; second pieces of `T^{ds}(q)` at `+ S_q`, `S_q = -v_{q,1} + v_{p,2}`. -/
theorem alternate_even_phase0 (word : Word) (h : phase word = 0) :
    (alternateJets word .even 0).1 = 0 ∧
    (alternateJets word .even 1).1 = texV2 (parentsAt word).odd - texV1Even (parentsAt word).even ∧
    (alternateJets word .even 2).1 = texV1Odd (parentsAt word).odd + texV2 (parentsAt word).odd ∧
    (alternateJets word .even 3).1 =
      texV1Odd (parentsAt word).odd + texV2 (parentsAt word).odd +
        (texV2 (parentsAt word).odd - texV1Even (parentsAt word).even) ∧
    (alternateJets word .even 4).1 = texV1Even (parentsAt word).even ∧
    (alternateJets word .even 5).1 =
      texV2 (parentsAt word).odd - texV1Even (parentsAt word).even + texV2 (parentsAt word).even := by
  simp only [alternateJets, h, if_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (0 : TileJet).1 = 0
    rfl
  · show (0 + (-kernelJet (parentsAt word).even + transverseJet (parentsAt word).odd)).1 = _
    refine Prod.ext ?_ ?_ <;> simp [kernelJet, transverseJet, texV1Even, texV2] <;> ring
  · show (2 • kernelJet (parentsAt word).odd + transverseJet (parentsAt word).odd).1 = _
    refine Prod.ext ?_ ?_ <;> simp [kernelJet, transverseJet, texV1Odd, texV2]
  · show (2 • kernelJet (parentsAt word).odd + transverseJet (parentsAt word).odd +
      (-kernelJet (parentsAt word).even + transverseJet (parentsAt word).odd)).1 = _
    refine Prod.ext ?_ ?_ <;> simp [kernelJet, transverseJet, texV1Odd, texV1Even, texV2] <;> ring
  · show (kernelJet (parentsAt word).even).1 = _
    simp [kernelJet, texV1Even]
  · show (transverseJet (parentsAt word).odd - kernelJet (parentsAt word).even +
      transverseJet (parentsAt word).even).1 = _
    refine Prod.ext ?_ ?_ <;> simp [kernelJet, transverseJet, texV1Even, texV2]

/-- Even alternate, phase 1 (W1 odd): `T^{ds}(q)^+` at `v_{p,1}`, `T^{ds}(q)^-` at `v_{p,2}`, `T(p)^+` at 0,
`T(p)^-` at `v_{p,2} + v_{q,2} + 2 v_{q,1}`; second pieces at `+ S_q`, `S_q = v_{q,1} + v_{p,2}`. -/
theorem alternate_even_phase1 (word : Word) (h : phase word = 1) :
    (alternateJets word .even 0).1 = texV1Odd (parentsAt word).odd ∧
    (alternateJets word .even 1).1 =
      texV1Odd (parentsAt word).odd + (texV1Even (parentsAt word).even + texV2 (parentsAt word).odd) ∧
    (alternateJets word .even 2).1 = texV2 (parentsAt word).odd ∧
    (alternateJets word .even 3).1 =
      texV2 (parentsAt word).odd + (texV1Even (parentsAt word).even + texV2 (parentsAt word).odd) ∧
    (alternateJets word .even 4).1 = 0 ∧
    (alternateJets word .even 5).1 =
      texV2 (parentsAt word).odd + texV2 (parentsAt word).even + 2 • texV1Even (parentsAt word).even := by
  simp only [alternateJets, h, Nat.one_ne_zero, ↓reduceIte]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (2 • kernelJet (parentsAt word).odd).1 = _
    refine Prod.ext ?_ ?_ <;> simp [kernelJet, texV1Odd]
  · show (2 • kernelJet (parentsAt word).odd + (kernelJet (parentsAt word).even +
      transverseJet (parentsAt word).odd)).1 = _
    refine Prod.ext ?_ ?_ <;> simp [kernelJet, transverseJet, texV1Odd, texV1Even, texV2]
  · show (transverseJet (parentsAt word).odd).1 = _
    simp [transverseJet, texV2]
  · show (transverseJet (parentsAt word).odd + (kernelJet (parentsAt word).even +
      transverseJet (parentsAt word).odd)).1 = _
    refine Prod.ext ?_ ?_ <;> simp [kernelJet, transverseJet, texV1Even, texV2]
  · show (0 : TileJet).1 = 0
    rfl
  · show (transverseJet (parentsAt word).odd + transverseJet (parentsAt word).even +
      2 • kernelJet (parentsAt word).even).1 = _
    refine Prod.ext ?_ ?_ <;> simp [kernelJet, transverseJet, texV1Even, texV2]

/-! ### The seventh alternate piece. The paper gives no value where the alternate tile is omitted (`−`); those
cases are not stated here. -/

/-- Seventh piece, odd child, phase 0 (even-first), Types 1 and 3: `v_{q,1} + v_{p,2}`. -/
theorem seventh_odd_phase0 (beforePush : Word) (digit : Digit) (hd : digit ≠ .two)
    (h : phase (beforePush ++ [digit]) = 0) :
    (seventhAlternateJet beforePush digit .odd).1 =
      texV1Even (parentsAt (beforePush ++ [digit])).even + texV2 (parentsAt (beforePush ++ [digit])).odd := by
  have hd' : decide (phase (beforePush ++ [digit]) = 0) = true := decide_eq_true h
  cases digit with
  | one =>
    simp only [seventhAlternateJet, hd']
    refine Prod.ext ?_ ?_ <;> simp [kernelJet, transverseJet, texV1Even, texV2]
  | two => exact absurd rfl hd
  | three =>
    simp only [seventhAlternateJet, hd']
    refine Prod.ext ?_ ?_ <;> simp [kernelJet, transverseJet, texV1Even, texV2]

/-- Seventh piece, odd child, phase 1 (odd-first), Types 1 and 3: `v_{p,2} + v_{p,1} - v_{q,1}`. -/
theorem seventh_odd_phase1 (beforePush : Word) (digit : Digit) (hd : digit ≠ .two)
    (h : phase (beforePush ++ [digit]) = 1) :
    (seventhAlternateJet beforePush digit .odd).1 =
      texV2 (parentsAt (beforePush ++ [digit])).odd + texV1Odd (parentsAt (beforePush ++ [digit])).odd -
        texV1Even (parentsAt (beforePush ++ [digit])).even := by
  have hd' : decide (phase (beforePush ++ [digit]) = 0) = false := decide_eq_false (by omega)
  cases digit with
  | one =>
    simp only [seventhAlternateJet, hd']
    refine Prod.ext ?_ ?_ <;> simp [kernelJet, transverseJet, texV1Odd, texV1Even, texV2]
  | two => exact absurd rfl hd
  | three =>
    simp only [seventhAlternateJet, hd']
    refine Prod.ext ?_ ?_ <;> simp [kernelJet, transverseJet, texV1Odd, texV1Even, texV2]

/-- Seventh piece, even child, phase 0 (even-first), Type 1: `v_{p,2} + v_{p,1} - v_{q,1}`. -/
theorem seventh_even_phase0_one (beforePush : Word) (h : phase (beforePush ++ [.one]) = 0) :
    (seventhAlternateJet beforePush .one .even).1 =
      texV2 (parentsAt (beforePush ++ [.one])).odd + texV1Odd (parentsAt (beforePush ++ [.one])).odd -
        texV1Even (parentsAt (beforePush ++ [.one])).even := by
  have hd' : decide (phase (beforePush ++ [.one]) = 0) = true := decide_eq_true h
  simp only [seventhAlternateJet, hd']
  refine Prod.ext ?_ ?_ <;> simp [kernelJet, transverseJet, texV1Odd, texV1Even, texV2] <;> ring

/-- Seventh piece, even child, phase 0 (even-first), Type 2: `v_{q,2}`. -/
theorem seventh_even_phase0_two (beforePush : Word) (h : phase (beforePush ++ [.two]) = 0) :
    (seventhAlternateJet beforePush .two .even).1 = texV2 (parentsAt (beforePush ++ [.two])).even := by
  have hd' : decide (phase (beforePush ++ [.two]) = 0) = true := decide_eq_true h
  simp only [seventhAlternateJet, hd']
  simp [transverseJet, texV2]

/-- Seventh piece, even child, phase 1 (odd-first), Type 1: `v_{p,2} + v_{q,1}`. -/
theorem seventh_even_phase1_one (beforePush : Word) (h : phase (beforePush ++ [.one]) = 1) :
    (seventhAlternateJet beforePush .one .even).1 =
      texV2 (parentsAt (beforePush ++ [.one])).odd + texV1Even (parentsAt (beforePush ++ [.one])).even := by
  have hd' : decide (phase (beforePush ++ [.one]) = 0) = false := decide_eq_false (by omega)
  simp only [seventhAlternateJet, hd']
  refine Prod.ext ?_ ?_ <;> simp [kernelJet, transverseJet, texV1Even, texV2] <;> ring

/-- Seventh piece, even child, phase 1 (odd-first), Type 2: `2 v_{q,1} + v_{q,2}`. -/
theorem seventh_even_phase1_two (beforePush : Word) (h : phase (beforePush ++ [.two]) = 1) :
    (seventhAlternateJet beforePush .two .even).1 =
      2 • texV1Even (parentsAt (beforePush ++ [.two])).even + texV2 (parentsAt (beforePush ++ [.two])).even := by
  have hd' : decide (phase (beforePush ++ [.two]) = 0) = false := decide_eq_false (by omega)
  simp only [seventhAlternateJet, hd']
  refine Prod.ext ?_ ?_ <;> simp [kernelJet, transverseJet, texV1Even, texV2]

end FLatticePaper.Construction
