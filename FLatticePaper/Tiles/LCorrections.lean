import FLatticePaper.Construction.Offsets
import FLatticePaper.Construction.OffsetTables

/-! # The L-corrections of the paper (`def:odd_l_correction`, `def:even_l_correction`), task 35

`farey_recursion.tex` 3491-3594 defines the odd and even `L`-corrections as unions of translates of the parent tiles.
Here the printed offsets `K_1, ..., K_4` are transcribed (`oddTexK`, `evenTexK`), the corrections are the cell sets
`oddLCorrection`, `evenLCorrection` built from them, and the constructor's increments `correctionJets` are compared with the
printed table for every word.

Sign and parity conventions. `odd = true` is `W_1` odd (the number of 1s in the word), `plus = true` is the sign `+`.
The constructor's `flip` flag is the opposite of `plus` (`flip = false` is `+`), as the matching of the case tables shows.

Agreement with the printed tables, for every word (`correctionJets` with the parents of the word `beforeLast ++ [last]`):
* odd, `W_1` odd, `+`: all four translations agree;   odd, `W_1` even, `-`: all four agree;
* odd, `W_1` even, `+`: `K_1, K_2, K_4` agree and `K_3` differs: the printed `-(v_{q,2}+v_{p,2})` is the constructor's
  `-v_{q,2}+v_{p,2}`;
* odd, `W_1` odd, `-`: `K_2, K_3, K_4` agree and `K_1` differs: the printed `v_{q,2}` is the constructor's `-v_{q,2}`;
* even, `W_1` odd, `+`; even, `W_1` even, `+`; even, `W_1` even, `-`: all four agree, for `s = 1, 2` in `K_3`;
* even, `W_1` odd, `-`: `K_1, K_3, K_4` agree and `K_2` differs: the printed `-v_{q,1}+v_{p,1}-v_{q,1}` is the constructor's
  `-v_{q,1}+v_{p,2}-v_{q,2}`.
The odd `K_1` (`W_1` odd, `-`) is the negative of the printed value, so it agrees exactly when `v_{q,2} = 0`; the odd
`K_3` (`W_1` even, `+`) differs from the printed value by `2 v_{p,2}`; the even `K_2` (`W_1` odd, `-`) differs by
`(v_{p,2} - v_{q,2}) - (v_{p,1} - v_{q,1})`. All four statements are proved below for every word.

The two readings of the placement are both recorded: the cell sets below place the bridge and the heads at `k K_1 + K_2`
(the `c`-relations of the text), which is the reading that reproduces the constructor's outputs; the union formulas read
literally (without `k K_1`) do not. Not formalised here: the constructor's head restoration (`alternateRestoration`), its
bridge nudge for pure base-run ancestors, and the boundary-word clause of `lemma:l_correc_properties` (2). The inductive step
of that lemma (3635-3640) is discussed in the report: its displayed decomposition is not an identity for the definition at
`k = 1`. -/

namespace FLatticePaper.Tiles.LCorrections

open FLatticePaper.Farey FLatticePaper.Construction

/-- The printed `K_1, K_2, K_3, K_4` of `eq:l_correction_odd` (lines 3513-3530), for `W_1` odd (`odd`) or even and the
sign `+` (`plus`) or `-`. -/
def oddTexK (odd plus : Bool) (p q : Fraction) : Site × Site × Site × Site :=
  match odd, plus with
  | true, true =>
    (texV2 q, texV2 q + (texV1Even q - texV1Odd p),
      (-texV2 q + texV2 p) + (texV1Odd p - texV1Even q), -texV1Even q)
  | true, false => (texV2 q, -texV2 p, texV1Odd p - texV1Even q, texV1Even q)
  | false, true => (texV2 q, texV2 q, -(texV2 q + texV2 p), texV1Even q)
  | false, false =>
    (-texV2 q, -texV2 p - (texV1Odd p - texV1Even q), 0, -texV1Even q)

/-- The printed `K_1, K_2, K_3, K_4` of `eq:l_correction_even` (lines 3566-3588), with `s = 2` when `s2` is true. -/
def evenTexK (odd plus s2 : Bool) (p q : Fraction) : Site × Site × Site × Site :=
  match odd, plus with
  | true, true =>
    (texV1Odd p, texV1Odd p,
      if s2 then (texV1Even q - texV1Odd p) + ((texV2 q - texV2 p) + texV1Even q) else texV1Even q - texV1Odd p,
      texV2 p)
  | false, true =>
    (-texV1Odd p, -texV1Even q, if s2 then texV2 q - texV2 p else texV1Odd p - texV1Even q, texV2 p)
  | true, false =>
    (-texV1Odd p, -texV1Even q + (texV1Odd p - texV1Even q),
      if s2 then (texV2 q - texV2 p) + texV1Even q else 0, -texV2 p)
  | false, false =>
    (texV1Odd p, texV1Odd p + (texV2 p - texV2 q),
      if s2 then (texV2 q - texV2 p) - texV1Odd p + texV1Even q else 0, -texV2 p)

/-- The shifted copy of a cell set. -/
def shiftCells (T : Finset Site) (v : Site) : Finset Site :=
  T.image (fun x => x + v)

/-- The odd `L`-correction of `eq:l_correction_odd` as a cell set, for the word `w = w_1 s 2^k` (`k` trailing 2s):
stems `T(q_2) + j K_1` for `0 ≤ j ≤ k`, bridge `T(p_2)` at `k K_1 + K_2`, heads `T-hat(q_2)` at `k K_1 + K_2 + K_3 + i K_4`
for `1 ≤ i ≤ 2(k+1) - z`, where `z = 0` when the correction is elongated. -/
def oddLCorrection (k : ℕ) (elongated : Bool) (Tp Tq Th : Finset Site) (p q : Fraction) (odd plus : Bool) :
    Finset Site :=
  let K := oddTexK odd plus p q
  let base : Site := (k : ℤ) • K.1 + K.2.1
  let z : ℕ := if elongated then 0 else 1
  (Finset.range (k + 1)).biUnion (fun j => shiftCells Tq ((j : ℤ) • K.1)) ∪
    shiftCells Tp base ∪
    (Finset.range (2 * (k + 1) - z)).biUnion (fun i => shiftCells Th (base + K.2.2.1 + ((i : ℤ) + 1) • K.2.2.2))

/-- The even `L`-correction of `eq:l_correction_even` as a cell set, for `w = w_1 s 3^k`: stems `T(p_2) + j K_1`,
bridge `T(q_2)` at `k K_1 + K_2`, heads `T-hat(p_2)` at `k K_1 + K_2 + K_3 + i K_4`. -/
def evenLCorrection (k : ℕ) (elongated : Bool) (Tp Tq Th : Finset Site) (p q : Fraction) (odd plus s2 : Bool) :
    Finset Site :=
  let K := evenTexK odd plus s2 p q
  let base : Site := (k : ℤ) • K.1 + K.2.1
  let z : ℕ := if elongated then 0 else 1
  (Finset.range (k + 1)).biUnion (fun j => shiftCells Tp ((j : ℤ) • K.1)) ∪
    shiftCells Tq base ∪
    (Finset.range (2 * (k + 1) - z)).biUnion (fun i => shiftCells Th (base + K.2.2.1 + ((i : ℤ) + 1) • K.2.2.2))

/-! ### The constructor's increments against the printed tables, for every word. -/

theorem kernelJet_fst (f : Fraction) : (kernelJet f).1 = texV1Even f := rfl

theorem transverseJet_fst (f : Fraction) : (transverseJet f).1 = texV2 f := rfl

theorem two_nsmul_texV1Even (f : Fraction) : (2 : ℕ) • texV1Even f = texV1Odd f := by
  rw [two_nsmul]
  ext <;> simp [texV1Even, texV1Odd] <;> ring

theorem twiceKernelJet_fst (f : Fraction) : (2 • kernelJet f).1 = texV1Odd f := by
  rw [Prod.smul_fst, kernelJet_fst, two_nsmul_texV1Even]

/-- The parent pair `(p_2, q_2)` of the word `w` (the odd and the even parent). -/
def wordParents (w : Word) : Fraction × Fraction := ((parentsAt w).odd, (parentsAt w).even)

/-- Odd, `W_1` odd, sign `+` (`flip = false`): the four translations of the constructor are the printed `K_1..K_4`. -/
theorem odd_W1odd_plus (bl : Word) (l : Digit) (h : phase (bl ++ [l]) = 1) :
    (correctionJets bl l .odd false).scan.1 = (oddTexK true true (wordParents (bl ++ [l])).1
      (wordParents (bl ++ [l])).2).1 ∧
    (correctionJets bl l .odd false).bridge.1 = (oddTexK true true (wordParents (bl ++ [l])).1
      (wordParents (bl ++ [l])).2).2.1 ∧
    (correctionJets bl l .odd false).headStart.1 = (oddTexK true true (wordParents (bl ++ [l])).1
      (wordParents (bl ++ [l])).2).2.2.1 ∧
    (correctionJets bl l .odd false).headStep.1 = (oddTexK true true (wordParents (bl ++ [l])).1
      (wordParents (bl ++ [l])).2).2.2.2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext <;>
    simp [correctionJets, oddTexK, wordParents, h, transverseJet, kernelJet, texV1Odd, texV1Even, texV2]

/-- Odd, `W_1` odd, sign `-` (`flip = true`): the scan is the negative of the printed `K_1`; the rest agree. -/
theorem odd_W1odd_minus (bl : Word) (l : Digit) (h : phase (bl ++ [l]) = 1) :
    (correctionJets bl l .odd true).scan.1 = -(texV2 (wordParents (bl ++ [l])).2) ∧
    (correctionJets bl l .odd true).bridge.1 = (oddTexK true false (wordParents (bl ++ [l])).1
      (wordParents (bl ++ [l])).2).2.1 ∧
    (correctionJets bl l .odd true).headStart.1 = (oddTexK true false (wordParents (bl ++ [l])).1
      (wordParents (bl ++ [l])).2).2.2.1 ∧
    (correctionJets bl l .odd true).headStep.1 = (oddTexK true false (wordParents (bl ++ [l])).1
      (wordParents (bl ++ [l])).2).2.2.2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext <;>
    simp [correctionJets, oddTexK, wordParents, h, transverseJet, kernelJet, texV1Odd, texV1Even, texV2]

/-- Odd, `W_1` even, sign `+`: `K_1` and `K_2` agree and `K_4` agrees; the constructor's `K_3` is `-v_{q,2} + v_{p,2}`. -/
theorem odd_W1even_plus (bl : Word) (l : Digit) (h : phase (bl ++ [l]) = 0) :
    (correctionJets bl l .odd false).scan.1 = (oddTexK false true (wordParents (bl ++ [l])).1
      (wordParents (bl ++ [l])).2).1 ∧
    (correctionJets bl l .odd false).bridge.1 = (oddTexK false true (wordParents (bl ++ [l])).1
      (wordParents (bl ++ [l])).2).2.1 ∧
    (correctionJets bl l .odd false).headStart.1 = -texV2 (wordParents (bl ++ [l])).2 +
      texV2 (wordParents (bl ++ [l])).1 ∧
    (correctionJets bl l .odd false).headStep.1 = (oddTexK false true (wordParents (bl ++ [l])).1
      (wordParents (bl ++ [l])).2).2.2.2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext <;>
    simp [correctionJets, oddTexK, wordParents, h, transverseJet, kernelJet, texV1Even, texV2]

/-- Odd, `W_1` even, sign `-`: all four translations are the printed ones. -/
theorem odd_W1even_minus (bl : Word) (l : Digit) (h : phase (bl ++ [l]) = 0) :
    (correctionJets bl l .odd true).scan.1 = (oddTexK false false (wordParents (bl ++ [l])).1
      (wordParents (bl ++ [l])).2).1 ∧
    (correctionJets bl l .odd true).bridge.1 = (oddTexK false false (wordParents (bl ++ [l])).1
      (wordParents (bl ++ [l])).2).2.1 ∧
    (correctionJets bl l .odd true).headStart.1 = (oddTexK false false (wordParents (bl ++ [l])).1
      (wordParents (bl ++ [l])).2).2.2.1 ∧
    (correctionJets bl l .odd true).headStep.1 = (oddTexK false false (wordParents (bl ++ [l])).1
      (wordParents (bl ++ [l])).2).2.2.2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext <;>
    simp [correctionJets, oddTexK, wordParents, h, transverseJet, kernelJet, texV1Odd, texV1Even, texV2]

/-- Even, `W_1` odd, sign `+`: all four translations are the printed ones, with `s = 2` in `K_3` exactly when `l = 2`. -/
theorem even_W1odd_plus (bl : Word) (l : Digit) (h : phase (bl ++ [l]) = 1) :
    (correctionJets bl l .even false).scan.1 = (evenTexK true true (decide (l = .two)) (wordParents (bl ++ [l])).1
      (wordParents (bl ++ [l])).2).1 ∧
    (correctionJets bl l .even false).bridge.1 = (evenTexK true true (decide (l = .two)) (wordParents (bl ++ [l])).1
      (wordParents (bl ++ [l])).2).2.1 ∧
    (correctionJets bl l .even false).headStart.1 = (evenTexK true true (decide (l = .two))
      (wordParents (bl ++ [l])).1 (wordParents (bl ++ [l])).2).2.2.1 ∧
    (correctionJets bl l .even false).headStep.1 = (evenTexK true true (decide (l = .two))
      (wordParents (bl ++ [l])).1 (wordParents (bl ++ [l])).2).2.2.2 := by
  cases l <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> ext <;>
    simp [correctionJets, evenTexK, wordParents, h, transverseJet, kernelJet, texV1Odd, texV1Even, texV2] <;> ring

/-- Even, `W_1` even, sign `+`: all four translations are the printed ones. -/
theorem even_W1even_plus (bl : Word) (l : Digit) (h : phase (bl ++ [l]) = 0) :
    (correctionJets bl l .even false).scan.1 = (evenTexK false true (decide (l = .two)) (wordParents (bl ++ [l])).1
      (wordParents (bl ++ [l])).2).1 ∧
    (correctionJets bl l .even false).bridge.1 = (evenTexK false true (decide (l = .two)) (wordParents (bl ++ [l])).1
      (wordParents (bl ++ [l])).2).2.1 ∧
    (correctionJets bl l .even false).headStart.1 = (evenTexK false true (decide (l = .two))
      (wordParents (bl ++ [l])).1 (wordParents (bl ++ [l])).2).2.2.1 ∧
    (correctionJets bl l .even false).headStep.1 = (evenTexK false true (decide (l = .two))
      (wordParents (bl ++ [l])).1 (wordParents (bl ++ [l])).2).2.2.2 := by
  cases l <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> ext <;>
    simp [correctionJets, evenTexK, wordParents, h, transverseJet, kernelJet, texV1Odd, texV1Even, texV2]

/-- Even, `W_1` even, sign `-`: all four translations are the printed ones. -/
theorem even_W1even_minus (bl : Word) (l : Digit) (h : phase (bl ++ [l]) = 0) :
    (correctionJets bl l .even true).scan.1 = (evenTexK false false (decide (l = .two)) (wordParents (bl ++ [l])).1
      (wordParents (bl ++ [l])).2).1 ∧
    (correctionJets bl l .even true).bridge.1 = (evenTexK false false (decide (l = .two)) (wordParents (bl ++ [l])).1
      (wordParents (bl ++ [l])).2).2.1 ∧
    (correctionJets bl l .even true).headStart.1 = (evenTexK false false (decide (l = .two))
      (wordParents (bl ++ [l])).1 (wordParents (bl ++ [l])).2).2.2.1 ∧
    (correctionJets bl l .even true).headStep.1 = (evenTexK false false (decide (l = .two))
      (wordParents (bl ++ [l])).1 (wordParents (bl ++ [l])).2).2.2.2 := by
  cases l <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> ext <;>
    simp [correctionJets, evenTexK, wordParents, h, transverseJet, kernelJet, texV1Odd, texV1Even, texV2] <;> ring

/-- Even, `W_1` odd, sign `-`: `K_1`, `K_3`, `K_4` agree; the constructor's `K_2` is `-v_{q,1} + v_{p,2} - v_{q,2}`. -/
theorem even_W1odd_minus (bl : Word) (l : Digit) (h : phase (bl ++ [l]) = 1) :
    (correctionJets bl l .even true).scan.1 = (evenTexK true false (decide (l = .two)) (wordParents (bl ++ [l])).1
      (wordParents (bl ++ [l])).2).1 ∧
    (correctionJets bl l .even true).bridge.1 = -texV1Even (wordParents (bl ++ [l])).2 +
      texV2 (wordParents (bl ++ [l])).1 - texV2 (wordParents (bl ++ [l])).2 ∧
    (correctionJets bl l .even true).headStart.1 = (evenTexK true false (decide (l = .two))
      (wordParents (bl ++ [l])).1 (wordParents (bl ++ [l])).2).2.2.1 ∧
    (correctionJets bl l .even true).headStep.1 = (evenTexK true false (decide (l = .two))
      (wordParents (bl ++ [l])).1 (wordParents (bl ++ [l])).2).2.2.2 := by
  cases l <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> ext <;>
    simp [correctionJets, evenTexK, wordParents, h, transverseJet, kernelJet, texV1Odd, texV1Even, texV2]

end FLatticePaper.Tiles.LCorrections
