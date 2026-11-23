import FLatticePaper.Plane.Induction.W1NonfreeSheet
import FLatticePaper.Plane.Induction.W1Step
import FLatticePaper.Plane.Induction.SheetCharts
import FLatticePaper.Plane.Induction.I3Permits

/-! # Task 92: the nonfree A-side corner data of the sheet square (the `M`-versus-`A` correspondence)

At a strict `A` root (`Ψ c ≥ 1`) with its parent square `ParentSquareOut`, the unit bound of `Ψ` and monotonicity along the retained
return give `Ψ ≥ 0` at the three corners. At a corner `p` with `Ψ p ≥ 1` every input of `p` has `Ψ ≥ 0` (unit bound), so `M = min(A, C)`
equals `A` on the star of `p` and `laplacian M p = laplacian A p`. The `A`-laplacian is the parent laplacian at `zTurn (p − lv)`
(`zTurn = i3Z`). Corners with `Ψ = 0` are the tie corners, handled by `hagree_M_tie_of_inherited`, and are not claimed here. -/

namespace FLatticePaper.W1NonfreeHsq

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.AndOrRank
open FLatticePaper.W1Phase FLatticePaper.W1MSheet FLatticePaper.W1SheetSquare FLatticePaper.W1NonfreeOut
open FLatticePaper.W1NonfreeSheet FLatticePaper.W1Step FLatticePaper.W1Pointers

/-- The laplacian of a minimum equals that of the first field where the first field is the smaller at the site and at its inputs. -/
theorem lap_min_of_le (A C : Field) (x : Site) (hx : A x ≤ C x)
    (h1 : A (incomingNeg x) ≤ C (incomingNeg x)) (h2 : A (incomingPos x) ≤ C (incomingPos x)) :
    laplacian (fun z => min (A z) (C z)) x = laplacian A x := by
  simp only [laplacian, min_eq_left hx, min_eq_left h1, min_eq_left h2]

/-- The laplacian of the sheet `A` in parent coordinates. -/
theorem lap_sheetA (word : Word) (p : Site) :
    laplacian (fun z => (frameAt word).sheetA (FqW word) z) p =
      laplacian (standardField (conjWord word)) (zTurn (p - (frameAt word).sheetShift)) :=
  (laplacian_sub_even (FqW word) (frameAt word).sheetShift (frameAt word).evenSite_sheetShift p).trans
    (i3_laplacian_quarterTurn (standardField (conjWord word)) (p - (frameAt word).sheetShift))

/-- The unit bound of `Ψ` at an input. -/
theorem psi_unit_input {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    {c j : Site} (hE : Edge j c) : sheetPsi word c - 1 ≤ sheetPsi word j := by
  have h := sheetDiff_unit hw hSE c j hE
  have e1 : sheetPsi word c = sheetDiffW word c := rfl
  have e2 : sheetPsi word j = sheetDiffW word j := rfl
  rw [e1, e2]
  linarith [h.1]

/-- At a strict-enough site (`Ψ c ≥ 1`) every input has `Ψ ≥ 0`. -/
theorem psi_input_nonneg {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    {c j : Site} (hE : Edge j c) (hc : 1 ≤ sheetPsi word c) : 0 ≤ sheetPsi word j := by
  have := psi_unit_input hw hSE hE
  omega

/-- `Ψ` does not decrease along the `A`-retained edges. -/
theorem psi_mono {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    {seed : Site → Site → Prop} (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    {p q : Site} (h : sheetPolicyA P (frameAt word).sheetShift p q) : sheetPsi word p ≤ sheetPsi word q :=
  sheetDiff_mono_A hw hSE P h

/-- At a site with `Ψ ≥ 1`, the sheet minimum has the laplacian of `A`. -/
theorem lap_MW_eq_sheetA {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    {p : Site} (hp : 1 ≤ sheetPsi word p) :
    laplacian (MW word) p = laplacian (fun z => (frameAt word).sheetA (FqW word) z) p := by
  have hx : (frameAt word).sheetA (FqW word) p ≤ (frameAt word).sheetC (FqW word) p := by
    unfold sheetPsi at hp
    omega
  have h1 : (frameAt word).sheetA (FqW word) (incomingNeg p) ≤
      (frameAt word).sheetC (FqW word) (incomingNeg p) := by
    have h := psi_input_nonneg hw hSE (c := p) (j := incomingNeg p) (by unfold Edge; exact Or.inl rfl) hp
    unfold sheetPsi at h
    omega
  have h2 : (frameAt word).sheetA (FqW word) (incomingPos p) ≤
      (frameAt word).sheetC (FqW word) (incomingPos p) := by
    have h := psi_input_nonneg hw hSE (c := p) (j := incomingPos p) (by unfold Edge; exact Or.inr rfl) hp
    unfold sheetPsi at h
    omega
  exact lap_min_of_le (fun z => (frameAt word).sheetA (FqW word) z) (fun z => (frameAt word).sheetC (FqW word) z)
    p hx h1 h2

/-- The pointer of a site whose only retained input is `o` is `o`. -/
theorem pointer_of_unique (Q : Site → Site → Prop) (c o : Site)
    (ho : o = incomingNeg c ∨ o = incomingPos c) (hQ : Q c o) (hu : ∀ j, Q c j → j = o) :
    pointerOf Q c = o := by
  unfold pointerOf
  classical
  split_ifs with hn
  · exact hu _ hn
  · rcases ho with ho | ho
    · exact absurd (by rw [← ho]; exact hQ) hn
    · exact ho.symm

/-- A strict corner (`Ψ ≥ 1`) of the sheet square: its `M`-laplacian is that of the parent, with the `A`-pointer. -/
theorem corner_facts {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    {seed : Site → Site → Prop} (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    {p nx : Site} (hnx : Edge nx p) (hQ : sheetPolicyA P (frameAt word).sheetShift p nx)
    (hL : laplacian (standardField (conjWord word)) (zTurn (p - (frameAt word).sheetShift)) = -1 ∨
      (laplacian (standardField (conjWord word)) (zTurn (p - (frameAt word).sheetShift)) = 0 ∧
        ∀ j, sheetPolicyA P (frameAt word).sheetShift p j → j = nx))
    (hp : 1 ≤ sheetPsi word p) :
    laplacian (MW word) p = -1 ∨
      (laplacian (MW word) p = 0 ∧ pointerOf (sheetPolicyA P (frameAt word).sheetShift) p = nx) := by
  rw [lap_MW_eq_sheetA hw hSE hp, lap_sheetA word p]
  rcases hL with e | ⟨e, u⟩
  · exact Or.inl e
  · exact Or.inr ⟨e, pointer_of_unique _ p nx hnx hQ u⟩

/-- **The nonfree A-side corner data of the sheet square** (task 92). For a strict `A` root `c` (`Ψ c ≥ 1`) with its parent square: the
three corners have `Ψ ≥ 0`; each strict corner has the `M`-laplacian of its parent with the `A`-pointer to its successor; the rejected
input of `c` is its `A`-pointer. -/
theorem square_facts {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    {seed : Site → Site → Prop} (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    {c : Site} (hc : 1 ≤ sheetPsi word c)
    (h : ParentSquareOut (standardField (conjWord word)) P.retained (zTurn (c - (frameAt word).sheetShift))) :
    ∃ p0 p1 p2 : Site, ∃ a b : ℤ,
      c ∈ squareCorners a b ∧ p0 ∈ squareCorners a b ∧ p1 ∈ squareCorners a b ∧ p2 ∈ squareCorners a b ∧
      (∀ c' ∈ squareCorners a b, c' ≠ c → c' = p0 ∨ c' = p1 ∨ c' = p2) ∧
      (p0 = incomingNeg c ∨ p0 = incomingPos c) ∧
      0 ≤ sheetPsi word p0 ∧ 0 ≤ sheetPsi word p1 ∧ 0 ≤ sheetPsi word p2 ∧
      (1 ≤ sheetPsi word p0 → laplacian (MW word) p0 = -1 ∨
        (laplacian (MW word) p0 = 0 ∧ pointerOf (sheetPolicyA P (frameAt word).sheetShift) p0 = p1)) ∧
      (1 ≤ sheetPsi word p1 → laplacian (MW word) p1 = -1 ∨
        (laplacian (MW word) p1 = 0 ∧ pointerOf (sheetPolicyA P (frameAt word).sheetShift) p1 = p2)) ∧
      (1 ≤ sheetPsi word p2 → laplacian (MW word) p2 = -1 ∨
        (laplacian (MW word) p2 = 0 ∧ pointerOf (sheetPolicyA P (frameAt word).sheetShift) p2 = c)) ∧
      (∃ o' : Site, (o' = incomingNeg c ∨ o' = incomingPos c) ∧ o' ∉ squareCorners a b ∧
        pointerOf (sheetPolicyA P (frameAt word).sheetShift) c = o') := by
  have hlv := (frameAt word).evenSite_sheetShift
  obtain ⟨p0, p1, p2, o', a, b, hc0, hq0, hq1, hq2, hcov, hne01, hne12, hne02, hin0, hnot0, hE1, hE2, hE3,
    hR0, hR1, hR2, hoin, hoout, hRo, hun, hL0, hL1, hL2⟩ := sheet_squareOut_of_parent hlv c h
  have hp0 : 0 ≤ sheetPsi word p0 := psi_input_nonneg hw hSE (c := c) (j := p0) hin0 hc
  have hp1 : 0 ≤ sheetPsi word p1 := by
    have := psi_mono hw hSE P (p := p0) (q := p1) hR0
    omega
  have hp2 : 0 ≤ sheetPsi word p2 := by
    have := psi_mono hw hSE P (p := p1) (q := p2) hR1
    omega
  refine ⟨p0, p1, p2, a, b, hc0, hq0, hq1, hq2, hcov, hin0, hp0, hp1, hp2, ?_, ?_, ?_, ⟨o', hoin, hoout, ?_⟩⟩
  · intro hq
    exact corner_facts hw hSE P hE1 hR0 hL0 hq
  · intro hq
    exact corner_facts hw hSE P hE2 hR1 hL1 hq
  · intro hq
    exact corner_facts hw hSE P hE3 hR2 hL2 hq
  · exact pointer_of_unique (sheetPolicyA P (frameAt word).sheetShift) c o' hoin hRo hun

end FLatticePaper.W1NonfreeHsq
