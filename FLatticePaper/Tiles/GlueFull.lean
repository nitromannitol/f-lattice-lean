import FLatticePaper.Tiles.WeakStepAssembly
import FLatticePaper.Tiles.TileCompatInputs
import FLatticePaper.Tiles.SameParentStd

/-! # The glued weak odometers on the full copies (uncorrected children)

The weak odometer of a child that is not corrected is glued on the kept parts of the six copies of its decomposition
(`WeakStepAssembly.GluedChildren`); `keptPart` removes the overlaps of two copies of the same parent that are not a doubled pair.
`GlueFullInput` asks that the glue respect the full copies. The half-turn `x ↦ D - x` of the child permutes the copies
(odd child `(0 1)(2 5)(3 4)`, even child `(0 3)(1 2)(4 5)`; numerics `tmp-w6/chk14.py`), and every removed overlap that is not
empty is a swapped pair (`tmp-w6/chk13.py`).

`SameParentInput` is the geometric part of Case 1 of the proof of `lemma:tile-odometer-existence`, stated here, not proved: at a
child that is not corrected, the two copies of one parent that the half-turn does not swap do not meet (the bounds by the strip
functionals `N_r`), and the two copies that it swaps are compatible (their overlap is a copy of the grandparent tile in both
decompositions, with the same affine factor; the base cases by the explicit formulas). -/

namespace FLatticePaper.Tiles.GlueFull

open FLatticePaper.Farey
open FLatticePaper.Tiles
open FLatticePaper.Tiles.JointFamily
open FLatticePaper.Tiles.JointInduction (GoodBelow)
open FLatticePaper.Tiles.TileCompatInputs (PairCompat)
open FLatticePaper.Tiles.WeakStepPaper (paperS)
open FLatticePaper.Tiles.Standard (IsBase)

/-- The entries `i` and `j` of a decomposition have disjoint placed domains. Vacuous when an entry is missing. -/
def PairDisjoint (ps : List Piece) (i j : ℕ) : Prop :=
  ∀ p q : Piece, ps[i]? = some p → ps[j]? = some q → Disjoint p.placed q.placed

/-- The full tile decomposition of the odd child of `w` over the family below `w` (the paper data). -/
abbrev oddFull (f : Word → JSlice) (w : Word) : List Piece :=
  tileOddPieces paperS (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven) (fun u => (below f w u).lEven) w

/-- The full tile decomposition of the even child of `w` over the family below `w` (the paper data). -/
abbrev evenFull (f : Word → JSlice) (w : Word) : List Piece :=
  tileEvenPieces paperS (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven) (fun u => (below f w u).lOdd) w

/-- **Case 1 of the proof of `lemma:tile-odometer-existence`, geometric part**: at a child that is not corrected, the copies of one
parent that are not a doubled pair either do not meet (the pairs the half-turn of the child does not swap: odd `(2,4)`, `(3,5)`;
even `(0,2)`, `(1,3)`) or are compatible (the swapped pairs: odd `(0,1)`, `(3,4)`, `(2,5)`; even `(0,3)`, `(1,2)`, `(4,5)`). -/
def SameParentInput (D : JointData) : Prop :=
  ∀ (f : Word → JSlice) (w : Word), GoodBelow D f w.length → ¬ IsBase w →
    (¬ CorrectedAfterThree w →
      PairDisjoint (oddFull f w) 2 4 ∧ PairDisjoint (oddFull f w) 3 5 ∧
        PairCompat (oddFull f w) 0 1 ∧ PairCompat (oddFull f w) 3 4 ∧ PairCompat (oddFull f w) 2 5) ∧
    (¬ CorrectedAfterTwo w →
      PairDisjoint (evenFull f w) 0 2 ∧ PairDisjoint (evenFull f w) 1 3 ∧
        PairCompat (evenFull f w) 0 3 ∧ PairCompat (evenFull f w) 1 2 ∧ PairCompat (evenFull f w) 4 5)

/-! ### The half-turn argument for six pieces

`g k` is the placed piece `k` (with its constant) on the copy `C k`; `x ↦ D - x` sends copy `k` to copy `σ k`, and the half-turn
of the parent tile gives `2 g_{σ k}(D - x) = 2 g_k(x) - 2 a^T x + K_k` on copy `k` (`a` the second affine factor of the child).
Two copies that agree on their overlap, with images that agree on theirs, have the same constant; a swapped pair with equal
constants that differs by a constant on its overlap agrees there (the difference `c` satisfies `2 c = -2 c`). -/

section HalfTurn

variable (g : ℕ → Site → ℤ) (C : ℕ → Set Site) (D a : Site) (σ : ℕ → ℕ)

/-- Two pieces agree on the overlap of their copies. -/
def AgreeOn (k l : ℕ) : Prop := ∀ x ∈ C k, x ∈ C l → g k x = g l x

/-- The half-turn relation of the six pieces, with the constants `K`. -/
def HalfTurnRel (K : ℕ → ℤ) : Prop :=
  ∀ k < 6, ∀ x ∈ C k, D - x ∈ C (σ k) ∧ 2 * g (σ k) (D - x) = 2 * g k x - 2 * dotS a x + K k

variable {g C D a σ}

theorem agreeOn_symm {k l : ℕ} (h : AgreeOn g C k l) : AgreeOn g C l k :=
  fun x hl hk => (h x hk hl).symm

/-- **Overlapping copies that agree have the same constant**, when their images agree too. -/
theorem const_eq {K : ℕ → ℤ} (hK : HalfTurnRel g C D a σ K) {k l : ℕ} (hk : k < 6) (hl : l < 6) (x : Site)
    (hxk : x ∈ C k) (hxl : x ∈ C l) (h1 : AgreeOn g C k l) (h2 : AgreeOn g C (σ k) (σ l)) : K k = K l := by
  obtain ⟨m1, e1⟩ := hK k hk x hxk
  obtain ⟨m2, e2⟩ := hK l hl x hxl
  have f1 := h1 x hxk hxl
  have f2 := h2 (D - x) m1 m2
  linarith

/-- **A swapped pair agrees on its overlap**: if the half-turn exchanges the copies `i` and `σ i`, their constants are equal,
and the two pieces differ by a constant `c` on the overlap, then `c = 0`. -/
theorem swapped_agree {K : ℕ → ℤ} (hK : HalfTurnRel g C D a σ K) {i : ℕ} (hi : i < 6) (hs : σ i < 6)
    (hss : σ (σ i) = i) (hKi : K i = K (σ i)) (c : ℤ) (hc : ∀ x ∈ C i, x ∈ C (σ i) → g i x - g (σ i) x = c) :
    AgreeOn g C i (σ i) := by
  intro x hx hx'
  obtain ⟨m1, e1⟩ := hK i hi x hx
  obtain ⟨m2, e2⟩ := hK (σ i) hs x hx'
  rw [hss] at m2 e2
  have c1 := hc x hx hx'
  have c2 := hc (D - x) m2 m1
  have hc0 : c = 0 := by linarith
  linarith

end HalfTurn

/-! ### One placed piece under the half-turn -/

theorem mem_shiftS' (S : Set Site) (a z : Site) : z ∈ SiteInduction.shiftS S a ↔ z - a ∈ S := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨z - a, h, by simp⟩

/-- **A placed piece under the half-turn of the child**: the register `R` with the half-turn `y ↦ D_r - y` (affine factor `a_r`),
placed at `u` with affine factor `η` and at `u'` with `η'`, where `u + u' + D_r = D` and `η + η' + a_r = a`: the second placement
at `D - x` is the first at `x` up to `-a^T x` and a constant (doubled). -/
theorem placed_rel (R : PartialOdometer) (Dr ar : Site)
    (hR : ∀ y ∈ R.dom, Dr - y ∈ R.dom ∧ 2 * (R.val (Dr - y) - R.val y) = dotS ar Dr - 2 * dotS ar y)
    (u u' η η' D a : Site) (hu : u + u' + Dr = D) (hη : η + η' + ar = a) (κ κ' : ℤ) :
    ∃ K : ℤ, ∀ x, x - u ∈ R.dom → D - x - u' ∈ R.dom ∧
      2 * (R.val (D - x - u') + dotS η' (D - x) + κ') = 2 * (R.val (x - u) + dotS η x + κ) - 2 * dotS a x + K := by
  refine ⟨dotS ar Dr + 2 * dotS ar u + 2 * dotS η' D + 2 * κ' - 2 * κ, fun x hx => ?_⟩
  have e : D - x - u' = Dr - (x - u) := by
    rw [← hu]; abel
  obtain ⟨hm, he⟩ := hR (x - u) hx
  rw [e]
  refine ⟨hm, ?_⟩
  have h1 : η.1 + η'.1 + ar.1 = a.1 := by rw [← hη]; rfl
  have h2 : η.2 + η'.2 + ar.2 = a.2 := by rw [← hη]; rfl
  simp only [dotS, Prod.fst_sub, Prod.snd_sub] at he ⊢
  linear_combination he + (-2 * x.1) * h1 + (-2 * x.2) * h2

/-- **One copy under the half-turn**: a copy `C_k` of the register `R` at `u_k` and its image `C_{σ k}` at `u_{σ k}`, with the
pieces `g_k`, `g_{σ k}` placed from `R`, satisfy the half-turn relation of `HalfTurnRel` at copy `k`. -/
theorem rel_part (R : PartialOdometer) (Dr ar : Site)
    (hR : ∀ y ∈ R.dom, Dr - y ∈ R.dom ∧ 2 * (R.val (Dr - y) - R.val y) = dotS ar Dr - 2 * dotS ar y)
    (uk us ηk ηs D a : Site) (hu : uk + us + Dr = D) (hη : ηk + ηs + ar = a) (κk κs : ℤ) (Ck Cs : Set Site)
    (hCk : ∀ x, x ∈ Ck ↔ x - uk ∈ R.dom) (hCs : ∀ x, x ∈ Cs ↔ x - us ∈ R.dom) (gk gs : Site → ℤ)
    (hgk : ∀ x, gk x = R.val (x - uk) + dotS ηk x + κk) (hgs : ∀ x, gs x = R.val (x - us) + dotS ηs x + κs) :
    ∃ K : ℤ, ∀ x ∈ Ck, D - x ∈ Cs ∧ 2 * gs (D - x) = 2 * gk x - 2 * dotS a x + K := by
  obtain ⟨K, hK⟩ := placed_rel R Dr ar hR uk us ηk ηs D a hu hη κk κs
  refine ⟨K, fun x hx => ?_⟩
  obtain ⟨hm, he⟩ := hK x ((hCk x).1 hx)
  exact ⟨(hCs _).2 hm, by rw [hgs, hgk]; exact he⟩

/-! ### The odd child -/

open FLatticePaper.Construction (texV1Odd texV1Even texV2)
open FLatticePaper.Tiles.ChildGlue (oddP oddQ evenP evenQ pieceSet)
open FLatticePaper.Tiles.ClosedPathAssembly (placedOdd placedEven affOdd affEven)
open FLatticePaper.Tiles.SurgicalWeak (regsAt regOdo)

/-- The half-turn of the odd child on its six copies: `P^+ ↔ P^-`, `Q^{+,1} ↔ Q^{-,2}`, `Q^{+,2} ↔ Q^{-,1}`. -/
def σO : ℕ → ℕ
  | 0 => 1 | 1 => 0 | 2 => 5 | 3 => 4 | 4 => 3 | 5 => 2 | n => n

/-- The offset of copy `k` of the odd child. -/
def offO (w : Word) (k : ℕ) : Site := if k < 2 then (oddP w).getD k 0 else (oddQ w).getD (k - 2) 0

/-- The centre `D = v_1 + v_2 + 1 - i` of a fraction (odd: `v_1 = texV1Odd`). -/
def cenO (f : Fraction) : Site := texV1Odd f + texV2 f + ((1 : ℤ), (-1 : ℤ))
/-- The centre of an even fraction. -/
def cenE (f : Fraction) : Site := texV1Even f + texV2 f + ((1 : ℤ), (-1 : ℤ))

/-- The offsets and affine factors of the copies of the odd child under the half-turn: `u_k + u_{σ k} + D_r = D_{p_0}` and
`η_k + η_{σ k} + a_{r,2} = a_{p_0,2}` (`r` the register of copy `k`; text, end of the proof of (b)). -/
theorem odd_alg (w : Word) (k : ℕ) (hk : k < 6) :
    offO w k + offO w (σO k) + (if k < 2 then cenO (parentsAt w).odd else cenE (parentsAt w).even) =
        cenO ((parentsAt w).current .odd) ∧
      affOdd (parentsAt w).odd (parentsAt w).even k + affOdd (parentsAt w).odd (parentsAt w).even (σO k) +
          (if k < 2 then offsetA (parentsAt w).odd.num (parentsAt w).odd.den true
            else offsetA (parentsAt w).even.num (parentsAt w).even.den true) =
        offsetA ((parentsAt w).current .odd).num ((parentsAt w).current .odd).den true := by
  interval_cases k <;> cases h : (phase w == 1) <;>
    simp only [offO, σO, oddP, oddQ, MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, h, cenO, cenE, affOdd,
      Parents.current, Parents.combine, offsetA, if_true, if_false, Bool.false_eq_true, List.getD_cons_zero,
      List.getD_cons_succ, Nat.reduceSub, Nat.lt_irrefl, Nat.one_lt_ofNat, Nat.zero_lt_two, Nat.reduceLT, Nat.reduceEqDiff,
      or_self, or_true, true_or, OfNat.ofNat_ne_one, zero_ne_one] <;>
    refine ⟨?_, ?_⟩ <;> ext <;>
    simp [texV1Odd, texV1Even, texV2] <;> ring

theorem σO_lt (k : ℕ) (hk : k < 6) : σO k < 6 ∧ σO (σO k) = k ∧ (k < 2 ↔ σO k < 2) := by
  interval_cases k <;> simp [σO]

theorem memC_odd (w : Word) (T1 T2 : Set Site) (k : ℕ) (_hk : k < 6) (x : Site) :
    x ∈ pieceSet (oddP w) (oddQ w) T1 T2 k ↔ x - offO w k ∈ (if k < 2 then T1 else T2) := by
  unfold pieceSet offO
  rw [ClosedPathCycle.oddP_length]
  by_cases h : k < 2
  · simp only [if_pos h, mem_shiftS']
  · simp only [if_neg h, mem_shiftS']

theorem placedOdd_eq (w : Word) (oP oQ : Site → ℤ) (κ : ℕ → ℤ) (k : ℕ) (x : Site) :
    placedOdd w oP oQ 0 k x + κ k = (if k < 2 then oP else oQ) (x - offO w k) +
      dotS (affOdd (parentsAt w).odd (parentsAt w).even k) x + κ k := by
  unfold placedOdd offO
  by_cases h : k < 2 <;> simp [h, ClosedPathSum.dot2, dotS]

/-- **The half-turn relation of the odd child**, from the half-turns of the two registers. -/
theorem odd_rel (w : Word) (P Q : PartialOdometer) (κ : ℕ → ℤ)
    (hP : ∀ y ∈ P.dom, cenO (parentsAt w).odd - y ∈ P.dom ∧
      2 * (P.val (cenO (parentsAt w).odd - y) - P.val y) =
        dotS (offsetA (parentsAt w).odd.num (parentsAt w).odd.den true) (cenO (parentsAt w).odd) -
          2 * dotS (offsetA (parentsAt w).odd.num (parentsAt w).odd.den true) y)
    (hQ : ∀ y ∈ Q.dom, cenE (parentsAt w).even - y ∈ Q.dom ∧
      2 * (Q.val (cenE (parentsAt w).even - y) - Q.val y) =
        dotS (offsetA (parentsAt w).even.num (parentsAt w).even.den true) (cenE (parentsAt w).even) -
          2 * dotS (offsetA (parentsAt w).even.num (parentsAt w).even.den true) y) :
    ∃ K : ℕ → ℤ, HalfTurnRel (fun k z => placedOdd w P.val Q.val 0 k z + κ k)
      (pieceSet (oddP w) (oddQ w) ↑P.dom ↑Q.dom) (cenO ((parentsAt w).current .odd))
      (offsetA ((parentsAt w).current .odd).num ((parentsAt w).current .odd).den true) σO K := by
  have h : ∀ k, k < 6 → ∃ Kk : ℤ, ∀ x ∈ pieceSet (oddP w) (oddQ w) ↑P.dom ↑Q.dom k,
      cenO ((parentsAt w).current .odd) - x ∈ pieceSet (oddP w) (oddQ w) ↑P.dom ↑Q.dom (σO k) ∧
      2 * (placedOdd w P.val Q.val 0 (σO k) (cenO ((parentsAt w).current .odd) - x) + κ (σO k)) =
        2 * (placedOdd w P.val Q.val 0 k x + κ k) -
          2 * dotS (offsetA ((parentsAt w).current .odd).num ((parentsAt w).current .odd).den true) x + Kk := by
    intro k hk
    obtain ⟨hs6, -, hs2⟩ := σO_lt k hk
    obtain ⟨hu, hη⟩ := odd_alg w k hk
    by_cases hk2 : k < 2
    · have hs : σO k < 2 := hs2.1 hk2
      rw [if_pos hk2] at hu hη
      refine rel_part P _ _ hP _ _ _ _ _ _ hu hη (κ k) (κ (σO k)) (pieceSet (oddP w) (oddQ w) ↑P.dom ↑Q.dom k)
        (pieceSet (oddP w) (oddQ w) ↑P.dom ↑Q.dom (σO k)) (fun x => ?_) (fun x => ?_)
        (fun z => placedOdd w P.val Q.val 0 k z + κ k) (fun z => placedOdd w P.val Q.val 0 (σO k) z + κ (σO k))
        (fun x => ?_) (fun x => ?_)
      · rw [memC_odd w _ _ k hk x, if_pos hk2]; rfl
      · rw [memC_odd w _ _ (σO k) hs6 x, if_pos hs]; rfl
      · rw [placedOdd_eq, if_pos hk2]
      · rw [placedOdd_eq, if_pos hs]
    · have hs : ¬ σO k < 2 := fun h => hk2 (hs2.2 h)
      rw [if_neg hk2] at hu hη
      refine rel_part Q _ _ hQ _ _ _ _ _ _ hu hη (κ k) (κ (σO k)) (pieceSet (oddP w) (oddQ w) ↑P.dom ↑Q.dom k)
        (pieceSet (oddP w) (oddQ w) ↑P.dom ↑Q.dom (σO k)) (fun x => ?_) (fun x => ?_)
        (fun z => placedOdd w P.val Q.val 0 k z + κ k) (fun z => placedOdd w P.val Q.val 0 (σO k) z + κ (σO k))
        (fun x => ?_) (fun x => ?_)
      · rw [memC_odd w _ _ k hk x, if_neg hk2]; rfl
      · rw [memC_odd w _ _ (σO k) hs6 x, if_neg hs]; rfl
      · rw [placedOdd_eq, if_neg hk2]
      · rw [placedOdd_eq, if_neg hs]
  choose! K hK using h
  exact ⟨K, fun k hk x hx => by
    obtain ⟨h1, h2⟩ := hK k hk x hx
    exact ⟨h1, by linarith⟩⟩

/-! ### The full decomposition of the odd child and the placed copies -/

theorem offO_eq (w : Word) :
    p0Off w .p1Plus = offO w 0 ∧ p0Off w .p1Minus = offO w 1 ∧ p0Off w .q1DPlus = offO w 2 ∧
      p0Off w .q1DPlus + vQ1 w = offO w 3 ∧ p0Off w .q1DMinus = offO w 4 ∧ p0Off w .q1DMinus + vQ1 w = offO w 5 := by
  cases h : (phase w == 1) <;>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [p0Off, offO, oddP, oddQ, MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, SurgicalDict.offsetP0, W1Odd,
      vP1, vP2, vQ1, vQ2, h]

theorem affO_eq (w : Word) :
    p0Aff w .p1Plus = affOdd (parentsAt w).odd (parentsAt w).even 0 ∧
      p0Aff w .p1Minus = affOdd (parentsAt w).odd (parentsAt w).even 1 ∧
      p0Aff w .q1DPlus = affOdd (parentsAt w).odd (parentsAt w).even 2 ∧
      p0Aff w .q1DPlus = affOdd (parentsAt w).odd (parentsAt w).even 3 ∧
      p0Aff w .q1DMinus = affOdd (parentsAt w).odd (parentsAt w).even 4 ∧
      p0Aff w .q1DMinus = affOdd (parentsAt w).odd (parentsAt w).even 5 := by
  cases h : W1Odd w <;>
    simp only [p0Aff, h, affOdd, pairAffine, offsetA, if_true, if_false, Bool.false_eq_true] <;>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ext <;> simp

/-- At a child that is not corrected, the full decomposition of the odd child consists of the six copies of the registers at
the offsets `offO` with the affine factors `affOdd`. -/
theorem oddFull_get (f : Word → JSlice) (w u1 u2 : Word) (hw : ¬ IsBase w) (hreg : regsAt w = (some u1, some u2))
    (hc : ¬ CorrectedAfterThree w) (hl1 : u1.length < w.length) (hl2 : u2.length < w.length) (k : ℕ) (hk : k < 6) :
    (oddFull f w)[k]? = some (stdPiece (if k < 2 then (f u1).tOdd else (f u2).tEven) (offO w k)
      (affOdd (parentsAt w).odd (parentsAt w).even k)) := by
  have hcorr : decide (w.getLast? = some Digit.three) = false := by
    simp only [decide_eq_false_iff_not]
    exact fun h => hc ⟨hw, h⟩
  have hb1 : below f w u1 = f u1 := by simp only [below, if_pos hl1]
  have hb2 : below f w u2 = f u2 := by simp only [below, if_pos hl2]
  obtain ⟨o0, o1, o2, o3, o4, o5⟩ := offO_eq w
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := affO_eq w
  have hL : oddFull f w = [stdPiece (f u1).tOdd (offO w 0) (affOdd (parentsAt w).odd (parentsAt w).even 0),
      stdPiece (f u1).tOdd (offO w 1) (affOdd (parentsAt w).odd (parentsAt w).even 1),
      stdPiece (f u2).tEven (offO w 2) (affOdd (parentsAt w).odd (parentsAt w).even 2),
      stdPiece (f u2).tEven (offO w 3) (affOdd (parentsAt w).odd (parentsAt w).even 3),
      stdPiece (f u2).tEven (offO w 4) (affOdd (parentsAt w).odd (parentsAt w).even 4),
      stdPiece (f u2).tEven (offO w 5) (affOdd (parentsAt w).odd (parentsAt w).even 5)] := by
    simp only [oddFull, tileOddPieces, hreg, regOdo, hb1, hb2, hcorr, Bool.false_and, Bool.false_eq_true, if_false]
    rw [o3, o5, o0, o1, o2, o4, a0, a1, a2, a4, a3.symm.trans a2, a5.symm.trans a4]
  rw [hL]
  interval_cases k <;> simp

/-! ### Corner points and the raw half-turn of a register -/

/-- The eight corner points of a standard tile with lattice vectors `X`, `Y` (`TileTranslation.StdCornerValues`). -/
def Corners (T : Finset Site) (X Y : Site) : Prop :=
  (0 : Site) ∈ T ∧ ((1 : ℤ), (0 : ℤ)) ∈ T ∧ X - ((0 : ℤ), (1 : ℤ)) ∈ T ∧ X ∈ T ∧ Y + ((1 : ℤ), (0 : ℤ)) ∈ T ∧
    Y + ((1 : ℤ), (-1 : ℤ)) ∈ T ∧ X + Y + ((1 : ℤ), (-1 : ℤ)) ∈ T ∧ X + Y + ((1 : ℤ), (-1 : ℤ)) - ((1 : ℤ), (0 : ℤ)) ∈ T

theorem corners_of (o : PartialOdometer) (α : Site) (β : ℤ) (X Y e : Site)
    (h : TileTranslation.StdCornerValues o α β X Y e) : Corners o.dom X Y := by
  obtain ⟨⟨h1, -⟩, ⟨h2, -⟩, ⟨h3, -⟩, ⟨h4, -⟩, ⟨h5, -⟩, ⟨h6, -⟩, ⟨h7, -⟩, ⟨h8, -⟩⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- The half-turn of a tile odometer normalised with slope `0`, without the normalisation. -/
theorem raw_halfTurn (o : PartialOdometer) (v1 v2 a2 : Site) (h : TileHalfTurn o v1 v2 a2) (β' : ℤ)
    (hz : FirstTileNormal o 0 β') :
    ∀ y ∈ o.dom, v1 + v2 + ((1 : ℤ), (-1 : ℤ)) - y ∈ o.dom ∧
      2 * (o.val (v1 + v2 + ((1 : ℤ), (-1 : ℤ)) - y) - o.val y) =
        dotS a2 (v1 + v2 + ((1 : ℤ), (-1 : ℤ))) - 2 * dotS a2 y := by
  obtain ⟨α, β, hN, hH⟩ := h
  obtain ⟨hα, -⟩ := WeakStepAssembly.normal_unique o α 0 β β' hN hz
  subst hα
  intro y hy
  obtain ⟨hm, he⟩ := hH y hy
  refine ⟨hm, ?_⟩
  simp only [normed, dotS, Prod.fst_zero, Prod.snd_zero, zero_mul, add_zero, sub_zero] at he ⊢
  linarith

/-! ### The constants of the odd child are equal on the swapped pairs -/

theorem offO_vals (w : Word) :
    ((phase w == 1) = false → offO w 0 = texV1Even (parentsAt w).even + texV1Even (parentsAt w).even ∧
      offO w 1 = texV2 (parentsAt w).even ∧ offO w 2 = 0 ∧ offO w 3 = texV1Even (parentsAt w).even ∧
      offO w 4 = texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd ∧
      offO w 5 = texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∧
    ((phase w == 1) = true → offO w 0 = 0 ∧
      offO w 1 = texV1Even (parentsAt w).even + texV1Even (parentsAt w).even + texV2 (parentsAt w).even ∧
      offO w 2 = texV1Odd (parentsAt w).odd ∧ offO w 3 = texV1Odd (parentsAt w).odd + texV1Even (parentsAt w).even ∧
      offO w 4 = texV2 (parentsAt w).odd ∧ offO w 5 = texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) := by
  refine ⟨fun h => ?_, fun h => ?_⟩ <;>
    simp [offO, oddP, oddQ, MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, h]

/-- **The constants of the swapped pairs of the odd child are equal**: along a spanning tree of overlaps of copies that agree
(copies of different registers, and the two copies of a doubled piece), with witnesses at corner points of the register tiles
(`tmp-w6/chk17.py`). -/
theorem oddK (w : Word) (F : ℕ → Site → ℤ) (PT QT : Finset Site) (Dc a : Site) (K : ℕ → ℤ)
    (hK : HalfTurnRel F (pieceSet (oddP w) (oddQ w) ↑PT ↑QT) Dc a σO K)
    (hmix : ∀ k l, k < 2 → 2 ≤ l → l < 6 → AgreeOn F (pieceSet (oddP w) (oddQ w) ↑PT ↑QT) k l)
    (h23 : AgreeOn F (pieceSet (oddP w) (oddQ w) ↑PT ↑QT) 2 3)
    (h45 : AgreeOn F (pieceSet (oddP w) (oddQ w) ↑PT ↑QT) 4 5)
    (hcP : Corners PT (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd))
    (hcQ : Corners QT (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)) :
    K 0 = K 1 ∧ K 3 = K 4 ∧ K 2 = K 5 := by
  have mP : ∀ k x, k < 2 → x - offO w k ∈ PT → x ∈ pieceSet (oddP w) (oddQ w) ↑PT ↑QT k := fun k x hk h =>
    (memC_odd w _ _ k (by omega) x).2 (by rw [if_pos hk]; exact h)
  have mQ : ∀ k x, 2 ≤ k → k < 6 → x - offO w k ∈ QT → x ∈ pieceSet (oddP w) (oddQ w) ↑PT ↑QT k := fun k x hk hk6 h =>
    (memC_odd w _ _ k hk6 x).2 (by rw [if_neg (by omega)]; exact h)
  have mx' : ∀ k l, k < 2 → 2 ≤ l → l < 6 → AgreeOn F (pieceSet (oddP w) (oddQ w) ↑PT ↑QT) l k :=
    fun k l hk hl hl6 => agreeOn_symm (hmix k l hk hl hl6)
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7⟩ := hcP
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7⟩ := hcQ
  obtain ⟨hE, hO⟩ := offO_vals w
  cases h : (phase w == 1)
  · obtain ⟨o0, o1, o2, o3, o4, o5⟩ := hE h
    have e03 := const_eq hK (k := 0) (l := 3) (by omega) (by omega)
      (texV1Even (parentsAt w).even + texV1Even (parentsAt w).even)
      (mP 0 _ (by omega) (by rw [o0, sub_self]; exact c0))
      (mQ 3 _ (by omega) (by omega) (by rw [o3]; convert d3 using 1; abel))
      (hmix 0 3 (by omega) (by omega) (by omega)) (hmix 1 4 (by omega) (by omega) (by omega))
    have e23 := const_eq hK (k := 2) (l := 3) (by omega) (by omega)
      (texV1Even (parentsAt w).even + texV2 (parentsAt w).even + ((1 : ℤ), (-1 : ℤ)))
      (mQ 2 _ (by omega) (by omega) (by rw [o2, sub_zero]; exact d6))
      (mQ 3 _ (by omega) (by omega) (by rw [o3]; convert d5 using 1; abel))
      h23 (agreeOn_symm h45)
    have e14 := const_eq hK (k := 1) (l := 4) (by omega) (by omega)
      (texV2 (parentsAt w).even + (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + ((1 : ℤ), (-1 : ℤ))))
      (mP 1 _ (by omega) (by rw [o1]; convert c6 using 1; abel))
      (mQ 4 _ (by omega) (by omega) (by rw [o4]; convert d5 using 1; abel))
      (hmix 1 4 (by omega) (by omega) (by omega)) (hmix 0 3 (by omega) (by omega) (by omega))
    have e45 := const_eq hK (k := 4) (l := 5) (by omega) (by omega)
      (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd +
        (texV1Even (parentsAt w).even + texV2 (parentsAt w).even + ((1 : ℤ), (-1 : ℤ))))
      (mQ 4 _ (by omega) (by omega) (by rw [o4]; convert d6 using 1; abel))
      (mQ 5 _ (by omega) (by omega) (by rw [o5]; convert d5 using 1; abel))
      h45 (agreeOn_symm h23)
    have e05 := const_eq hK (k := 0) (l := 5) (by omega) (by omega)
      (texV1Even (parentsAt w).even + texV1Even (parentsAt w).even +
        (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + ((1 : ℤ), (-1 : ℤ)) - ((1 : ℤ), (0 : ℤ))))
      (mP 0 _ (by omega) (by rw [o0]; convert c7 using 1; abel))
      (mQ 5 _ (by omega) (by omega) (by rw [o5]; convert d2 using 1; ext <;> simp <;> ring))
      (hmix 0 5 (by omega) (by omega) (by omega)) (hmix 1 2 (by omega) (by omega) (by omega))
    exact ⟨by omega, by omega, by omega⟩
  · obtain ⟨o0, o1, o2, o3, o4, o5⟩ := hO h
    have e02 := const_eq hK (k := 0) (l := 2) (by omega) (by omega) (texV1Odd (parentsAt w).odd)
      (mP 0 _ (by omega) (by rw [o0, sub_zero]; exact c3))
      (mQ 2 _ (by omega) (by omega) (by rw [o2, sub_self]; exact d0))
      (hmix 0 2 (by omega) (by omega) (by omega)) (hmix 1 5 (by omega) (by omega) (by omega))
    have e23 := const_eq hK (k := 2) (l := 3) (by omega) (by omega)
      (texV1Odd (parentsAt w).odd + (texV1Even (parentsAt w).even + texV2 (parentsAt w).even + ((1 : ℤ), (-1 : ℤ))))
      (mQ 2 _ (by omega) (by omega) (by rw [o2]; convert d6 using 1; abel))
      (mQ 3 _ (by omega) (by omega) (by rw [o3]; convert d5 using 1; abel))
      h23 (agreeOn_symm h45)
    have e15 := const_eq hK (k := 1) (l := 5) (by omega) (by omega)
      (texV1Even (parentsAt w).even + texV1Even (parentsAt w).even + texV2 (parentsAt w).even +
        (texV2 (parentsAt w).odd + ((1 : ℤ), (-1 : ℤ))))
      (mP 1 _ (by omega) (by rw [o1]; convert c5 using 1; abel))
      (mQ 5 _ (by omega) (by omega) (by rw [o5]; convert d6 using 1; abel))
      (hmix 1 5 (by omega) (by omega) (by omega)) (hmix 0 2 (by omega) (by omega) (by omega))
    have e45 := const_eq hK (k := 4) (l := 5) (by omega) (by omega)
      (texV2 (parentsAt w).odd + (texV1Even (parentsAt w).even + texV2 (parentsAt w).even + ((1 : ℤ), (-1 : ℤ))))
      (mQ 4 _ (by omega) (by omega) (by rw [o4]; convert d6 using 1; abel))
      (mQ 5 _ (by omega) (by omega) (by rw [o5]; convert d5 using 1; abel))
      h45 (agreeOn_symm h23)
    have e04 := const_eq hK (k := 0) (l := 4) (by omega) (by omega)
      (texV2 (parentsAt w).odd + ((1 : ℤ), (0 : ℤ)))
      (mP 0 _ (by omega) (by rw [o0, sub_zero]; exact c4))
      (mQ 4 _ (by omega) (by omega) (by rw [o4]; convert d1 using 1; abel))
      (hmix 0 4 (by omega) (by omega) (by omega)) (hmix 1 3 (by omega) (by omega) (by omega))
    exact ⟨by omega, by omega, by omega⟩

/-! ### From agreement on every overlap to the full decomposition (odd child) -/

theorem mem_placed_std (o : PartialOdometer) (off aff x : Site) :
    x ∈ (stdPiece o off aff).placed ↔ x - off ∈ o.dom := by
  simp only [Piece.placed, stdPiece, Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨x - off, h, by simp⟩

/-- The odd child tile is the union of its six copies. -/
theorem oddTile_union (w u1 u2 : Word) (hw : ¬ IsBase w) (hT1 : (Standard.stateAt w).tOdd = Standard.oddTile u1)
    (hT2 : (Standard.stateAt w).tEven = Standard.evenTile u2) (x : Site) :
    x ∈ Standard.oddTile w ↔ ∃ k < 6, x - offO w k ∈ (if k < 2 then Standard.oddTile u1 else Standard.evenTile u2) := by
  have ho : Standard.oddTile w = Standard.oddChildB (phase w == 1) (Standard.oddTile u1) (Standard.evenTile u2)
      (parentsAt w).odd (parentsAt w).even := by
    show (Standard.childTiles w (Standard.stateAt w)).1 = _
    rw [SiteInduction.childTiles_nonbase w hw, hT1, hT2, Standard.stateAt_par]
  rw [ho]
  obtain ⟨hE, hO⟩ := offO_vals w
  constructor
  · intro hx
    cases h : (phase w == 1)
    · obtain ⟨o0, o1, o2, o3, o4, o5⟩ := hE h
      simp only [h, Standard.oddChildB, Finset.mem_union, Standard.mem_shift] at hx
      rcases hx with ((((hx | hx) | hx) | hx) | hx) | hx
      · exact ⟨2, by omega, by rw [o2]; simpa using hx⟩
      · exact ⟨3, by omega, by rw [o3]; simpa using hx⟩
      · exact ⟨4, by omega, by rw [o4]; simpa using hx⟩
      · exact ⟨5, by omega, by rw [o5]; simpa using hx⟩
      · exact ⟨0, by omega, by rw [o0]; simpa using hx⟩
      · exact ⟨1, by omega, by rw [o1]; simpa using hx⟩
    · obtain ⟨o0, o1, o2, o3, o4, o5⟩ := hO h
      simp only [h, Standard.oddChildB, Finset.mem_union, Standard.mem_shift] at hx
      rcases hx with ((((hx | hx) | hx) | hx) | hx) | hx
      · exact ⟨2, by omega, by rw [o2]; simpa using hx⟩
      · exact ⟨3, by omega, by rw [o3]; simpa using hx⟩
      · exact ⟨4, by omega, by rw [o4]; simpa using hx⟩
      · exact ⟨5, by omega, by rw [o5]; simpa using hx⟩
      · exact ⟨0, by omega, by rw [o0]; simpa using hx⟩
      · exact ⟨1, by omega, by rw [o1]; simpa using hx⟩
  · rintro ⟨k, hk, hx⟩
    cases h : (phase w == 1)
    · obtain ⟨o0, o1, o2, o3, o4, o5⟩ := hE h
      simp only [Standard.oddChildB, Finset.mem_union, Standard.mem_shift]
      interval_cases k
      · rw [o0] at hx; simp at hx; tauto
      · rw [o1] at hx; simp at hx; tauto
      · rw [o2] at hx; simp at hx; tauto
      · rw [o3] at hx; simp at hx; tauto
      · rw [o4] at hx; simp at hx; tauto
      · rw [o5] at hx; simp at hx; tauto
    · obtain ⟨o0, o1, o2, o3, o4, o5⟩ := hO h
      simp only [Standard.oddChildB, Finset.mem_union, Standard.mem_shift]
      interval_cases k
      · rw [o0] at hx; simp at hx; tauto
      · rw [o1] at hx; simp at hx; tauto
      · rw [o2] at hx; simp at hx; tauto
      · rw [o3] at hx; simp at hx; tauto
      · rw [o4] at hx; simp at hx; tauto
      · rw [o5] at hx; simp at hx; tauto

open FLatticePaper.Tiles.ChildGlue (keptSet pieceFlag dblOdd dblEven tOddSet tEvenSet kept_cover keptSet_subset)

theorem oddFull_length (f : Word → JSlice) (w : Word) : (oddFull f w).length = 6 := by
  simp [oddFull, tileOddPieces]

/-- **The glue respects the full odd decomposition** once every two copies agree on their overlap: each point of a copy is kept
by some copy, where the glue is that copy's piece, and the two pieces agree there. -/
theorem odd_respects (f : Word → JSlice) (w u1 u2 : Word) (hw : ¬ IsBase w) (hreg : regsAt w = (some u1, some u2))
    (hc : ¬ CorrectedAfterThree w) (hl1 : u1.length < w.length) (hl2 : u2.length < w.length)
    (hdO : (f u1).tOdd.dom = Standard.oddTile u1) (hdE : (f u2).tEven.dom = Standard.evenTile u2)
    (hT1 : (Standard.stateAt w).tOdd = Standard.oddTile u1) (hT2 : (Standard.stateAt w).tEven = Standard.evenTile u2)
    (κ : ℕ → ℤ) (go : Site → ℤ)
    (hgo : ∀ i < (oddP w).length + (oddQ w).length,
      ∀ z ∈ keptSet (pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2)) (pieceFlag (oddP w)) (dblOdd w) i,
        go z = placedOdd w (f u1).tOdd.val (f u2).tEven.val 0 i z + κ i)
    (hall : ∀ k l, k < 6 → l < 6 → AgreeOn (fun i z => placedOdd w (f u1).tOdd.val (f u2).tEven.val 0 i z + κ i)
      (pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2)) k l) :
    RespectsPieces ⟨Standard.oddTile w, go⟩ (oddFull f w) := by
  have hget := oddFull_get f w u1 u2 hw hreg hc hl1 hl2
  have hlen6 : (oddP w).length + (oddQ w).length = 6 := by
    rw [ClosedPathCycle.oddP_length, ClosedPathCycle.oddQ_length]
  have memC : ∀ k < 6, ∀ x, x ∈ pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) k ↔
      x - offO w k ∈ (if k < 2 then (f u1).tOdd else (f u2).tEven).dom := by
    intro k hk x
    rw [memC_odd w _ _ k hk x]
    by_cases h : k < 2
    · simp only [if_pos h, tOddSet, Finset.mem_coe, hdO]
    · simp only [if_neg h, tEvenSet, Finset.mem_coe, hdE]
  have hfull : ∀ k < 6, ∀ x ∈ pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) k,
      go x = placedOdd w (f u1).tOdd.val (f u2).tEven.val 0 k x + κ k := by
    intro k hk x hx
    obtain ⟨j, hj, hxj⟩ := kept_cover _ _ _ k x hx
    rw [hgo j (by omega) x hxj]
    exact hall j k (by omega) hk x (keptSet_subset _ _ _ j hxj) hx
  have hidx : ∀ p ∈ oddFull f w, ∃ k < 6, p = stdPiece (if k < 2 then (f u1).tOdd else (f u2).tEven) (offO w k)
      (affOdd (parentsAt w).odd (parentsAt w).even k) := by
    intro p hp
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hp
    have hk6 : k < 6 := by
      have := (List.getElem?_eq_some_iff.mp hk).1
      rwa [oddFull_length] at this
    rw [hget k hk6] at hk
    exact ⟨k, hk6, (Option.some.inj hk).symm⟩
  refine ⟨?_, fun p hp => ?_⟩
  · ext x
    show x ∈ Standard.oddTile w ↔ x ∈ pieceUnion (oddFull f w)
    rw [oddTile_union w u1 u2 hw hT1 hT2, JointGlue.mem_pieceUnion]
    constructor
    · rintro ⟨k, hk, hx⟩
      refine ⟨_, List.mem_of_getElem? (hget k hk), ?_⟩
      rw [mem_placed_std]
      by_cases h : k < 2
      · rw [if_pos h] at hx ⊢; rw [hdO]; exact hx
      · rw [if_neg h] at hx ⊢; rw [hdE]; exact hx
    · rintro ⟨p, hp, hx⟩
      obtain ⟨k, hk, rfl⟩ := hidx p hp
      rw [mem_placed_std] at hx
      refine ⟨k, hk, ?_⟩
      by_cases h : k < 2
      · rw [if_pos h] at hx ⊢; rw [← hdO]; exact hx
      · rw [if_neg h] at hx ⊢; rw [← hdE]; exact hx
  · obtain ⟨k, hk, rfl⟩ := hidx p hp
    refine ⟨κ k, fun x hx _ => ?_⟩
    rw [mem_placed_std] at hx
    have hxC := (memC k hk x).2 hx
    show go x = _
    rw [hfull k hk x hxC, placedOdd_eq]
    by_cases h : k < 2
    · simp only [if_pos h, stdPiece]
    · simp only [if_neg h, stdPiece]

open FLatticePaper.Tiles.ChildGlue (MarksAgreeOdd DoubledAgreeOdd MarksAgreeEven DoubledAgreeEven)

theorem memC_full (w u1 u2 : Word) (P Q : PartialOdometer) (hdO : P.dom = Standard.oddTile u1)
    (hdE : Q.dom = Standard.evenTile u2) (k : ℕ) (hk : k < 6) (x : Site) :
    x ∈ pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) k ↔ x - offO w k ∈ (if k < 2 then P else Q).dom := by
  rw [memC_odd w _ _ k hk x]
  by_cases h : k < 2
  · simp only [if_pos h, tOddSet, Finset.mem_coe, hdO]
  · simp only [if_neg h, tEvenSet, Finset.mem_coe, hdE]

/-- **The odd child that is not corrected**: the glue on the kept parts respects the full decomposition. -/
theorem odd_full (D : JointData) (hS : D.S = paperS) (hsl : WeakStepAssembly.TileSlopeZero D) (hsp : SameParentInput D)
    (f : Word → JSlice) (w u1 u2 : Word) (hgood : GoodBelow D f w.length) (hw : ¬ IsBase w)
    (hreg : regsAt w = (some u1, some u2)) (hc : ¬ CorrectedAfterThree w) (κ : ℕ → ℤ) (go : Site → ℤ)
    (hM : MarksAgreeOdd w u1 u2 (fun i z => placedOdd w (f u1).tOdd.val (f u2).tEven.val 0 i z + κ i))
    (hD : DoubledAgreeOdd w u1 u2 (dblOdd w) (fun i z => placedOdd w (f u1).tOdd.val (f u2).tEven.val 0 i z + κ i))
    (hgo : ∀ i < (oddP w).length + (oddQ w).length,
      ∀ z ∈ keptSet (pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2)) (pieceFlag (oddP w)) (dblOdd w) i,
        go z = placedOdd w (f u1).tOdd.val (f u2).tEven.val 0 i z + κ i) :
    RespectsPieces ⟨Standard.oddTile w, go⟩ (oddFull f w) := by
  have hl1 : u1.length < w.length := JointInduction.regsAt_lt w u1 (Or.inl (by rw [hreg]))
  have hl2 : u2.length < w.length := JointInduction.regsAt_lt w u2 (Or.inr (by rw [hreg]))
  have hp : (parentsAt u1).current .odd = (parentsAt w).odd :=
    ((WeakStepAssembly.regsAt_parents w).1 u1 (by rw [hreg])).symm
  have hq : (parentsAt u2).current .even = (parentsAt w).even :=
    ((WeakStepAssembly.regsAt_parents w).2 u2 (by rw [hreg])).symm
  obtain ⟨hS1, hJ1⟩ := hgood u1 hl1
  obtain ⟨hS2, hJ2⟩ := hgood u2 hl2
  have hdO : (f u1).tOdd.dom = Standard.oddTile u1 := by rw [(WeakStepAssembly.slice_domains D f u1 hS1).1, hS]; rfl
  have hdE : (f u2).tEven.dom = Standard.evenTile u2 := by rw [(WeakStepAssembly.slice_domains D f u2 hS2).2, hS]; rfl
  have hT1 : (Standard.stateAt w).tOdd = Standard.oddTile u1 := (WeakStepPaper.regsAt_tiles w).1 u1 (by rw [hreg])
  have hT2 : (Standard.stateAt w).tEven = Standard.evenTile u2 := (WeakStepPaper.regsAt_tiles w).2.2.1 u2 (by rw [hreg])
  -- corners and half-turns of the registers
  obtain ⟨αo, γo, -, hVo⟩ := TileTranslationStd.stdCorners_odd u1 (f u1).tOdd (WeakStepAssembly.slice_respects D f u1 hS1).1
  obtain ⟨αe, γe, -, hVe⟩ := TileTranslationStd.stdCorners_even u2 (f u2).tEven (WeakStepAssembly.slice_respects D f u2 hS2).2
  have hcP := corners_of _ _ _ _ _ _ hVo
  have hcQ := corners_of _ _ _ _ _ _ hVe
  rw [hdO, hp] at hcP
  rw [hdE, hq] at hcQ
  obtain ⟨⟨βo, hzo⟩, -⟩ := hsl f w.length hgood u1 hl1
  obtain ⟨-, ⟨βe, hze⟩⟩ := hsl f w.length hgood u2 hl2
  have hHP := raw_halfTurn _ _ _ _ hJ1.2.1.2.2.1 βo hzo
  have hHQ := raw_halfTurn _ _ _ _ hJ2.2.1.2.2.2.1 βe hze
  rw [hp] at hHP
  rw [hq] at hHQ
  obtain ⟨K, hK⟩ := odd_rel w (f u1).tOdd (f u2).tEven κ hHP hHQ
  rw [hdO, hdE] at hK
  -- the agreements
  have hlen6 : (oddP w).length + (oddQ w).length = 6 := by
    rw [ClosedPathCycle.oddP_length, ClosedPathCycle.oddQ_length]
  have hmix : ∀ k l, k < 2 → 2 ≤ l → l < 6 → AgreeOn (fun i z => placedOdd w (f u1).tOdd.val (f u2).tEven.val 0 i z + κ i)
      (pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2)) k l := by
    intro k l hk hl hl6 x hxk hxl
    have hfl : pieceFlag (oddP w) k ≠ pieceFlag (oddP w) l := by
      simp only [pieceFlag, ClosedPathCycle.oddP_length, ne_eq, decide_eq_decide]
      omega
    obtain ⟨m1, m2⟩ := ChildGlue.copies_mixed (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) (SiteInduction.marksOdd u1)
      (SiteInduction.marksEven u2) (fun a ha b hb z h1 h2 => MixedFromCells.mixedOdd_all w hw u1 u2 hT1 hT2 a ha b hb z h1 h2)
      k l (by omega) (by omega) hfl x hxk hxl
    exact hM k l (by omega) (by omega) hfl x m1 m2
  have hdbl : ∀ j, j = 2 ∨ j = 4 → AgreeOn (fun i z => placedOdd w (f u1).tOdd.val (f u2).tEven.val 0 i z + κ i)
      (pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2)) j (j + 1) := by
    intro j hj x h1 h2
    exact hD j (j + 1) (by omega) (by omega) (by omega)
      (by simp only [pieceFlag, ClosedPathCycle.oddP_length, decide_eq_decide]; omega)
      ⟨rfl, by rw [ClosedPathCycle.oddP_length]; omega⟩ x h1 h2
  obtain ⟨k01, k34, k25⟩ := oddK w _ (Standard.oddTile u1) (Standard.evenTile u2) _ _ K hK hmix (hdbl 2 (Or.inl rfl))
    (hdbl 4 (Or.inr rfl)) hcP hcQ
  have hget := oddFull_get f w u1 u2 hw hreg hc hl1 hl2
  have memC := memC_full w u1 u2 (f u1).tOdd (f u2).tEven hdO hdE
  have conv : ∀ i j, i < 6 → j < 6 → PairCompat (oddFull f w) i j → ∃ c : ℤ,
      ∀ x ∈ pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) i,
        x ∈ pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) j →
          (placedOdd w (f u1).tOdd.val (f u2).tEven.val 0 i x + κ i) -
            (placedOdd w (f u1).tOdd.val (f u2).tEven.val 0 j x + κ j) = c := by
    intro i j hi hj h
    obtain ⟨c, hc'⟩ := h _ _ (hget i hi) (hget j hj)
    refine ⟨c + κ i - κ j, fun x hxi hxj => ?_⟩
    have e := hc' x ((mem_placed_std _ _ _ x).2 ((memC i hi x).1 hxi)) ((mem_placed_std _ _ _ x).2 ((memC j hj x).1 hxj))
      (by simp [stdPiece]) (by simp [stdPiece])
    rw [placedOdd_eq, placedOdd_eq]
    simp only [JointGlue.pieceVal, stdPiece] at e
    by_cases hi2 : i < 2 <;> by_cases hj2 : j < 2 <;> simp only [hi2, hj2, if_true, if_false] at e ⊢ <;> linarith
  have disj : ∀ i j, i < 6 → j < 6 → PairDisjoint (oddFull f w) i j →
      AgreeOn (fun i z => placedOdd w (f u1).tOdd.val (f u2).tEven.val 0 i z + κ i)
        (pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2)) i j := by
    intro i j hi hj h x hxi hxj
    exact absurd ((mem_placed_std _ _ _ x).2 ((memC j hj x).1 hxj))
      (Finset.disjoint_left.mp (h _ _ (hget i hi) (hget j hj)) ((mem_placed_std _ _ _ x).2 ((memC i hi x).1 hxi)))
  obtain ⟨hd24, hd35, hc01, hc34, hc25⟩ := (hsp f w hgood hw).1 hc
  obtain ⟨c01, hc01'⟩ := conv 0 1 (by omega) (by omega) hc01
  obtain ⟨c34, hc34'⟩ := conv 3 4 (by omega) (by omega) hc34
  obtain ⟨c25, hc25'⟩ := conv 2 5 (by omega) (by omega) hc25
  have a01 := swapped_agree hK (i := 0) (by omega) (by decide) rfl k01 c01 hc01'
  have a34 := swapped_agree hK (i := 3) (by omega) (by decide) rfl k34 c34 hc34'
  have a25 := swapped_agree hK (i := 2) (by omega) (by decide) rfl k25 c25 hc25'
  have a24 := disj 2 4 (by omega) (by omega) hd24
  have a35 := disj 3 5 (by omega) (by omega) hd35
  have hlt : ∀ k l, k < l → l < 6 → AgreeOn (fun i z => placedOdd w (f u1).tOdd.val (f u2).tEven.val 0 i z + κ i)
      (pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2)) k l := by
    intro k l hkl hl
    interval_cases l <;> interval_cases k
    all_goals first
      | exact a01 | exact a34 | exact a25 | exact a24 | exact a35
      | exact hdbl 2 (Or.inl rfl) | exact hdbl 4 (Or.inr rfl)
      | exact hmix _ _ (by omega) (by omega) (by omega)
  have hall : ∀ k l, k < 6 → l < 6 → AgreeOn (fun i z => placedOdd w (f u1).tOdd.val (f u2).tEven.val 0 i z + κ i)
      (pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2)) k l := by
    intro k l hk hl
    rcases lt_trichotomy k l with h | rfl | h
    · exact hlt k l h hl
    · exact fun x _ _ => rfl
    · exact agreeOn_symm (hlt l k h hk)
  exact odd_respects f w u1 u2 hw hreg hc hl1 hl2 hdO hdE hT1 hT2 κ go hgo hall

/-! ### The even child -/

/-- The half-turn of the even child on its six copies: `P^{+,1} ↔ P^{-,2}`, `P^{+,2} ↔ P^{-,1}`, `Q^+ ↔ Q^-`. -/
def σE : ℕ → ℕ
  | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 5 | 5 => 4 | n => n

/-- The offset of copy `k` of the even child. -/
def offE (w : Word) (k : ℕ) : Site := if k < 4 then (evenP w).getD k 0 else (evenQ w).getD (k - 4) 0

theorem even_alg (w : Word) (k : ℕ) (hk : k < 6) :
    offE w k + offE w (σE k) + (if k < 4 then cenO (parentsAt w).odd else cenE (parentsAt w).even) =
        cenE ((parentsAt w).current .even) ∧
      affEven (parentsAt w).odd (parentsAt w).even k + affEven (parentsAt w).odd (parentsAt w).even (σE k) +
          (if k < 4 then offsetA (parentsAt w).odd.num (parentsAt w).odd.den true
            else offsetA (parentsAt w).even.num (parentsAt w).even.den true) =
        offsetA ((parentsAt w).current .even).num ((parentsAt w).current .even).den true := by
  interval_cases k <;> cases h : (phase w == 1) <;>
    simp only [offE, σE, evenP, evenQ, MixedPieces.pOffsetsEven, MixedPieces.qOffsetsEven, h, cenO, cenE, affEven,
      Parents.current, Parents.combine, offsetA, if_true, if_false, Bool.false_eq_true, List.getD_cons_zero,
      List.getD_cons_succ, Nat.reduceSub, Nat.lt_irrefl, Nat.reduceLT, Nat.reduceEqDiff,
      OfNat.ofNat_ne_one, zero_ne_one] <;>
    refine ⟨?_, ?_⟩ <;> ext <;>
    simp [texV1Odd, texV1Even, texV2] <;> ring

theorem σE_lt (k : ℕ) (hk : k < 6) : σE k < 6 ∧ σE (σE k) = k ∧ (k < 4 ↔ σE k < 4) := by
  interval_cases k <;> simp [σE]

theorem memC_even (w : Word) (T1 T2 : Set Site) (k : ℕ) (_hk : k < 6) (x : Site) :
    x ∈ pieceSet (evenP w) (evenQ w) T1 T2 k ↔ x - offE w k ∈ (if k < 4 then T1 else T2) := by
  unfold pieceSet offE
  rw [ClosedPathCycle.evenP_length]
  by_cases h : k < 4
  · simp only [if_pos h, mem_shiftS']
  · simp only [if_neg h, mem_shiftS']

theorem placedEven_eq (w : Word) (oP oQ : Site → ℤ) (κ : ℕ → ℤ) (k : ℕ) (x : Site) :
    placedEven w oP oQ 0 k x + κ k = (if k < 4 then oP else oQ) (x - offE w k) +
      dotS (affEven (parentsAt w).odd (parentsAt w).even k) x + κ k := by
  unfold placedEven offE
  by_cases h : k < 4 <;> simp [h, ClosedPathSum.dot2, dotS]

/-- **The half-turn relation of the even child**, from the half-turns of the two registers. -/
theorem even_rel (w : Word) (P Q : PartialOdometer) (κ : ℕ → ℤ)
    (hP : ∀ y ∈ P.dom, cenO (parentsAt w).odd - y ∈ P.dom ∧
      2 * (P.val (cenO (parentsAt w).odd - y) - P.val y) =
        dotS (offsetA (parentsAt w).odd.num (parentsAt w).odd.den true) (cenO (parentsAt w).odd) -
          2 * dotS (offsetA (parentsAt w).odd.num (parentsAt w).odd.den true) y)
    (hQ : ∀ y ∈ Q.dom, cenE (parentsAt w).even - y ∈ Q.dom ∧
      2 * (Q.val (cenE (parentsAt w).even - y) - Q.val y) =
        dotS (offsetA (parentsAt w).even.num (parentsAt w).even.den true) (cenE (parentsAt w).even) -
          2 * dotS (offsetA (parentsAt w).even.num (parentsAt w).even.den true) y) :
    ∃ K : ℕ → ℤ, HalfTurnRel (fun k z => placedEven w P.val Q.val 0 k z + κ k)
      (pieceSet (evenP w) (evenQ w) ↑P.dom ↑Q.dom) (cenE ((parentsAt w).current .even))
      (offsetA ((parentsAt w).current .even).num ((parentsAt w).current .even).den true) σE K := by
  have h : ∀ k, k < 6 → ∃ Kk : ℤ, ∀ x ∈ pieceSet (evenP w) (evenQ w) ↑P.dom ↑Q.dom k,
      cenE ((parentsAt w).current .even) - x ∈ pieceSet (evenP w) (evenQ w) ↑P.dom ↑Q.dom (σE k) ∧
      2 * (placedEven w P.val Q.val 0 (σE k) (cenE ((parentsAt w).current .even) - x) + κ (σE k)) =
        2 * (placedEven w P.val Q.val 0 k x + κ k) -
          2 * dotS (offsetA ((parentsAt w).current .even).num ((parentsAt w).current .even).den true) x + Kk := by
    intro k hk
    obtain ⟨hs6, -, hs4⟩ := σE_lt k hk
    obtain ⟨hu, hη⟩ := even_alg w k hk
    by_cases hk4 : k < 4
    · have hs : σE k < 4 := hs4.1 hk4
      rw [if_pos hk4] at hu hη
      refine rel_part P _ _ hP _ _ _ _ _ _ hu hη (κ k) (κ (σE k)) (pieceSet (evenP w) (evenQ w) ↑P.dom ↑Q.dom k)
        (pieceSet (evenP w) (evenQ w) ↑P.dom ↑Q.dom (σE k)) (fun x => ?_) (fun x => ?_)
        (fun z => placedEven w P.val Q.val 0 k z + κ k) (fun z => placedEven w P.val Q.val 0 (σE k) z + κ (σE k))
        (fun x => ?_) (fun x => ?_)
      · rw [memC_even w _ _ k hk x, if_pos hk4]; rfl
      · rw [memC_even w _ _ (σE k) hs6 x, if_pos hs]; rfl
      · rw [placedEven_eq, if_pos hk4]
      · rw [placedEven_eq, if_pos hs]
    · have hs : ¬ σE k < 4 := fun h => hk4 (hs4.2 h)
      rw [if_neg hk4] at hu hη
      refine rel_part Q _ _ hQ _ _ _ _ _ _ hu hη (κ k) (κ (σE k)) (pieceSet (evenP w) (evenQ w) ↑P.dom ↑Q.dom k)
        (pieceSet (evenP w) (evenQ w) ↑P.dom ↑Q.dom (σE k)) (fun x => ?_) (fun x => ?_)
        (fun z => placedEven w P.val Q.val 0 k z + κ k) (fun z => placedEven w P.val Q.val 0 (σE k) z + κ (σE k))
        (fun x => ?_) (fun x => ?_)
      · rw [memC_even w _ _ k hk x, if_neg hk4]; rfl
      · rw [memC_even w _ _ (σE k) hs6 x, if_neg hs]; rfl
      · rw [placedEven_eq, if_neg hk4]
      · rw [placedEven_eq, if_neg hs]
  choose! K hK using h
  exact ⟨K, fun k hk x hx => by
    obtain ⟨h1, h2⟩ := hK k hk x hx
    exact ⟨h1, by linarith⟩⟩

theorem offE_vals (w : Word) :
    ((phase w == 1) = false → offE w 0 = texV1Even (parentsAt w).even ∧
      offE w 1 = texV1Even (parentsAt w).even + texV2 (parentsAt w).odd ∧ offE w 2 = texV2 (parentsAt w).even ∧
      offE w 3 = texV2 (parentsAt w).even + texV2 (parentsAt w).odd ∧ offE w 4 = 0 ∧
      offE w 5 = texV1Odd (parentsAt w).odd + (texV2 (parentsAt w).odd + texV2 (parentsAt w).odd)) ∧
    ((phase w == 1) = true → offE w 0 = 0 ∧ offE w 1 = texV2 (parentsAt w).odd ∧
      offE w 2 = texV1Even (parentsAt w).even + texV2 (parentsAt w).even ∧
      offE w 3 = texV1Even (parentsAt w).even + texV2 (parentsAt w).even + texV2 (parentsAt w).odd ∧
      offE w 4 = texV1Odd (parentsAt w).odd ∧ offE w 5 = texV2 (parentsAt w).odd + texV2 (parentsAt w).odd) := by
  refine ⟨fun h => ?_, fun h => ?_⟩ <;>
    simp [offE, evenP, evenQ, MixedPieces.pOffsetsEven, MixedPieces.qOffsetsEven, h]

/-- **The constants of the swapped pairs of the even child are equal**, along the spanning tree `(0,1), (0,4), (1,5), (2,4),
(2,3)` of agreeing overlaps with corner witnesses. -/
theorem evenK (w : Word) (F : ℕ → Site → ℤ) (PT QT : Finset Site) (Dc a : Site) (K : ℕ → ℤ)
    (hK : HalfTurnRel F (pieceSet (evenP w) (evenQ w) ↑PT ↑QT) Dc a σE K)
    (hmix : ∀ k l, k < 4 → 4 ≤ l → l < 6 → AgreeOn F (pieceSet (evenP w) (evenQ w) ↑PT ↑QT) k l)
    (h01 : AgreeOn F (pieceSet (evenP w) (evenQ w) ↑PT ↑QT) 0 1)
    (h23 : AgreeOn F (pieceSet (evenP w) (evenQ w) ↑PT ↑QT) 2 3)
    (hcP : Corners PT (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd))
    (hcQ : Corners QT (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)) :
    K 0 = K 3 ∧ K 1 = K 2 ∧ K 4 = K 5 := by
  have mP : ∀ k x, k < 4 → x - offE w k ∈ PT → x ∈ pieceSet (evenP w) (evenQ w) ↑PT ↑QT k := fun k x hk h =>
    (memC_even w _ _ k (by omega) x).2 (by rw [if_pos hk]; exact h)
  have mQ : ∀ k x, 4 ≤ k → k < 6 → x - offE w k ∈ QT → x ∈ pieceSet (evenP w) (evenQ w) ↑PT ↑QT k :=
    fun k x hk hk6 h => (memC_even w _ _ k hk6 x).2 (by rw [if_neg (by omega)]; exact h)
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7⟩ := hcP
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7⟩ := hcQ
  obtain ⟨hE, hO⟩ := offE_vals w
  cases h : (phase w == 1)
  · obtain ⟨o0, o1, o2, o3, o4, o5⟩ := hE h
    have e01 := const_eq hK (k := 0) (l := 1) (by omega) (by omega)
      (texV1Even (parentsAt w).even + (texV2 (parentsAt w).odd + ((1 : ℤ), (0 : ℤ))))
      (mP 0 _ (by omega) (by rw [o0]; convert c4 using 1; abel))
      (mP 1 _ (by omega) (by rw [o1]; convert c1 using 1; abel))
      h01 (agreeOn_symm h23)
    have e04 := const_eq hK (k := 0) (l := 4) (by omega) (by omega) (texV1Even (parentsAt w).even)
      (mP 0 _ (by omega) (by rw [o0, sub_self]; exact c0))
      (mQ 4 _ (by omega) (by omega) (by rw [o4, sub_zero]; exact d3))
      (hmix 0 4 (by omega) (by omega) (by omega)) (hmix 3 5 (by omega) (by omega) (by omega))
    have e15 := const_eq hK (k := 1) (l := 5) (by omega) (by omega)
      (texV1Even (parentsAt w).even + texV2 (parentsAt w).odd +
        (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + ((1 : ℤ), (-1 : ℤ)) - ((1 : ℤ), (0 : ℤ))))
      (mP 1 _ (by omega) (by rw [o1]; convert c7 using 1; abel))
      (mQ 5 _ (by omega) (by omega) (by rw [o5]; convert d2 using 1; ext <;> simp <;> ring))
      (hmix 1 5 (by omega) (by omega) (by omega)) (hmix 2 4 (by omega) (by omega) (by omega))
    have e24 := const_eq hK (k := 2) (l := 4) (by omega) (by omega)
      (texV2 (parentsAt w).even + ((1 : ℤ), (0 : ℤ)))
      (mP 2 _ (by omega) (by rw [o2]; convert c1 using 1; abel))
      (mQ 4 _ (by omega) (by omega) (by rw [o4, sub_zero]; exact d4))
      (hmix 2 4 (by omega) (by omega) (by omega)) (hmix 1 5 (by omega) (by omega) (by omega))
    have e23 := const_eq hK (k := 2) (l := 3) (by omega) (by omega)
      (texV2 (parentsAt w).even + (texV2 (parentsAt w).odd + ((1 : ℤ), (0 : ℤ))))
      (mP 2 _ (by omega) (by rw [o2]; convert c4 using 1; abel))
      (mP 3 _ (by omega) (by rw [o3]; convert c1 using 1; abel))
      h23 (agreeOn_symm h01)
    exact ⟨by omega, by omega, by omega⟩
  · obtain ⟨o0, o1, o2, o3, o4, o5⟩ := hO h
    have e01 := const_eq hK (k := 0) (l := 1) (by omega) (by omega)
      (texV2 (parentsAt w).odd + ((1 : ℤ), (0 : ℤ)))
      (mP 0 _ (by omega) (by rw [o0, sub_zero]; exact c4))
      (mP 1 _ (by omega) (by rw [o1]; convert c1 using 1; abel))
      h01 (agreeOn_symm h23)
    have e04 := const_eq hK (k := 0) (l := 4) (by omega) (by omega) (texV1Odd (parentsAt w).odd)
      (mP 0 _ (by omega) (by rw [o0, sub_zero]; exact c3))
      (mQ 4 _ (by omega) (by omega) (by rw [o4, sub_self]; exact d0))
      (hmix 0 4 (by omega) (by omega) (by omega)) (hmix 3 5 (by omega) (by omega) (by omega))
    have e15 := const_eq hK (k := 1) (l := 5) (by omega) (by omega)
      (texV2 (parentsAt w).odd + (texV2 (parentsAt w).odd + ((1 : ℤ), (0 : ℤ))))
      (mP 1 _ (by omega) (by rw [o1]; convert c4 using 1; abel))
      (mQ 5 _ (by omega) (by omega) (by rw [o5]; convert d1 using 1; abel))
      (hmix 1 5 (by omega) (by omega) (by omega)) (hmix 2 4 (by omega) (by omega) (by omega))
    have e24 := const_eq hK (k := 2) (l := 4) (by omega) (by omega)
      (texV1Even (parentsAt w).even + texV2 (parentsAt w).even + (texV1Odd (parentsAt w).odd - ((0 : ℤ), (1 : ℤ))))
      (mP 2 _ (by omega) (by rw [o2]; convert c2 using 1; abel))
      (mQ 4 _ (by omega) (by omega) (by rw [o4]; convert d7 using 1; ext <;> (simp; try ring)))
      (hmix 2 4 (by omega) (by omega) (by omega)) (hmix 1 5 (by omega) (by omega) (by omega))
    have e23 := const_eq hK (k := 2) (l := 3) (by omega) (by omega)
      (texV1Even (parentsAt w).even + texV2 (parentsAt w).even + (texV2 (parentsAt w).odd + ((1 : ℤ), (0 : ℤ))))
      (mP 2 _ (by omega) (by rw [o2]; convert c4 using 1; abel))
      (mP 3 _ (by omega) (by rw [o3]; convert c1 using 1; abel))
      h23 (agreeOn_symm h01)
    exact ⟨by omega, by omega, by omega⟩

theorem offE_eq (w : Word) :
    q0Off w .p1DPlus = offE w 0 ∧ q0Off w .p1DPlus + vP2 w = offE w 1 ∧ q0Off w .p1DMinus = offE w 2 ∧
      q0Off w .p1DMinus + vP2 w = offE w 3 ∧ q0Off w .q1Plus = offE w 4 ∧ q0Off w .q1Minus = offE w 5 := by
  cases h : (phase w == 1) <;>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp [q0Off, offE, evenP, evenQ, MixedPieces.pOffsetsEven, MixedPieces.qOffsetsEven, SurgicalDict.offsetQ0, W1Odd,
      vP1, vP2, vQ1, vQ2, h]; try abel)

theorem affE_eq (w : Word) :
    q0Aff w .p1DPlus = affEven (parentsAt w).odd (parentsAt w).even 0 ∧
      q0Aff w .p1DPlus + aP2 w = affEven (parentsAt w).odd (parentsAt w).even 1 ∧
      q0Aff w .p1DMinus = affEven (parentsAt w).odd (parentsAt w).even 2 ∧
      q0Aff w .p1DMinus + aP2 w = affEven (parentsAt w).odd (parentsAt w).even 3 ∧
      q0Aff w .q1Plus = affEven (parentsAt w).odd (parentsAt w).even 4 ∧
      q0Aff w .q1Minus = affEven (parentsAt w).odd (parentsAt w).even 5 := by
  cases h : W1Odd w <;>
    simp only [q0Aff, h, affEven, aP2, pairAffine, offsetA, if_true, if_false, Bool.false_eq_true] <;>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ext <;> simp <;> ring

theorem evenFull_get (f : Word → JSlice) (w u1 u2 : Word) (hw : ¬ IsBase w) (hreg : regsAt w = (some u1, some u2))
    (hc : ¬ CorrectedAfterTwo w) (hl1 : u1.length < w.length) (hl2 : u2.length < w.length) (k : ℕ) (hk : k < 6) :
    (evenFull f w)[k]? = some (stdPiece (if k < 4 then (f u1).tOdd else (f u2).tEven) (offE w k)
      (affEven (parentsAt w).odd (parentsAt w).even k)) := by
  have hcorr : decide (w.getLast? = some Digit.two) = false := by
    simp only [decide_eq_false_iff_not]
    exact fun h => hc ⟨hw, h⟩
  have hb1 : below f w u1 = f u1 := by simp only [below, if_pos hl1]
  have hb2 : below f w u2 = f u2 := by simp only [below, if_pos hl2]
  obtain ⟨o0, o1, o2, o3, o4, o5⟩ := offE_eq w
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := affE_eq w
  have hL : evenFull f w = [stdPiece (f u1).tOdd (offE w 0) (affEven (parentsAt w).odd (parentsAt w).even 0),
      stdPiece (f u1).tOdd (offE w 1) (affEven (parentsAt w).odd (parentsAt w).even 1),
      stdPiece (f u1).tOdd (offE w 2) (affEven (parentsAt w).odd (parentsAt w).even 2),
      stdPiece (f u1).tOdd (offE w 3) (affEven (parentsAt w).odd (parentsAt w).even 3),
      stdPiece (f u2).tEven (offE w 4) (affEven (parentsAt w).odd (parentsAt w).even 4),
      stdPiece (f u2).tEven (offE w 5) (affEven (parentsAt w).odd (parentsAt w).even 5)] := by
    simp only [evenFull, tileEvenPieces, hreg, regOdo, hb1, hb2, hcorr, Bool.false_eq_true, if_false]
    rw [o1, o3, o0, o2, o4, o5, a1, a3, a0, a2, a4, a5]
  rw [hL]
  interval_cases k <;> simp

theorem evenFull_length (f : Word → JSlice) (w : Word) : (evenFull f w).length = 6 := by
  simp [evenFull, tileEvenPieces]

/-- The even child tile is the union of its six copies. -/
theorem evenTile_union (w u1 u2 : Word) (hw : ¬ IsBase w) (hT1 : (Standard.stateAt w).tOdd = Standard.oddTile u1)
    (hT2 : (Standard.stateAt w).tEven = Standard.evenTile u2) (x : Site) :
    x ∈ Standard.evenTile w ↔ ∃ k < 6, x - offE w k ∈ (if k < 4 then Standard.oddTile u1 else Standard.evenTile u2) := by
  have ho : Standard.evenTile w = Standard.evenChildB (phase w == 1) (Standard.oddTile u1) (Standard.evenTile u2)
      (parentsAt w).odd (parentsAt w).even := by
    show (Standard.childTiles w (Standard.stateAt w)).2 = _
    rw [SiteInduction.childTiles_nonbase w hw, hT1, hT2, Standard.stateAt_par]
  rw [ho]
  obtain ⟨hE, hO⟩ := offE_vals w
  constructor
  · intro hx
    cases h : (phase w == 1)
    · obtain ⟨o0, o1, o2, o3, o4, o5⟩ := hE h
      simp only [h, Standard.evenChildB, Finset.mem_union, Standard.mem_shift] at hx
      rcases hx with ((((hx | hx) | hx) | hx) | hx) | hx
      · exact ⟨4, by omega, by rw [o4]; simpa using hx⟩
      · exact ⟨5, by omega, by rw [o5]; simpa using hx⟩
      · exact ⟨0, by omega, by rw [o0]; simpa using hx⟩
      · exact ⟨1, by omega, by rw [o1]; simpa using hx⟩
      · exact ⟨2, by omega, by rw [o2]; simpa using hx⟩
      · exact ⟨3, by omega, by rw [o3]; simpa using hx⟩
    · obtain ⟨o0, o1, o2, o3, o4, o5⟩ := hO h
      simp only [h, Standard.evenChildB, Finset.mem_union, Standard.mem_shift] at hx
      rcases hx with ((((hx | hx) | hx) | hx) | hx) | hx
      · exact ⟨4, by omega, by rw [o4]; simpa using hx⟩
      · exact ⟨5, by omega, by rw [o5]; simpa using hx⟩
      · exact ⟨0, by omega, by rw [o0]; simpa using hx⟩
      · exact ⟨1, by omega, by rw [o1]; simpa using hx⟩
      · exact ⟨2, by omega, by rw [o2]; simpa using hx⟩
      · exact ⟨3, by omega, by rw [o3]; simpa using hx⟩
  · rintro ⟨k, hk, hx⟩
    cases h : (phase w == 1)
    · obtain ⟨o0, o1, o2, o3, o4, o5⟩ := hE h
      simp only [Standard.evenChildB, Finset.mem_union, Standard.mem_shift]
      interval_cases k
      · rw [o0] at hx; simp at hx; tauto
      · rw [o1] at hx; simp at hx; tauto
      · rw [o2] at hx; simp at hx; tauto
      · rw [o3] at hx; simp at hx; tauto
      · rw [o4] at hx; simp at hx; tauto
      · rw [o5] at hx; simp at hx; tauto
    · obtain ⟨o0, o1, o2, o3, o4, o5⟩ := hO h
      simp only [Standard.evenChildB, Finset.mem_union, Standard.mem_shift]
      interval_cases k
      · rw [o0] at hx; simp at hx; tauto
      · rw [o1] at hx; simp at hx; tauto
      · rw [o2] at hx; simp at hx; tauto
      · rw [o3] at hx; simp at hx; tauto
      · rw [o4] at hx; simp at hx; tauto
      · rw [o5] at hx; simp at hx; tauto

theorem memC_fullE (w u1 u2 : Word) (P Q : PartialOdometer) (hdO : P.dom = Standard.oddTile u1)
    (hdE : Q.dom = Standard.evenTile u2) (k : ℕ) (hk : k < 6) (x : Site) :
    x ∈ pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) k ↔ x - offE w k ∈ (if k < 4 then P else Q).dom := by
  rw [memC_even w _ _ k hk x]
  by_cases h : k < 4
  · simp only [if_pos h, tOddSet, Finset.mem_coe, hdO]
  · simp only [if_neg h, tEvenSet, Finset.mem_coe, hdE]

theorem even_respects (f : Word → JSlice) (w u1 u2 : Word) (hw : ¬ IsBase w) (hreg : regsAt w = (some u1, some u2))
    (hc : ¬ CorrectedAfterTwo w) (hl1 : u1.length < w.length) (hl2 : u2.length < w.length)
    (hdO : (f u1).tOdd.dom = Standard.oddTile u1) (hdE : (f u2).tEven.dom = Standard.evenTile u2)
    (hT1 : (Standard.stateAt w).tOdd = Standard.oddTile u1) (hT2 : (Standard.stateAt w).tEven = Standard.evenTile u2)
    (κ : ℕ → ℤ) (ge : Site → ℤ)
    (hge : ∀ i < (evenP w).length + (evenQ w).length,
      ∀ z ∈ keptSet (pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2)) (pieceFlag (evenP w)) dblEven i,
        ge z = placedEven w (f u1).tOdd.val (f u2).tEven.val 0 i z + κ i)
    (hall : ∀ k l, k < 6 → l < 6 → AgreeOn (fun i z => placedEven w (f u1).tOdd.val (f u2).tEven.val 0 i z + κ i)
      (pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2)) k l) :
    RespectsPieces ⟨Standard.evenTile w, ge⟩ (evenFull f w) := by
  have hget := evenFull_get f w u1 u2 hw hreg hc hl1 hl2
  have memC := memC_fullE w u1 u2 (f u1).tOdd (f u2).tEven hdO hdE
  have hfull : ∀ k < 6, ∀ x ∈ pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) k,
      ge x = placedEven w (f u1).tOdd.val (f u2).tEven.val 0 k x + κ k := by
    intro k hk x hx
    obtain ⟨j, hj, hxj⟩ := kept_cover _ _ _ k x hx
    rw [hge j (by rw [ClosedPathCycle.evenP_length, ClosedPathCycle.evenQ_length]; omega) x hxj]
    exact hall j k (by omega) hk x (keptSet_subset _ _ _ j hxj) hx
  have hidx : ∀ p ∈ evenFull f w, ∃ k < 6, p = stdPiece (if k < 4 then (f u1).tOdd else (f u2).tEven) (offE w k)
      (affEven (parentsAt w).odd (parentsAt w).even k) := by
    intro p hp
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hp
    have hk6 : k < 6 := by
      have := (List.getElem?_eq_some_iff.mp hk).1
      rwa [evenFull_length] at this
    rw [hget k hk6] at hk
    exact ⟨k, hk6, (Option.some.inj hk).symm⟩
  refine ⟨?_, fun p hp => ?_⟩
  · ext x
    show x ∈ Standard.evenTile w ↔ x ∈ pieceUnion (evenFull f w)
    rw [evenTile_union w u1 u2 hw hT1 hT2, JointGlue.mem_pieceUnion]
    constructor
    · rintro ⟨k, hk, hx⟩
      refine ⟨_, List.mem_of_getElem? (hget k hk), ?_⟩
      rw [mem_placed_std]
      by_cases h : k < 4
      · rw [if_pos h] at hx ⊢; rw [hdO]; exact hx
      · rw [if_neg h] at hx ⊢; rw [hdE]; exact hx
    · rintro ⟨p, hp, hx⟩
      obtain ⟨k, hk, rfl⟩ := hidx p hp
      rw [mem_placed_std] at hx
      refine ⟨k, hk, ?_⟩
      by_cases h : k < 4
      · rw [if_pos h] at hx ⊢; rw [← hdO]; exact hx
      · rw [if_neg h] at hx ⊢; rw [← hdE]; exact hx
  · obtain ⟨k, hk, rfl⟩ := hidx p hp
    refine ⟨κ k, fun x hx _ => ?_⟩
    rw [mem_placed_std] at hx
    have hxC := (memC k hk x).2 hx
    show ge x = _
    rw [hfull k hk x hxC, placedEven_eq]
    by_cases h : k < 4
    · simp only [if_pos h, stdPiece]
    · simp only [if_neg h, stdPiece]

theorem even_full (D : JointData) (hS : D.S = paperS) (hsl : WeakStepAssembly.TileSlopeZero D) (hsp : SameParentInput D)
    (f : Word → JSlice) (w u1 u2 : Word) (hgood : GoodBelow D f w.length) (hw : ¬ IsBase w)
    (hreg : regsAt w = (some u1, some u2)) (hc : ¬ CorrectedAfterTwo w) (κ : ℕ → ℤ) (go : Site → ℤ)
    (hM : MarksAgreeEven w u1 u2 (fun i z => placedEven w (f u1).tOdd.val (f u2).tEven.val 0 i z + κ i))
    (hD : DoubledAgreeEven w u1 u2 dblEven (fun i z => placedEven w (f u1).tOdd.val (f u2).tEven.val 0 i z + κ i))
    (hgo : ∀ i < (evenP w).length + (evenQ w).length,
      ∀ z ∈ keptSet (pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2)) (pieceFlag (evenP w)) dblEven i,
        go z = placedEven w (f u1).tOdd.val (f u2).tEven.val 0 i z + κ i) :
    RespectsPieces ⟨Standard.evenTile w, go⟩ (evenFull f w) := by
  have hl1 : u1.length < w.length := JointInduction.regsAt_lt w u1 (Or.inl (by rw [hreg]))
  have hl2 : u2.length < w.length := JointInduction.regsAt_lt w u2 (Or.inr (by rw [hreg]))
  have hp : (parentsAt u1).current .odd = (parentsAt w).odd :=
    ((WeakStepAssembly.regsAt_parents w).1 u1 (by rw [hreg])).symm
  have hq : (parentsAt u2).current .even = (parentsAt w).even :=
    ((WeakStepAssembly.regsAt_parents w).2 u2 (by rw [hreg])).symm
  obtain ⟨hS1, hJ1⟩ := hgood u1 hl1
  obtain ⟨hS2, hJ2⟩ := hgood u2 hl2
  have hdO : (f u1).tOdd.dom = Standard.oddTile u1 := by rw [(WeakStepAssembly.slice_domains D f u1 hS1).1, hS]; rfl
  have hdE : (f u2).tEven.dom = Standard.evenTile u2 := by rw [(WeakStepAssembly.slice_domains D f u2 hS2).2, hS]; rfl
  have hT1 : (Standard.stateAt w).tOdd = Standard.oddTile u1 := (WeakStepPaper.regsAt_tiles w).1 u1 (by rw [hreg])
  have hT2 : (Standard.stateAt w).tEven = Standard.evenTile u2 := (WeakStepPaper.regsAt_tiles w).2.2.1 u2 (by rw [hreg])
  -- corners and half-turns of the registers
  obtain ⟨αo, γo, -, hVo⟩ := TileTranslationStd.stdCorners_odd u1 (f u1).tOdd (WeakStepAssembly.slice_respects D f u1 hS1).1
  obtain ⟨αe, γe, -, hVe⟩ := TileTranslationStd.stdCorners_even u2 (f u2).tEven (WeakStepAssembly.slice_respects D f u2 hS2).2
  have hcP := corners_of _ _ _ _ _ _ hVo
  have hcQ := corners_of _ _ _ _ _ _ hVe
  rw [hdO, hp] at hcP
  rw [hdE, hq] at hcQ
  obtain ⟨⟨βo, hzo⟩, -⟩ := hsl f w.length hgood u1 hl1
  obtain ⟨-, ⟨βe, hze⟩⟩ := hsl f w.length hgood u2 hl2
  have hHP := raw_halfTurn _ _ _ _ hJ1.2.1.2.2.1 βo hzo
  have hHQ := raw_halfTurn _ _ _ _ hJ2.2.1.2.2.2.1 βe hze
  rw [hp] at hHP
  rw [hq] at hHQ
  obtain ⟨K, hK⟩ := even_rel w (f u1).tOdd (f u2).tEven κ hHP hHQ
  rw [hdO, hdE] at hK
  -- the agreements
  have hlen6 : (evenP w).length + (evenQ w).length = 6 := by
    rw [ClosedPathCycle.evenP_length, ClosedPathCycle.evenQ_length]
  have hmix : ∀ k l, k < 4 → 4 ≤ l → l < 6 → AgreeOn (fun i z => placedEven w (f u1).tOdd.val (f u2).tEven.val 0 i z + κ i)
      (pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2)) k l := by
    intro k l hk hl hl6 x hxk hxl
    have hfl : pieceFlag (evenP w) k ≠ pieceFlag (evenP w) l := by
      simp only [pieceFlag, ClosedPathCycle.evenP_length, ne_eq, decide_eq_decide]
      omega
    obtain ⟨m1, m2⟩ := ChildGlue.copies_mixed (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) (SiteInduction.marksOdd u1)
      (SiteInduction.marksEven u2) (fun a ha b hb z h1 h2 => MixedFromCells.mixedEven_all w hw u1 u2 hT1 hT2 a ha b hb z h1 h2)
      k l (by omega) (by omega) hfl x hxk hxl
    exact hM k l (by omega) (by omega) hfl x m1 m2
  have hdbl : ∀ j, j = 0 ∨ j = 2 → AgreeOn (fun i z => placedEven w (f u1).tOdd.val (f u2).tEven.val 0 i z + κ i)
      (pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2)) j (j + 1) := by
    intro j hj x h1 h2
    exact hD j (j + 1) (by omega) (by omega) (by omega)
      (by simp only [pieceFlag, ClosedPathCycle.evenP_length, decide_eq_decide]; omega)
      ⟨rfl, hj⟩ x h1 h2
  obtain ⟨k03, k12, k45⟩ := evenK w _ (Standard.oddTile u1) (Standard.evenTile u2) _ _ K hK hmix (hdbl 0 (Or.inl rfl))
    (hdbl 2 (Or.inr rfl)) hcP hcQ
  have hget := evenFull_get f w u1 u2 hw hreg hc hl1 hl2
  have memC := memC_fullE w u1 u2 (f u1).tOdd (f u2).tEven hdO hdE
  have conv : ∀ i j, i < 6 → j < 6 → PairCompat (evenFull f w) i j → ∃ c : ℤ,
      ∀ x ∈ pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) i,
        x ∈ pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) j →
          (placedEven w (f u1).tOdd.val (f u2).tEven.val 0 i x + κ i) -
            (placedEven w (f u1).tOdd.val (f u2).tEven.val 0 j x + κ j) = c := by
    intro i j hi hj h
    obtain ⟨c, hc'⟩ := h _ _ (hget i hi) (hget j hj)
    refine ⟨c + κ i - κ j, fun x hxi hxj => ?_⟩
    have e := hc' x ((mem_placed_std _ _ _ x).2 ((memC i hi x).1 hxi)) ((mem_placed_std _ _ _ x).2 ((memC j hj x).1 hxj))
      (by simp [stdPiece]) (by simp [stdPiece])
    rw [placedEven_eq, placedEven_eq]
    simp only [JointGlue.pieceVal, stdPiece] at e
    by_cases hi2 : i < 4 <;> by_cases hj2 : j < 4 <;> simp only [hi2, hj2, if_true, if_false] at e ⊢ <;> linarith
  have disj : ∀ i j, i < 6 → j < 6 → PairDisjoint (evenFull f w) i j →
      AgreeOn (fun i z => placedEven w (f u1).tOdd.val (f u2).tEven.val 0 i z + κ i)
        (pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2)) i j := by
    intro i j hi hj h x hxi hxj
    exact absurd ((mem_placed_std _ _ _ x).2 ((memC j hj x).1 hxj))
      (Finset.disjoint_left.mp (h _ _ (hget i hi) (hget j hj)) ((mem_placed_std _ _ _ x).2 ((memC i hi x).1 hxi)))
  obtain ⟨hd02, hd13, hc03, hc12, hc45⟩ := (hsp f w hgood hw).2 hc
  obtain ⟨c03, hc03'⟩ := conv 0 3 (by omega) (by omega) hc03
  obtain ⟨c12, hc12'⟩ := conv 1 2 (by omega) (by omega) hc12
  obtain ⟨c45, hc45'⟩ := conv 4 5 (by omega) (by omega) hc45
  have a03 := swapped_agree hK (i := 0) (by omega) (by decide) rfl k03 c03 hc03'
  have a12 := swapped_agree hK (i := 1) (by omega) (by decide) rfl k12 c12 hc12'
  have a45 := swapped_agree hK (i := 4) (by omega) (by decide) rfl k45 c45 hc45'
  have a02 := disj 0 2 (by omega) (by omega) hd02
  have a13 := disj 1 3 (by omega) (by omega) hd13
  have hlt : ∀ k l, k < l → l < 6 → AgreeOn (fun i z => placedEven w (f u1).tOdd.val (f u2).tEven.val 0 i z + κ i)
      (pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2)) k l := by
    intro k l hkl hl
    interval_cases l <;> interval_cases k
    all_goals first
      | exact a03 | exact a12 | exact a45 | exact a02 | exact a13
      | exact hdbl 0 (Or.inl rfl) | exact hdbl 2 (Or.inr rfl)
      | exact hmix _ _ (by omega) (by omega) (by omega)
  have hall : ∀ k l, k < 6 → l < 6 → AgreeOn (fun i z => placedEven w (f u1).tOdd.val (f u2).tEven.val 0 i z + κ i)
      (pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2)) k l := by
    intro k l hk hl
    rcases lt_trichotomy k l with h | rfl | h
    · exact hlt k l h hl
    · exact fun x _ _ => rfl
    · exact agreeOn_symm (hlt l k h hk)
  exact even_respects f w u1 u2 hw hreg hc hl1 hl2 hdO hdE hT1 hT2 κ go hgo hall


/-- **`GlueFullInput` from Case 1**: at the children that are not corrected, the glue on the kept parts respects the full
decomposition, given the geometric part of Case 1 (`SameParentInput`) and the normalisation of the registers. -/
theorem glueFullInput_of (D : JointData) (hS : D.S = paperS) (hsl : WeakStepAssembly.TileSlopeZero D)
    (hsp : SameParentInput D) : WeakStepAssembly.GlueFullInput D := by
  intro f w u1 u2 hgood hw hreg κo κe go ge hglue
  obtain ⟨hMo, hDo, hgo, hMe, hDe, hge⟩ := hglue
  exact ⟨fun hc => odd_full D hS hsl hsp f w u1 u2 hgood hw hreg hc κo go hMo hDo hgo,
    fun hc => even_full D hS hsl hsp f w u1 u2 hgood hw hreg hc κe ge hMe hDe hge⟩

/-! ### Case 1 from its parts: the swapped pairs through the grandparent copy

At a child that is not corrected, a swapped pair of copies `i`, `j` of one register that meet do so in one copy `G` of the
grandparent tile, which lies in the decomposition of the register in both frames, with the same affine factor (text, Case 1,
line 4557; numerics `tmp-w6/chk18.py`, `chk19.py`: the sub-copies are odd `(0,1) → (1,0)`, `(2,5) → (3,0)`, `(3,4) → (3,0)`,
even `(1,2) → (4,3)` or `(5,2)`, `(4,5) → (5,4)`; never an L-correction entry). -/

/-- The swap data of the entries `i`, `j` of `ps` through the decomposition `dec` of their register: when the two copies meet,
there are entries `X`, `Y` of `dec` with the same odometer and no exceptional points, placed at the same point in the two frames
(`off_i + off_X = off_j + off_Y`), with the same total affine factor, and the overlap lies in the copy of `X`. -/
def SwapData (ps : List Piece) (i j : ℕ) (dec : List Piece) : Prop :=
  ∀ p q : Piece, ps[i]? = some p → ps[j]? = some q → (∃ z, z ∈ p.placed ∧ z ∈ q.placed) →
    ∃ (X Y : ℕ) (pX pY : Piece), dec[X]? = some pX ∧ dec[Y]? = some pY ∧ pX.odo = pY.odo ∧ pX.exc = ∅ ∧
      pY.exc = ∅ ∧ p.off + pX.off = q.off + pY.off ∧ p.aff + pX.aff = q.aff + pY.aff ∧
      ∀ z ∈ p.placed, z ∈ q.placed → z - p.off ∈ pX.placed

/-- The decomposition of the odd tile odometer of `u`, over the family below `u` (`TilePart` at `u`). -/
abbrev decO (D : JointData) (f : Word → JSlice) (u : Word) : List Piece :=
  tileOddPieces D.S (fun v => (below f u v).tOdd) (fun v => (below f u v).tEven) (fun v => (below f u v).lEven) u

/-- The decomposition of the even tile odometer of `u`, over the family below `u`. -/
abbrev decE (D : JointData) (f : Word → JSlice) (u : Word) : List Piece :=
  tileEvenPieces D.S (fun v => (below f u v).tOdd) (fun v => (below f u v).tEven) (fun v => (below f u v).lOdd) u

/-- **Case 1, the overlap of a swapped pair** (text, lines 4545-4561, geometric part), at a register word that is not a base word:
the overlap of the two copies is the copy `G` of the grandparent tile (`SwapData`). Stated, not proved. -/
def SwapContainInput (D : JointData) : Prop :=
  D.S = paperS → ∀ (f : Word → JSlice) (w u1 u2 : Word), GoodBelow D f w.length → ¬ IsBase w →
    regsAt w = (some u1, some u2) →
    (¬ CorrectedAfterThree w →
      (¬ IsBase u1 → SwapData (oddFull f w) 0 1 (decO D f u1)) ∧
      (¬ IsBase u2 → SwapData (oddFull f w) 3 4 (decE D f u2) ∧ SwapData (oddFull f w) 2 5 (decE D f u2))) ∧
    (¬ CorrectedAfterTwo w →
      (¬ IsBase u1 → SwapData (evenFull f w) 0 3 (decO D f u1) ∧ SwapData (evenFull f w) 1 2 (decO D f u1)) ∧
      (¬ IsBase u2 → SwapData (evenFull f w) 4 5 (decE D f u2)))

/-- **Case 1, the base cases** (text, lines 4563-4569): at a register word that is a base word, the swapped pairs are compatible.
Stated, not proved. -/
def SwapBaseInput (D : JointData) : Prop :=
  D.S = paperS → ∀ (f : Word → JSlice) (w u1 u2 : Word), GoodBelow D f w.length → ¬ IsBase w →
    regsAt w = (some u1, some u2) →
    (¬ CorrectedAfterThree w →
      (IsBase u1 → PairCompat (oddFull f w) 0 1) ∧
      (IsBase u2 → PairCompat (oddFull f w) 3 4 ∧ PairCompat (oddFull f w) 2 5)) ∧
    (¬ CorrectedAfterTwo w →
      (IsBase u1 → PairCompat (evenFull f w) 0 3 ∧ PairCompat (evenFull f w) 1 2) ∧
      (IsBase u2 → PairCompat (evenFull f w) 4 5))

/-- **Case 1, the non-swapped pairs** (text, lines 4528-4543): the disjointness half of `SameParentInput`. Stated, not proved
here (w5: `SameParentStd.stdOdd_same_disjoint`, `stdEven_same_disjoint`). -/
def SameDisjointInput (D : JointData) : Prop :=
  D.S = paperS → ∀ (f : Word → JSlice) (w : Word), GoodBelow D f w.length → ¬ IsBase w →
    (¬ CorrectedAfterThree w → PairDisjoint (oddFull f w) 2 4 ∧ PairDisjoint (oddFull f w) 3 5) ∧
    (¬ CorrectedAfterTwo w → PairDisjoint (evenFull f w) 0 2 ∧ PairDisjoint (evenFull f w) 1 3)

/-- **Swap data give compatibility**: if both entries are copies of one odometer `R` that respects `dec`, the two placed pieces
differ by a constant on their overlap. -/
theorem pairCompat_of_swap (ps : List Piece) (i j : ℕ) (dec : List Piece) (R : PartialOdometer) (hR : RespectsPieces R dec)
    (hpi : ∀ p, ps[i]? = some p → p.odo = R ∧ p.exc = ∅) (hpj : ∀ q, ps[j]? = some q → q.odo = R ∧ q.exc = ∅)
    (h : SwapData ps i j dec) : PairCompat ps i j := by
  intro p q hp hq
  by_cases hm : ∃ z, z ∈ p.placed ∧ z ∈ q.placed
  · obtain ⟨X, Y, pX, pY, hX, hY, hodo, heX, heY, hoff, haff, hsub⟩ := h p q hp hq hm
    obtain ⟨bX, hbX⟩ := hR.2 pX (List.mem_of_getElem? hX)
    obtain ⟨bY, hbY⟩ := hR.2 pY (List.mem_of_getElem? hY)
    obtain ⟨hpo, -⟩ := hpi p hp
    obtain ⟨hqo, -⟩ := hpj q hq
    refine ⟨bX - bY - dotS pX.aff p.off + dotS pY.aff q.off, fun x hxp hxq _ _ => ?_⟩
    have h1 := hsub x hxp hxq
    have e : x - q.off - pY.off = x - p.off - pX.off := by
      have : q.off + pY.off = p.off + pX.off := hoff.symm
      rw [sub_sub, sub_sub, this]
    have h2 : x - q.off ∈ pY.placed := by
      rw [Piece.placed, Finset.mem_image] at h1 ⊢
      obtain ⟨y, hy, hyx⟩ := h1
      refine ⟨y, by rw [← hodo]; exact hy, ?_⟩
      have : y = x - p.off - pX.off := by rw [← hyx]; abel
      rw [this, ← e]; abel
    have v1 := hbX (x - p.off) h1 (by rw [heX]; exact Set.notMem_empty _)
    have v2 := hbY (x - q.off) h2 (by rw [heY]; exact Set.notMem_empty _)
    simp only [JointGlue.pieceVal, hpo, hqo]
    rw [v1, v2, hodo, e]
    have a1 : pX.aff.1 + p.aff.1 = pY.aff.1 + q.aff.1 := by
      have := congrArg Prod.fst haff; simp only [Prod.fst_add] at this; linarith
    have a2 : pX.aff.2 + p.aff.2 = pY.aff.2 + q.aff.2 := by
      have := congrArg Prod.snd haff; simp only [Prod.snd_add] at this; linarith
    simp only [dotS, Prod.fst_sub, Prod.snd_sub]
    linear_combination x.1 * a1 + x.2 * a2
  · exact ⟨0, fun x hxp hxq _ _ => absurd ⟨x, hxp, hxq⟩ hm⟩

/-- **`SameParentInput` from its parts**: the non-swapped pairs do not meet (`SameDisjointInput`); a swapped pair is compatible,
at a base register word by `SwapBaseInput`, and otherwise through the grandparent copy (`SwapContainInput`), since the register's
tile odometer respects its decomposition (`TilePart` at the register word). -/
theorem sameParent_of (D : JointData) (hS : D.S = paperS) (hdis : SameDisjointInput D) (hcon : SwapContainInput D)
    (hbas : SwapBaseInput D) : SameParentInput D := by
  intro f w hgood hw
  obtain ⟨u1, u2, hreg⟩ := WeakStepAssembly.regsAt_nonbase w hw
  have hl1 : u1.length < w.length := JointInduction.regsAt_lt w u1 (Or.inl (by rw [hreg]))
  have hl2 : u2.length < w.length := JointInduction.regsAt_lt w u2 (Or.inr (by rw [hreg]))
  have hRO : ¬ IsBase u1 → RespectsPieces (f u1).tOdd (decO D f u1) := fun hb =>
    (((hgood u1 hl1).1.2.2.1).2.1 hb).1
  have hRE : ¬ IsBase u2 → RespectsPieces (f u2).tEven (decE D f u2) := fun hb =>
    (((hgood u2 hl2).1.2.2.1).2.1 hb).2.1
  obtain ⟨dO, dE⟩ := hdis hS f w hgood hw
  obtain ⟨cO, cE⟩ := hcon hS f w u1 u2 hgood hw hreg
  obtain ⟨bO, bE⟩ := hbas hS f w u1 u2 hgood hw hreg
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · have hget := oddFull_get f w u1 u2 hw hreg hc hl1 hl2
    have od : ∀ k < 6, ∀ p, (oddFull f w)[k]? = some p →
        p.odo = (if k < 2 then (f u1).tOdd else (f u2).tEven) ∧ p.exc = ∅ := by
      intro k hk p hp
      rw [hget k hk] at hp
      cases hp
      exact ⟨rfl, rfl⟩
    have oP : ∀ k < 2, ∀ p, (oddFull f w)[k]? = some p → p.odo = (f u1).tOdd ∧ p.exc = ∅ := fun k hk p hp => by
      have := od k (by omega) p hp; rwa [if_pos hk] at this
    have oQ : ∀ k, 2 ≤ k → k < 6 → ∀ p, (oddFull f w)[k]? = some p → p.odo = (f u2).tEven ∧ p.exc = ∅ :=
      fun k hk hk6 p hp => by have := od k hk6 p hp; rwa [if_neg (by omega)] at this
    obtain ⟨d24, d35⟩ := dO hc
    obtain ⟨c1, c2⟩ := cO hc
    obtain ⟨b1, b2⟩ := bO hc
    have h01 : PairCompat (oddFull f w) 0 1 := by
      by_cases hb : IsBase u1
      · exact b1 hb
      · exact pairCompat_of_swap _ 0 1 _ _ (hRO hb) (oP 0 (by omega)) (oP 1 (by omega)) (c1 hb)
    have h34 : PairCompat (oddFull f w) 3 4 ∧ PairCompat (oddFull f w) 2 5 := by
      by_cases hb : IsBase u2
      · exact b2 hb
      · exact ⟨pairCompat_of_swap _ 3 4 _ _ (hRE hb) (oQ 3 (by omega) (by omega)) (oQ 4 (by omega) (by omega))
          (c2 hb).1, pairCompat_of_swap _ 2 5 _ _ (hRE hb) (oQ 2 (by omega) (by omega)) (oQ 5 (by omega) (by omega))
          (c2 hb).2⟩
    exact ⟨d24, d35, h01, h34.1, h34.2⟩
  · have hget := evenFull_get f w u1 u2 hw hreg hc hl1 hl2
    have od : ∀ k < 6, ∀ p, (evenFull f w)[k]? = some p →
        p.odo = (if k < 4 then (f u1).tOdd else (f u2).tEven) ∧ p.exc = ∅ := by
      intro k hk p hp
      rw [hget k hk] at hp
      cases hp
      exact ⟨rfl, rfl⟩
    have oP : ∀ k < 4, ∀ p, (evenFull f w)[k]? = some p → p.odo = (f u1).tOdd ∧ p.exc = ∅ := fun k hk p hp => by
      have := od k (by omega) p hp; rwa [if_pos hk] at this
    have oQ : ∀ k, 4 ≤ k → k < 6 → ∀ p, (evenFull f w)[k]? = some p → p.odo = (f u2).tEven ∧ p.exc = ∅ :=
      fun k hk hk6 p hp => by have := od k hk6 p hp; rwa [if_neg (by omega)] at this
    obtain ⟨d02, d13⟩ := dE hc
    obtain ⟨c1, c2⟩ := cE hc
    obtain ⟨b1, b2⟩ := bE hc
    have h03 : PairCompat (evenFull f w) 0 3 ∧ PairCompat (evenFull f w) 1 2 := by
      by_cases hb : IsBase u1
      · exact b1 hb
      · exact ⟨pairCompat_of_swap _ 0 3 _ _ (hRO hb) (oP 0 (by omega)) (oP 3 (by omega)) (c1 hb).1,
          pairCompat_of_swap _ 1 2 _ _ (hRO hb) (oP 1 (by omega)) (oP 2 (by omega)) (c1 hb).2⟩
    have h45 : PairCompat (evenFull f w) 4 5 := by
      by_cases hb : IsBase u2
      · exact b2 hb
      · exact pairCompat_of_swap _ 4 5 _ _ (hRE hb) (oQ 4 (by omega) (by omega)) (oQ 5 (by omega) (by omega)) (c2 hb)
    exact ⟨d02, d13, h03.1, h03.2, h45⟩

/-- **`SameDisjointInput` for the paper data**, from the strip-functional separation of `SameParentStd`
(`stdOdd_same_disjoint`, `stdEven_same_disjoint`) on the six copies of the children. -/
theorem sameDisjoint_paper (D : JointData) : SameDisjointInput D := by
  intro hS f w hgood hw
  obtain ⟨u1, u2, hreg⟩ := WeakStepAssembly.regsAt_nonbase w hw
  have hl1 : u1.length < w.length := JointInduction.regsAt_lt w u1 (Or.inl (by rw [hreg]))
  have hl2 : u2.length < w.length := JointInduction.regsAt_lt w u2 (Or.inr (by rw [hreg]))
  have hp := (WeakStepAssembly.regsAt_parents w).1 u1 (by rw [hreg])
  have hq := (WeakStepAssembly.regsAt_parents w).2 u2 (by rw [hreg])
  obtain ⟨hS1, -⟩ := hgood u1 hl1
  obtain ⟨hS2, -⟩ := hgood u2 hl2
  have hdO : (f u1).tOdd.dom = Standard.oddTile u1 := by rw [(WeakStepAssembly.slice_domains D f u1 hS1).1, hS]; rfl
  have hdE : (f u2).tEven.dom = Standard.evenTile u2 := by rw [(WeakStepAssembly.slice_domains D f u2 hS2).2, hS]; rfl
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · have hd : w.getLast? ≠ some Digit.three := fun h => hc ⟨hw, h⟩
    have hget := oddFull_get f w u1 u2 hw hreg hc hl1 hl2
    have memC := memC_full w u1 u2 (f u1).tOdd (f u2).tEven hdO hdE
    have disj : ∀ i j, i < 6 → j < 6 →
        ((i = 2 ∧ j = 4) ∨ (i = 4 ∧ j = 2) ∨ (i = 3 ∧ j = 5) ∨ (i = 5 ∧ j = 3)) → PairDisjoint (oddFull f w) i j := by
      intro i j hi hj hij p q hpi hqj
      rw [hget i hi] at hpi
      rw [hget j hj] at hqj
      cases hpi
      cases hqj
      refine Finset.disjoint_left.2 fun x hxp hxq => ?_
      rw [mem_placed_std] at hxp hxq
      exact SameParentStd.stdOdd_same_disjoint w u1 u2 hw hp hq hd i j hij x ((memC i hi x).2 hxp) ((memC j hj x).2 hxq)
    exact ⟨disj 2 4 (by omega) (by omega) (Or.inl ⟨rfl, rfl⟩), disj 3 5 (by omega) (by omega) (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩
  · have hd : w.getLast? ≠ some Digit.two := fun h => hc ⟨hw, h⟩
    have hget := evenFull_get f w u1 u2 hw hreg hc hl1 hl2
    have memC := memC_fullE w u1 u2 (f u1).tOdd (f u2).tEven hdO hdE
    have disj : ∀ i j, i < 6 → j < 6 →
        ((i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) ∨ (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1)) → PairDisjoint (evenFull f w) i j := by
      intro i j hi hj hij p q hpi hqj
      rw [hget i hi] at hpi
      rw [hget j hj] at hqj
      cases hpi
      cases hqj
      refine Finset.disjoint_left.2 fun x hxp hxq => ?_
      rw [mem_placed_std] at hxp hxq
      exact SameParentStd.stdEven_same_disjoint w u1 u2 hw hp hq hd i j hij x ((memC i hi x).2 hxp) ((memC j hj x).2 hxq)
    exact ⟨disj 0 2 (by omega) (by omega) (Or.inl ⟨rfl, rfl⟩), disj 1 3 (by omega) (by omega) (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩

end FLatticePaper.Tiles.GlueFull
