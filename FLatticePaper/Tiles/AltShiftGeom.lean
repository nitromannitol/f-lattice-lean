import FLatticePaper.Tiles.AltLatticeOddW

/-! # The overlap of a register with its translate by the alternate shift: the closed forms

The alternate decompositions double the odd register `T(p)` with the shift `S_p` and the even register `T(q)` with `S_q`
(`SurgicalDict.altShifts`: `S_p = ∓v_{q,1} + v_{p,2}`, `S_q = ±v_{q,1} + v_{p,2}`, the upper sign when `W₁` is odd). On the closed
forms `H_p`, `H_q`:
* `t_p(S_p) = -T_p - 1` in both orientations (`n_p d_q - n_q d_p = ±1`), so a point `x` of `T(p)` with `x + S_p` in `T(p)` has
  `x + v_{p,2}` and `x + S_p - v_{p,2}` in `T(p)`: `x` is on the bottom walk and `x + S_p` on the top walk (`geomP`);
* `s_q(S_q) = ±(T_q + 2)`, so a point `x` of `T(q)` with `x + S_q` in `T(q)` is on the left walk (`x + v_{q,1}` in `T(q)`) and
  `x + S_q` on the right walk when `W₁` is odd, and the other way round when `W₁` is even (`geomQ`). -/

namespace FLatticePaper.Tiles.AltShiftGeom

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open FLatticePaper.Tiles.Standard (IsBase)
open FLatticePaper.Tiles.SiteInduction (InH tCo sCo tOf aOf lOf)

theorem tCo_add (f : Fraction) (x v : Site) : tCo f (x + v) = tCo f x + tCo f v := by
  simp only [tCo, Prod.fst_add, Prod.snd_add]; ring

theorem sCo_add (f : Fraction) (x v : Site) : sCo f (x + v) = sCo f x + sCo f v := by
  simp only [sCo, Prod.fst_add, Prod.snd_add]; ring

theorem tCo_sub (f : Fraction) (x v : Site) : tCo f (x - v) = tCo f x - tCo f v := by
  simp only [tCo, Prod.fst_sub, Prod.snd_sub]; ring

theorem sCo_sub (f : Fraction) (x v : Site) : sCo f (x - v) = sCo f x - sCo f v := by
  simp only [sCo, Prod.fst_sub, Prod.snd_sub]; ring

theorem par_sub (z v : Site) (hv : (v.1 + v.2) % 2 = 0) :
    decide (((z - v).1 + (z - v).2) % 2 = 0) = decide ((z.1 + z.2) % 2 = 0) := by
  simp only [Prod.fst_sub, Prod.snd_sub, decide_eq_decide]
  omega

/-- **Bottom and top walks.** If `t(B) = -T`, `s(B) = 0` and `t(S) = -T - 1` (`B`, `S` even), a point `x` with `x, x + S` in `H_f`
has `x + B` and `x + S - B` in `H_f`. -/
theorem geom_bt (f : Fraction) (hT : 0 < tOf f) (B S x : Site) (hB : (B.1 + B.2) % 2 = 0) (hS : (S.1 + S.2) % 2 = 0)
    (htB : tCo f B = -tOf f) (hsB : sCo f B = 0) (htS : tCo f S = -tOf f - 1)
    (hx : InH f x) (hxS : InH f (x + S)) : InH f (x + B) ∧ InH f (x + S - B) := by
  have pB := AltLatticeOddW.decide_par_add x B hB
  have pS := AltLatticeOddW.decide_par_add x S hS
  have pSB : decide (((x + S - B).1 + (x + S - B).2) % 2 = 0) = decide ((x.1 + x.2) % 2 = 0) := by
    rw [par_sub _ _ hB, pS]
  unfold InH at hx hxS ⊢
  rw [pS] at hxS
  rw [pB, pSB, tCo_add, sCo_add, tCo_sub, sCo_sub, tCo_add, sCo_add]
  rw [tCo_add, sCo_add] at hxS
  obtain ⟨a1, a2, a3, a4⟩ := hx
  obtain ⟨b1, b2, b3, b4⟩ := hxS
  exact ⟨⟨by linarith, by linarith, by linarith, by linarith⟩, ⟨by linarith, by linarith, by linarith, by linarith⟩⟩

/-- **Left and right walks, `s(S) = T + 2`.** If `t(U) = 0`, `s(U) = T`, `μ = 1`, a point `x` with `x, x + S` in `H_f` has `x + U`
and `x + S - U` in `H_f`. -/
theorem geom_lr_plus (f : Fraction) (hT : 0 < tOf f) (hmu : SiteInduction.muOf f = 1) (U S x : Site) (hU : (U.1 + U.2) % 2 = 0)
    (hS : (S.1 + S.2) % 2 = 0) (htU : tCo f U = 0) (hsU : sCo f U = tOf f) (hsS : sCo f S = tOf f + 2)
    (hx : InH f x) (hxS : InH f (x + S)) : InH f (x + U) ∧ InH f (x + S - U) := by
  have pU := AltLatticeOddW.decide_par_add x U hU
  have pS := AltLatticeOddW.decide_par_add x S hS
  have pSU : decide (((x + S - U).1 + (x + S - U).2) % 2 = 0) = decide ((x.1 + x.2) % 2 = 0) := by
    rw [par_sub _ _ hU, pS]
  unfold InH at hx hxS ⊢
  rw [pS] at hxS
  rw [pU, pSU, tCo_add, sCo_add, tCo_sub, sCo_sub, tCo_add, sCo_add, hmu]
  rw [tCo_add, sCo_add, hmu] at hxS
  rw [hmu] at hx
  obtain ⟨a1, a2, a3, a4⟩ := hx
  obtain ⟨b1, b2, b3, b4⟩ := hxS
  exact ⟨⟨by linarith, by linarith, by linarith, by linarith⟩, ⟨by linarith, by linarith, by linarith, by linarith⟩⟩

/-- **Left and right walks, `s(S) = -T - 2`.** A point `x` with `x, x + S` in `H_f` has `x - U` and `x + S + U` in `H_f`. -/
theorem geom_lr_minus (f : Fraction) (hT : 0 < tOf f) (hmu : SiteInduction.muOf f = 1) (U S x : Site) (hU : (U.1 + U.2) % 2 = 0)
    (hS : (S.1 + S.2) % 2 = 0) (htU : tCo f U = 0) (hsU : sCo f U = tOf f) (hsS : sCo f S = -tOf f - 2)
    (hx : InH f x) (hxS : InH f (x + S)) : InH f (x - U) ∧ InH f (x + S + U) := by
  have pU := par_sub x U hU
  have pS := AltLatticeOddW.decide_par_add x S hS
  have pSU : decide (((x + S + U).1 + (x + S + U).2) % 2 = 0) = decide ((x.1 + x.2) % 2 = 0) := by
    rw [AltLatticeOddW.decide_par_add _ _ hU, pS]
  unfold InH at hx hxS ⊢
  rw [pS] at hxS
  rw [pU, pSU, tCo_sub, sCo_sub, tCo_add, sCo_add, tCo_add, sCo_add, hmu]
  rw [tCo_add, sCo_add, hmu] at hxS
  rw [hmu] at hx
  obtain ⟨a1, a2, a3, a4⟩ := hx
  obtain ⟨b1, b2, b3, b4⟩ := hxS
  exact ⟨⟨by linarith, by linarith, by linarith, by linarith⟩, ⟨by linarith, by linarith, by linarith, by linarith⟩⟩

/-- The alternate shift of the odd register of `w`. -/
abbrev shP (w : Word) : Site :=
  (SurgicalDict.altShifts (phase w == 1) (texV2 (parentsAt w).odd) (texV1Even (parentsAt w).even)).1

/-- The alternate shift of the even register of `w`. -/
abbrev shQ (w : Word) : Site :=
  (SurgicalDict.altShifts (phase w == 1) (texV2 (parentsAt w).odd) (texV1Even (parentsAt w).even)).2

/-- **The odd register**: `x, x + S_p` in `H_p` give `x + v_{p,2}` and `x + S_p - v_{p,2}` in `H_p`. -/
theorem geomP {w : Word} (hw : ¬ IsBase w) (x : Site) (hx : InH (parentsAt w).odd x)
    (hxS : InH (parentsAt w).odd (x + shP w)) :
    InH (parentsAt w).odd (x + texV2 (parentsAt w).odd) ∧ InH (parentsAt w).odd (x + shP w - texV2 (parentsAt w).odd) := by
  obtain ⟨h1, h2, h3, h4, hpo, hqe, hdet⟩ := AltPieces.parents_facts hw
  have hT : 0 < tOf (parentsAt w).odd := by
    simp only [tOf]; nlinarith
  refine geom_bt _ hT _ _ x (by simp only [texV2]; omega) ?_ ?_ ?_ ?_ hx hxS
  · simp only [shP, SurgicalDict.altShifts]; split_ifs <;> simp only [texV2, texV1Even, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg] <;> omega
  · simp only [tCo, tOf, texV2]; ring
  · simp only [sCo, texV2]; ring
  · rcases Bool.eq_false_or_eq_true (phase w == 1) with h | h
    · have hph : phase w = 1 := by simpa using h
      rw [if_pos hph] at hdet
      simp only [shP, h, SurgicalDict.altShifts, if_true, tCo, tOf, texV2, texV1Even, Prod.fst_add, Prod.snd_add, Prod.fst_neg,
        Prod.snd_neg]
      linarith
    · have hph : ¬ phase w = 1 := by simpa using h
      rw [if_neg hph] at hdet
      simp only [shP, h, SurgicalDict.altShifts, Bool.false_eq_true, if_false, tCo, tOf, texV2, texV1Even, Prod.fst_add,
        Prod.snd_add]
      linarith

/-- **The even register**: `x, x + S_q` in `H_q` give, when `W₁` is odd, `x + v_{q,1}` and `x + S_q - v_{q,1}` in `H_q`, and when
`W₁` is even, `x - v_{q,1}` and `x + S_q + v_{q,1}`. -/
theorem geomQ {w : Word} (hw : ¬ IsBase w) (x : Site) (hx : InH (parentsAt w).even x)
    (hxS : InH (parentsAt w).even (x + shQ w)) :
    (phase w = 1 → InH (parentsAt w).even (x + texV1Even (parentsAt w).even) ∧
      InH (parentsAt w).even (x + shQ w - texV1Even (parentsAt w).even)) ∧
    (phase w ≠ 1 → InH (parentsAt w).even (x - texV1Even (parentsAt w).even) ∧
      InH (parentsAt w).even (x + shQ w + texV1Even (parentsAt w).even)) := by
  obtain ⟨h1, h2, h3, h4, hpo, hqe, hdet⟩ := AltPieces.parents_facts hw
  obtain ⟨-, -, -, hmq⟩ := AltItem5.parent_hyps hw
  have hT : 0 < tOf (parentsAt w).even := by
    simp only [tOf]; nlinarith
  have pU : ((texV1Even (parentsAt w).even).1 + (texV1Even (parentsAt w).even).2) % 2 = 0 := by
    simp only [texV1Even]; omega
  have pS : ((shQ w).1 + (shQ w).2) % 2 = 0 := by
    simp only [shQ, SurgicalDict.altShifts]; split_ifs <;> simp only [texV2, texV1Even, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg] <;> omega
  have htU : tCo (parentsAt w).even (texV1Even (parentsAt w).even) = 0 := by simp only [tCo, texV1Even]; ring
  have hsU : sCo (parentsAt w).even (texV1Even (parentsAt w).even) = tOf (parentsAt w).even := by
    simp only [sCo, tOf, texV1Even]; ring
  refine ⟨fun hph => ?_, fun hph => ?_⟩
  · have h : (phase w == 1) = true := by simpa using hph
    rw [if_pos hph] at hdet
    refine geom_lr_plus _ hT hmq _ _ x pU pS htU hsU ?_ hx hxS
    simp only [shQ, h, SurgicalDict.altShifts, if_true, sCo, tOf, texV2, texV1Even, Prod.fst_add, Prod.snd_add]
    linarith
  · have h : (phase w == 1) = false := by simpa using hph
    rw [if_neg hph] at hdet
    refine geom_lr_minus _ hT hmq _ _ x pU pS htU hsU ?_ hx hxS
    simp only [shQ, h, SurgicalDict.altShifts, Bool.false_eq_true, if_false, sCo, tOf, texV2, texV1Even, Prod.fst_add,
      Prod.snd_add, Prod.fst_neg, Prod.snd_neg]
    linarith

end FLatticePaper.Tiles.AltShiftGeom
