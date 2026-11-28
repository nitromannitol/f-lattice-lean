import FLatticePaper.Tiles.AltParentEven
import FLatticePaper.Tiles.AltSixEvenOF
import FLatticePaper.Tiles.AltSixOdd
import FLatticePaper.Construction.BaseCaseRecurrence
import FLatticePaper.Construction.NearOneBaseCases

/-! # Case 3 at a base parent word: the contacts of the parent piece with the standard copies

At `w = v d` with `v = 3^k` or `2^k`, the parent piece is an explicit base alternate tile (`PaperAltBaseCond`). Each copy has a
corner inside it, where both values are explicit: the copy's from the corner values of its register, the parent's from the base
formula. -/

namespace FLatticePaper.Tiles.AltBaseContacts

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.SiteInduction
open FLatticePaper.Tiles.ChildGlue FLatticePaper.Tiles.ClosedPathAssembly FLatticePaper.Tiles.ClosedPathSum
open FLatticePaper.Tiles.ClosedPathAlt FLatticePaper.Tiles.StandardClause
open FLatticePaper.Tiles.AltParentConstants FLatticePaper.Tiles.AltSixEven FLatticePaper.Tiles.AltParentEven
open FLatticePaper.Tiles.AltSixOdd
open FLatticePaper.Tiles.JointFamily (h0)

theorem base_ae31_0 (k : ℕ) (hk : 1 ≤ k) (w u1 u2 : Word) (hph : phase w = 1)
    (hrel : (parentsAt w).odd.num = (1) ∧ (parentsAt w).odd.den = (2 * (k : ℤ) + 2) ∧ (parentsAt w).even.num = (1) ∧
      (parentsAt w).even.den = (2 * (k : ℤ) + 3))
    (oP oQ oH : PartialOdometer) (βP βQ : ℤ)
    (_hdP : oP.dom = Standard.oddTile u1) (hdQ : oQ.dom = Standard.evenTile u2)
    (_hcP : TileTranslation.StdCornerValues oP 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (hcQ : TileTranslation.StdCornerValues oQ 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (hdH : ∀ x : ℤ × ℤ, x ∈ oH.dom ↔ x + ((-1 : ℤ), (-1 : ℤ)) ∈ paperLadderAltTile (2 * (k : ℤ) + 2))
    (hvH : ∀ x ∈ oH.dom, oH.val x = paperLadderAltValue (2 * (k : ℤ) + 2) (x + ((-1 : ℤ), (-1 : ℤ))))
    (hpc : ∃ C : ℤ, ∀ z, z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAE w u1 u2 0 →
      oH.val (z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z - placedAltEven w oP.val oQ.val 0 0 z = C) :
    ∀ z, z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAE w u1 u2 0 →
      oH.val (z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z + (-h0 (texV2 (parentsAt w).odd) + ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2)) = placedAltEven w oP.val oQ.val (AltSixEvenOF.kEvenOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 0 z := by
  obtain ⟨hD, hR, hAf, hSh⟩ := altEven_of w hph
  obtain ⟨C, hC⟩ := hpc
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hrel
  have hB4 := h0_even (texV2 (parentsAt w).odd) (by simp only [texV2]; omega)
  have hV4 := h0_even (texV2 (parentsAt w).even) (by simp only [texV2]; omega)
  have mQ := corner_mem _ _ _ _ _ _ hcQ
  have vQ := corner_raw _ _ _ _ _ hcQ
  rw [hdQ] at mQ
  set p := (parentsAt w).odd with hpdef
  set q := (parentsAt w).even with hqdef
  set A := texV1Odd p with hA
  set B := texV2 p with hBd
  set U := texV1Even q with hU
  set V := texV2 q with hV
  set S := shiftQ w with hSdef
  have ez : A + (V + ((1 : ℤ), (0 : ℤ))) - (B + U) + ((-1 : ℤ), (-1 : ℤ)) = ((2 * (k : ℤ)), (1)) := by
    ext <;> simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, hr1, hr2, hr3, hr4] <;> ring
  have m1 : A + (V + ((1 : ℤ), (0 : ℤ))) - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) := by
    rw [Finset.mem_coe, hdH, show A + (V + ((1 : ℤ), (0 : ℤ))) - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) = A + (V + ((1 : ℤ), (0 : ℤ))) - (B + U) from rfl, ez]
    simp only [paperLadderAltTile, paperLadderAltA, paperLadderAltB, paperLadderAltC, paperLadderAltD, Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq]
    omega
  have m2 : A + (V + ((1 : ℤ), (0 : ℤ))) ∈ ClosedPathAlt.dAE w u1 u2 0 := by
    have hdj : ClosedPathAlt.dAE w u1 u2 0 = shiftS (tEvenSet u2) (A) := by simp [ClosedPathAlt.dAE, pieceSet, hD]
    rw [hdj]
    exact mem_shift _ _ _ (V + ((1 : ℤ), (0 : ℤ))) mQ.2.2.2.2.1 (by abel)
  have h1 := hC _ m1 m2
  have hval : paperLadderAltValue (2 * (k : ℤ) + 2) ((2 * (k : ℤ)), (1)) = (-1) := by
    have hq : ((1) : ℤ) * ((1) + 1) = 2 * (1) + 0 := by ring
    simp only [paperLadderAltValue, Set.indicator_apply, Set.mem_union, paperLadderAltA, paperLadderAltB, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_setOf_eq, Prod.mk.injEq]
    split_ifs <;> (try simp only [and_false, false_or,
      not_or, not_and] at *) <;> omega
  rw [hvH _ m1, ez, hval] at h1
  rw [eval_lt w _ _ 0 0 _ (A) 0 (V + ((1 : ℤ), (0 : ℤ))) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) (by abel), vQ.2.2.2.2.1] at h1
  intro z hz1 hz2
  have h2 := hC z hz1 hz2
  rw [← placedAltEven_add]
  simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero, dot2, AltSixEvenOF.kEvenOF, Pi.zero_apply, zero_mul, add_zero, hr1, hr2, hr3, hr4] at h1 h2 hB4 hV4 ⊢
  try simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, Prod.fst_neg, Prod.snd_neg, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, dotS, dot2, AltSixEvenOF.kEvenOF, hr1, hr2, hr3, hr4] at h1
  linarith

theorem base_ae31_1 (k : ℕ) (hk : 1 ≤ k) (w u1 u2 : Word) (hph : phase w = 1)
    (hrel : (parentsAt w).odd.num = (1) ∧ (parentsAt w).odd.den = (2 * (k : ℤ) + 2) ∧ (parentsAt w).even.num = (1) ∧
      (parentsAt w).even.den = (2 * (k : ℤ) + 3))
    (oP oQ oH : PartialOdometer) (βP βQ : ℤ)
    (_hdP : oP.dom = Standard.oddTile u1) (hdQ : oQ.dom = Standard.evenTile u2)
    (_hcP : TileTranslation.StdCornerValues oP 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (hcQ : TileTranslation.StdCornerValues oQ 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (hdH : ∀ x : ℤ × ℤ, x ∈ oH.dom ↔ x + ((-1 : ℤ), (-1 : ℤ)) ∈ paperLadderAltTile (2 * (k : ℤ) + 2))
    (hvH : ∀ x ∈ oH.dom, oH.val x = paperLadderAltValue (2 * (k : ℤ) + 2) (x + ((-1 : ℤ), (-1 : ℤ))))
    (hpc : ∃ C : ℤ, ∀ z, z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAE w u1 u2 1 →
      oH.val (z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z - placedAltEven w oP.val oQ.val 0 1 z = C) :
    ∀ z, z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAE w u1 u2 1 →
      oH.val (z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z + (-h0 (texV2 (parentsAt w).odd) + ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2)) = placedAltEven w oP.val oQ.val (AltSixEvenOF.kEvenOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 1 z := by
  obtain ⟨hD, hR, hAf, hSh⟩ := altEven_of w hph
  obtain ⟨C, hC⟩ := hpc
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hrel
  have hB4 := h0_even (texV2 (parentsAt w).odd) (by simp only [texV2]; omega)
  have hV4 := h0_even (texV2 (parentsAt w).even) (by simp only [texV2]; omega)
  have mQ := corner_mem _ _ _ _ _ _ hcQ
  have vQ := corner_raw _ _ _ _ _ hcQ
  rw [hdQ] at mQ
  set p := (parentsAt w).odd with hpdef
  set q := (parentsAt w).even with hqdef
  set A := texV1Odd p with hA
  set B := texV2 p with hBd
  set U := texV1Even q with hU
  set V := texV2 q with hV
  set S := shiftQ w with hSdef
  have ez : S + A + (V + ((1 : ℤ), (-1 : ℤ))) - (B + U) + ((-1 : ℤ), (-1 : ℤ)) = ((2 * (k : ℤ) + 2), (2 * (k : ℤ) + 4)) := by
    rw [hSh]; ext <;> simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, hr1, hr2, hr3, hr4] <;> ring
  have m1 : S + A + (V + ((1 : ℤ), (-1 : ℤ))) - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) := by
    rw [Finset.mem_coe, hdH, show S + A + (V + ((1 : ℤ), (-1 : ℤ))) - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) = S + A + (V + ((1 : ℤ), (-1 : ℤ))) - (B + U) from rfl, ez]
    simp only [paperLadderAltTile, paperLadderAltA, paperLadderAltB, paperLadderAltC, paperLadderAltD, Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq, true_and]
    omega
  have m2 : S + A + (V + ((1 : ℤ), (-1 : ℤ))) ∈ ClosedPathAlt.dAE w u1 u2 1 := by
    have hdj : ClosedPathAlt.dAE w u1 u2 1 = shiftS (tEvenSet u2) (S + A) := by simp [ClosedPathAlt.dAE, pieceSet, hD]
    rw [hdj]
    exact mem_shift _ _ _ (V + ((1 : ℤ), (-1 : ℤ))) mQ.2.2.2.2.2.1 (by abel)
  have h1 := hC _ m1 m2
  have hval : paperLadderAltValue (2 * (k : ℤ) + 2) ((2 * (k : ℤ) + 2), (2 * (k : ℤ) + 4)) = (-2 * (k : ℤ) ^ 2 - 7 * (k : ℤ) - 6) := by
    have hq : ((2 * (k : ℤ) + 4) : ℤ) * ((2 * (k : ℤ) + 4) + 1) = 2 * (2 * (k : ℤ) ^ 2 + 9 * (k : ℤ) + 10) + 0 := by ring
    simp only [paperLadderAltValue, Set.indicator_apply, Set.mem_union, paperLadderAltA, paperLadderAltB, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_setOf_eq, Prod.mk.injEq, true_and]
    split_ifs <;> (try simp only [not_or, not_and] at *) <;> omega
  rw [hvH _ m1, ez, hval] at h1
  rw [eval_lt w _ _ 0 1 _ (S + A) (p.num, -p.den) (V + ((1 : ℤ), (-1 : ℤ))) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) (by abel), vQ.2.2.2.2.2.1] at h1
  intro z hz1 hz2
  have h2 := hC z hz1 hz2
  rw [← placedAltEven_add]
  simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, dot2, AltSixEvenOF.kEvenOF, Pi.zero_apply, add_zero, hr1, hr2, hr3, hr4] at h1 h2 hB4 hV4 ⊢
  rw [hSh] at h1
  try simp only [hBd, hU, texV1Even, texV2, Prod.fst_add, Prod.snd_add, hr1, hr2, hr3, hr4] at h1
  linarith

theorem base_ae31_2 (k : ℕ) (hk : 1 ≤ k) (w u1 u2 : Word) (hph : phase w = 1)
    (hrel : (parentsAt w).odd.num = (1) ∧ (parentsAt w).odd.den = (2 * (k : ℤ) + 2) ∧ (parentsAt w).even.num = (1) ∧
      (parentsAt w).even.den = (2 * (k : ℤ) + 3))
    (oP oQ oH : PartialOdometer) (βP βQ : ℤ)
    (_hdP : oP.dom = Standard.oddTile u1) (hdQ : oQ.dom = Standard.evenTile u2)
    (_hcP : TileTranslation.StdCornerValues oP 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (hcQ : TileTranslation.StdCornerValues oQ 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (hdH : ∀ x : ℤ × ℤ, x ∈ oH.dom ↔ x + ((-1 : ℤ), (-1 : ℤ)) ∈ paperLadderAltTile (2 * (k : ℤ) + 2))
    (hvH : ∀ x ∈ oH.dom, oH.val x = paperLadderAltValue (2 * (k : ℤ) + 2) (x + ((-1 : ℤ), (-1 : ℤ))))
    (hpc : ∃ C : ℤ, ∀ z, z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAE w u1 u2 2 →
      oH.val (z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z - placedAltEven w oP.val oQ.val 0 2 z = C) :
    ∀ z, z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAE w u1 u2 2 →
      oH.val (z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z + (-h0 (texV2 (parentsAt w).odd) + ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2)) = placedAltEven w oP.val oQ.val (AltSixEvenOF.kEvenOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 2 z := by
  obtain ⟨hD, hR, hAf, hSh⟩ := altEven_of w hph
  obtain ⟨C, hC⟩ := hpc
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hrel
  have hB4 := h0_even (texV2 (parentsAt w).odd) (by simp only [texV2]; omega)
  have hV4 := h0_even (texV2 (parentsAt w).even) (by simp only [texV2]; omega)
  have mQ := corner_mem _ _ _ _ _ _ hcQ
  have vQ := corner_raw _ _ _ _ _ hcQ
  rw [hdQ] at mQ
  set p := (parentsAt w).odd with hpdef
  set q := (parentsAt w).even with hqdef
  set A := texV1Odd p with hA
  set B := texV2 p with hBd
  set U := texV1Even q with hU
  set V := texV2 q with hV
  set S := shiftQ w with hSdef
  have ez : B + (U) - (B + U) + ((-1 : ℤ), (-1 : ℤ)) = ((-1), (-1)) := by
    ext <;> simp only [hBd, hU, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, hr1, hr2, hr3, hr4] <;> ring
  have m1 : B + (U) - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) := by
    rw [Finset.mem_coe, hdH, show B + (U) - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) = B + (U) - (B + U) from rfl, ez]
    simp only [paperLadderAltTile, paperLadderAltA, paperLadderAltB, paperLadderAltC, paperLadderAltD, Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq, true_and, true_or]
    omega
  have m2 : B + (U) ∈ ClosedPathAlt.dAE w u1 u2 2 := by
    have hdj : ClosedPathAlt.dAE w u1 u2 2 = shiftS (tEvenSet u2) (B) := by simp [ClosedPathAlt.dAE, pieceSet, hD]
    rw [hdj]
    exact mem_shift _ _ _ (U) mQ.2.2.2.1 (by abel)
  have h1 := hC _ m1 m2
  have hval : paperLadderAltValue (2 * (k : ℤ) + 2) ((-1), (-1)) = (0) := by
    have hq : ((-1) : ℤ) * ((-1) + 1) = 2 * (0) + 0 := by ring
    simp only [paperLadderAltValue, Set.indicator_apply, Set.mem_union, paperLadderAltA, paperLadderAltB, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_setOf_eq, Prod.mk.injEq, true_or]
    split_ifs <;> (try simp only [not_true_eq_false] at *); omega
  rw [hvH _ m1, ez, hval] at h1
  rw [eval_lt w _ _ 0 2 _ (B) (p.num, -p.den) (U) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) (by abel), vQ.2.2.2.1] at h1
  intro z hz1 hz2
  have h2 := hC z hz1 hz2
  rw [← placedAltEven_add]
  simp only [hBd, hU, hV, texV1Even, texV2, Prod.fst_add, Prod.snd_add, dot2, AltSixEvenOF.kEvenOF, Pi.zero_apply, add_zero, zero_add, hr1, hr2, hr3, hr4] at h1 h2 hB4 hV4 ⊢
  try simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, Prod.fst_neg, Prod.snd_neg, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, dotS, dot2, AltSixEvenOF.kEvenOF, hr1, hr2, hr3, hr4] at h1
  linarith

theorem base_ae31_3 (k : ℕ) (hk : 1 ≤ k) (w u1 u2 : Word) (hph : phase w = 1)
    (hrel : (parentsAt w).odd.num = (1) ∧ (parentsAt w).odd.den = (2 * (k : ℤ) + 2) ∧ (parentsAt w).even.num = (1) ∧
      (parentsAt w).even.den = (2 * (k : ℤ) + 3))
    (oP oQ oH : PartialOdometer) (βP βQ : ℤ)
    (_hdP : oP.dom = Standard.oddTile u1) (hdQ : oQ.dom = Standard.evenTile u2)
    (_hcP : TileTranslation.StdCornerValues oP 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (hcQ : TileTranslation.StdCornerValues oQ 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (hdH : ∀ x : ℤ × ℤ, x ∈ oH.dom ↔ x + ((-1 : ℤ), (-1 : ℤ)) ∈ paperLadderAltTile (2 * (k : ℤ) + 2))
    (hvH : ∀ x ∈ oH.dom, oH.val x = paperLadderAltValue (2 * (k : ℤ) + 2) (x + ((-1 : ℤ), (-1 : ℤ))))
    (hpc : ∃ C : ℤ, ∀ z, z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAE w u1 u2 3 →
      oH.val (z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z - placedAltEven w oP.val oQ.val 0 3 z = C) :
    ∀ z, z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAE w u1 u2 3 →
      oH.val (z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z + (-h0 (texV2 (parentsAt w).odd) + ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2)) = placedAltEven w oP.val oQ.val (AltSixEvenOF.kEvenOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 3 z := by
  obtain ⟨hD, hR, hAf, hSh⟩ := altEven_of w hph
  obtain ⟨C, hC⟩ := hpc
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hrel
  have hB4 := h0_even (texV2 (parentsAt w).odd) (by simp only [texV2]; omega)
  have hV4 := h0_even (texV2 (parentsAt w).even) (by simp only [texV2]; omega)
  have mQ := corner_mem _ _ _ _ _ _ hcQ
  have vQ := corner_raw _ _ _ _ _ hcQ
  rw [hdQ] at mQ
  set p := (parentsAt w).odd with hpdef
  set q := (parentsAt w).even with hqdef
  set A := texV1Odd p with hA
  set B := texV2 p with hBd
  set U := texV1Even q with hU
  set V := texV2 q with hV
  set S := shiftQ w with hSdef
  have ez : S + B + (((1 : ℤ), (0 : ℤ))) - (B + U) + ((-1 : ℤ), (-1 : ℤ)) = ((-2 * (k : ℤ) - 1), (2 * (k : ℤ) + 2)) := by
    rw [hSh]; ext <;> simp only [hBd, hU, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, hr1, hr2, hr3, hr4] <;> ring
  have m1 : S + B + (((1 : ℤ), (0 : ℤ))) - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) := by
    rw [Finset.mem_coe, hdH, show S + B + (((1 : ℤ), (0 : ℤ))) - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) = S + B + (((1 : ℤ), (0 : ℤ))) - (B + U) from rfl, ez]
    simp only [paperLadderAltTile, paperLadderAltA, paperLadderAltB, paperLadderAltC, paperLadderAltD, Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq]
    omega
  have m2 : S + B + (((1 : ℤ), (0 : ℤ))) ∈ ClosedPathAlt.dAE w u1 u2 3 := by
    have hdj : ClosedPathAlt.dAE w u1 u2 3 = shiftS (tEvenSet u2) (S + B) := by simp [ClosedPathAlt.dAE, pieceSet, hD]
    rw [hdj]
    exact mem_shift _ _ _ (((1 : ℤ), (0 : ℤ))) mQ.2.1 (by abel)
  have h1 := hC _ m1 m2
  have hval : paperLadderAltValue (2 * (k : ℤ) + 2) ((-2 * (k : ℤ) - 1), (2 * (k : ℤ) + 2)) = (-2 * (k : ℤ) ^ 2 - 7 * (k : ℤ) - 4) := by
    have hq : ((2 * (k : ℤ) + 2) : ℤ) * ((2 * (k : ℤ) + 2) + 1) = 2 * (2 * (k : ℤ) ^ 2 + 5 * (k : ℤ) + 3) + 0 := by ring
    simp only [paperLadderAltValue, Set.indicator_apply, Set.mem_union, paperLadderAltA, paperLadderAltB, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_setOf_eq, Prod.mk.injEq]
    split_ifs <;> (try simp only [not_or, not_and] at *) <;> omega
  rw [hvH _ m1, ez, hval] at h1
  rw [eval_lt w _ _ 0 3 _ (S + B) ((p.num, -p.den) + (p.num, -p.den)) (((1 : ℤ), (0 : ℤ))) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) (by abel), vQ.2.1] at h1
  intro z hz1 hz2
  have h2 := hC z hz1 hz2
  rw [← placedAltEven_add]
  simp only [hBd, hU, hV, texV1Even, texV2, Prod.fst_add, Prod.snd_add, dot2, AltSixEvenOF.kEvenOF, Pi.zero_apply, add_zero, hr1, hr2, hr3, hr4] at h1 h2 hB4 hV4 ⊢
  rw [hSh] at h1
  try simp only [hBd, hU, texV1Even, texV2, Prod.fst_add, Prod.snd_add, hr1, hr2, hr3, hr4] at h1
  linarith

theorem base_ae31_4 (k : ℕ) (hk : 1 ≤ k) (w u1 u2 : Word) (hph : phase w = 1)
    (hrel : (parentsAt w).odd.num = (1) ∧ (parentsAt w).odd.den = (2 * (k : ℤ) + 2) ∧ (parentsAt w).even.num = (1) ∧
      (parentsAt w).even.den = (2 * (k : ℤ) + 3))
    (oP oQ oH : PartialOdometer) (βP βQ : ℤ)
    (hdP : oP.dom = Standard.oddTile u1) (_hdQ : oQ.dom = Standard.evenTile u2)
    (hcP : TileTranslation.StdCornerValues oP 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (_hcQ : TileTranslation.StdCornerValues oQ 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (hdH : ∀ x : ℤ × ℤ, x ∈ oH.dom ↔ x + ((-1 : ℤ), (-1 : ℤ)) ∈ paperLadderAltTile (2 * (k : ℤ) + 2))
    (hvH : ∀ x ∈ oH.dom, oH.val x = paperLadderAltValue (2 * (k : ℤ) + 2) (x + ((-1 : ℤ), (-1 : ℤ))))
    (hpc : ∃ C : ℤ, ∀ z, z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAE w u1 u2 4 →
      oH.val (z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z - placedAltEven w oP.val oQ.val 0 4 z = C) :
    ∀ z, z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAE w u1 u2 4 →
      oH.val (z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z + (-h0 (texV2 (parentsAt w).odd) + ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2)) = placedAltEven w oP.val oQ.val (AltSixEvenOF.kEvenOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 4 z := by
  obtain ⟨hD, hR, hAf, hSh⟩ := altEven_of w hph
  obtain ⟨C, hC⟩ := hpc
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hrel
  have hB4 := h0_even (texV2 (parentsAt w).odd) (by simp only [texV2]; omega)
  have hV4 := h0_even (texV2 (parentsAt w).even) (by simp only [texV2]; omega)
  have mP := corner_mem _ _ _ _ _ _ hcP
  have vP := corner_raw _ _ _ _ _ hcP
  rw [hdP] at mP
  set p := (parentsAt w).odd with hpdef
  set q := (parentsAt w).even with hqdef
  set A := texV1Odd p with hA
  set B := texV2 p with hBd
  set U := texV1Even q with hU
  set V := texV2 q with hV
  set S := shiftQ w with hSdef
  have ez : 0 + (A + B + ((1 : ℤ), (-1 : ℤ))) - (B + U) + ((-1 : ℤ), (-1 : ℤ)) = ((2 * (k : ℤ) + 1), (-1)) := by
    ext <;> simp only [hA, hBd, hU, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, hr1, hr2, hr3, hr4] <;> ring
  have m1 : 0 + (A + B + ((1 : ℤ), (-1 : ℤ))) - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) := by
    rw [Finset.mem_coe, hdH, show 0 + (A + B + ((1 : ℤ), (-1 : ℤ))) - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) = 0 + (A + B + ((1 : ℤ), (-1 : ℤ))) - (B + U) from rfl, ez]
    simp only [paperLadderAltTile, paperLadderAltA, paperLadderAltB, paperLadderAltC, paperLadderAltD, Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq, and_true]
    omega
  have m2 : 0 + (A + B + ((1 : ℤ), (-1 : ℤ))) ∈ ClosedPathAlt.dAE w u1 u2 4 := by
    have hdj : ClosedPathAlt.dAE w u1 u2 4 = shiftS (tOddSet u1) (0) := by simp [ClosedPathAlt.dAE, pieceSet, hD, hR]
    rw [hdj]
    exact mem_shift _ _ _ (A + B + ((1 : ℤ), (-1 : ℤ))) mP.2.2.2.2.2.2.1 (by abel)
  have h1 := hC _ m1 m2
  have hval : paperLadderAltValue (2 * (k : ℤ) + 2) ((2 * (k : ℤ) + 1), (-1)) = (0) := by
    have hq : ((-1) : ℤ) * ((-1) + 1) = 2 * (0) + 0 := by ring
    simp only [paperLadderAltValue, Set.indicator_apply, Set.mem_union, paperLadderAltA, paperLadderAltB, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_setOf_eq, Prod.mk.injEq, and_true]
    split_ifs <;> (try simp only [not_or, not_and] at *) <;> omega
  rw [hvH _ m1, ez, hval] at h1
  rw [eval_ge w _ _ 0 4 _ (0) 0 (A + B + ((1 : ℤ), (-1 : ℤ))) (by norm_num) (by rw [hR]; rfl) (by rw [hAf]; rfl) (by abel), vP.2.2.2.2.2.2.1] at h1
  intro z hz1 hz2
  have h2 := hC z hz1 hz2
  rw [← placedAltEven_add]
  simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero, dot2, AltSixEvenOF.kEvenOF, Pi.zero_apply, zero_mul, add_zero, zero_add, hr1, hr2, hr3, hr4] at h1 h2 hB4 hV4 ⊢
  try simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, Prod.fst_neg, Prod.snd_neg, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, dotS, dot2, AltSixEvenOF.kEvenOF, hr1, hr2, hr3, hr4] at h1
  linarith

theorem base_ae31_5 (k : ℕ) (hk : 1 ≤ k) (w u1 u2 : Word) (hph : phase w = 1)
    (hrel : (parentsAt w).odd.num = (1) ∧ (parentsAt w).odd.den = (2 * (k : ℤ) + 2) ∧ (parentsAt w).even.num = (1) ∧
      (parentsAt w).even.den = (2 * (k : ℤ) + 3))
    (oP oQ oH : PartialOdometer) (βP βQ : ℤ)
    (hdP : oP.dom = Standard.oddTile u1) (_hdQ : oQ.dom = Standard.evenTile u2)
    (hcP : TileTranslation.StdCornerValues oP 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (_hcQ : TileTranslation.StdCornerValues oQ 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (hdH : ∀ x : ℤ × ℤ, x ∈ oH.dom ↔ x + ((-1 : ℤ), (-1 : ℤ)) ∈ paperLadderAltTile (2 * (k : ℤ) + 2))
    (hvH : ∀ x ∈ oH.dom, oH.val x = paperLadderAltValue (2 * (k : ℤ) + 2) (x + ((-1 : ℤ), (-1 : ℤ))))
    (hpc : ∃ C : ℤ, ∀ z, z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAE w u1 u2 5 →
      oH.val (z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z - placedAltEven w oP.val oQ.val 0 5 z = C) :
    ∀ z, z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAE w u1 u2 5 →
      oH.val (z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z + (-h0 (texV2 (parentsAt w).odd) + ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2)) = placedAltEven w oP.val oQ.val (AltSixEvenOF.kEvenOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 5 z := by
  obtain ⟨hD, hR, hAf, hSh⟩ := altEven_of w hph
  obtain ⟨C, hC⟩ := hpc
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hrel
  have hB4 := h0_even (texV2 (parentsAt w).odd) (by simp only [texV2]; omega)
  have hV4 := h0_even (texV2 (parentsAt w).even) (by simp only [texV2]; omega)
  have mP := corner_mem _ _ _ _ _ _ hcP
  have vP := corner_raw _ _ _ _ _ hcP
  rw [hdP] at mP
  set p := (parentsAt w).odd with hpdef
  set q := (parentsAt w).even with hqdef
  set A := texV1Odd p with hA
  set B := texV2 p with hBd
  set U := texV1Even q with hU
  set V := texV2 q with hV
  set S := shiftQ w with hSdef
  have ez : B + U + U + V + ((0 : ℤ × ℤ)) - (B + U) + ((-1 : ℤ), (-1 : ℤ)) = ((0), (2 * (k : ℤ) + 4)) := by
    ext <;> simp only [hBd, hU, hV, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, hr1, hr2, hr3, hr4] <;> ring
  have m1 : B + U + U + V + ((0 : ℤ × ℤ)) - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) := by
    rw [Finset.mem_coe, hdH, show B + U + U + V + ((0 : ℤ × ℤ)) - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) = B + U + U + V + ((0 : ℤ × ℤ)) - (B + U) from rfl, ez]
    simp only [paperLadderAltTile, paperLadderAltA, paperLadderAltB, paperLadderAltC, paperLadderAltD, Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq]
    omega
  have m2 : B + U + U + V + ((0 : ℤ × ℤ)) ∈ ClosedPathAlt.dAE w u1 u2 5 := by
    have hdj : ClosedPathAlt.dAE w u1 u2 5 = shiftS (tOddSet u1) (B + U + U + V) := by simp [ClosedPathAlt.dAE, pieceSet, hD, hR]
    rw [hdj]
    exact mem_shift _ _ _ ((0 : ℤ × ℤ)) mP.1 (by abel)
  have h1 := hC _ m1 m2
  have hval : paperLadderAltValue (2 * (k : ℤ) + 2) ((0), (2 * (k : ℤ) + 4)) = (-2 * (k : ℤ) ^ 2 - 9 * (k : ℤ) - 8) := by
    have hq : ((2 * (k : ℤ) + 4) : ℤ) * ((2 * (k : ℤ) + 4) + 1) = 2 * (2 * (k : ℤ) ^ 2 + 9 * (k : ℤ) + 10) + 0 := by ring
    simp only [paperLadderAltValue, Set.indicator_apply, Set.mem_union, paperLadderAltA, paperLadderAltB, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_setOf_eq, Prod.mk.injEq]
    split_ifs <;> (try simp only [false_and, false_or,
      not_or, not_and] at *) <;> omega
  rw [hvH _ m1, ez, hval] at h1
  rw [eval_ge w _ _ 0 5 _ (B + U + U + V) ((p.num, -p.den) + (q.num, -q.den)) ((0 : ℤ × ℤ)) (by norm_num) (by rw [hR]; rfl) (by rw [hAf]; rfl) (by abel), vP.1] at h1
  intro z hz1 hz2
  have h2 := hC z hz1 hz2
  rw [← placedAltEven_add]
  simp only [hBd, hU, hV, texV1Even, texV2, Prod.fst_add, Prod.snd_add, dot2, AltSixEvenOF.kEvenOF, Pi.zero_apply, add_zero, hr1, hr2, hr3, hr4] at h1 h2 hB4 hV4 ⊢
  try simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, Prod.fst_neg, Prod.snd_neg, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, dotS, dot2, AltSixEvenOF.kEvenOF, hr1, hr2, hr3, hr4] at h1
  linarith

theorem base_ae32_0 (k : ℕ) (hk : 1 ≤ k) (w u1 u2 : Word) (hph : phase w ≠ 1)
    (hrel : (parentsAt w).odd.num = (1) ∧ (parentsAt w).odd.den = (2 * (k : ℤ) + 2) ∧ (parentsAt w).even.num = (1) ∧
      (parentsAt w).even.den = (2 * (k : ℤ) + 1))
    (oP oQ oH : PartialOdometer) (βP βQ : ℤ)
    (_hdP : oP.dom = Standard.oddTile u1) (hdQ : oQ.dom = Standard.evenTile u2)
    (_hcP : TileTranslation.StdCornerValues oP 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (hcQ : TileTranslation.StdCornerValues oQ 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (hdH : ∀ x : ℤ × ℤ, x ∈ oH.dom ↔ x + ((-1 : ℤ), (-1 : ℤ)) ∈ paperLadderAltTile (2 * (k : ℤ) + 2))
    (hvH : ∀ x ∈ oH.dom, oH.val x = paperLadderAltValue (2 * (k : ℤ) + 2) (x + ((-1 : ℤ), (-1 : ℤ))))
    (hpc : ∃ C : ℤ, ∀ z, z - (texV2 (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAE w u1 u2 0 →
      oH.val (z - (texV2 (parentsAt w).even)) + dot2 ((parentsAt w).even.num, -(parentsAt w).even.den) z - placedAltEven w oP.val oQ.val 0 0 z = C) :
    ∀ z, z - (texV2 (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAE w u1 u2 0 →
      oH.val (z - (texV2 (parentsAt w).even)) + dot2 ((parentsAt w).even.num, -(parentsAt w).even.den) z + (-h0 (texV2 (parentsAt w).even) + ((parentsAt w).even.den ^ 2 + 2 * (parentsAt w).even.den * (parentsAt w).even.num - (parentsAt w).even.num ^ 2)) = placedAltEven w oP.val oQ.val (kEvenEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 0 z := by
  obtain ⟨hD, hR, hAf, hSh⟩ := altEven_ef w hph
  obtain ⟨C, hC⟩ := hpc
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hrel
  have hB4 := h0_even (texV2 (parentsAt w).odd) (by simp only [texV2]; omega)
  have hV4 := h0_even (texV2 (parentsAt w).even) (by simp only [texV2]; omega)
  have mQ := corner_mem _ _ _ _ _ _ hcQ
  have vQ := corner_raw _ _ _ _ _ hcQ
  rw [hdQ] at mQ
  set p := (parentsAt w).odd with hpdef
  set q := (parentsAt w).even with hqdef
  set A := texV1Odd p with hA
  set B := texV2 p with hBd
  set U := texV1Even q with hU
  set V := texV2 q with hV
  set S := shiftQ w with hSdef
  have ez : 0 + (V + ((1 : ℤ), (0 : ℤ))) - V + ((-1 : ℤ), (-1 : ℤ)) = ((0), (-1)) := by
    ext <;> simp only [hV, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, hr3, hr4] <;> ring
  have m1 : 0 + (V + ((1 : ℤ), (0 : ℤ))) - (texV2 (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) := by
    rw [Finset.mem_coe, hdH, show 0 + (V + ((1 : ℤ), (0 : ℤ))) - (texV2 (parentsAt w).even) = 0 + (V + ((1 : ℤ), (0 : ℤ))) - V from rfl, ez]
    simp only [paperLadderAltTile, paperLadderAltA, paperLadderAltB, paperLadderAltC, paperLadderAltD, Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq, and_true]
    omega
  have m2 : 0 + (V + ((1 : ℤ), (0 : ℤ))) ∈ ClosedPathAlt.dAE w u1 u2 0 := by
    have hdj : ClosedPathAlt.dAE w u1 u2 0 = shiftS (tEvenSet u2) (0) := by simp [ClosedPathAlt.dAE, pieceSet, hD]
    rw [hdj]
    exact mem_shift _ _ _ (V + ((1 : ℤ), (0 : ℤ))) mQ.2.2.2.2.1 (by abel)
  have h1 := hC _ m1 m2
  have hval : paperLadderAltValue (2 * (k : ℤ) + 2) ((0), (-1)) = (0) := by
    have hq : ((-1) : ℤ) * ((-1) + 1) = 2 * (0) + 0 := by ring
    simp only [paperLadderAltValue, Set.indicator_apply, Set.mem_union, paperLadderAltA, paperLadderAltB, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_setOf_eq, Prod.mk.injEq, and_true]
    split_ifs <;> (try simp only [false_or,
      not_or, not_and] at *) <;> omega
  rw [hvH _ m1, ez, hval] at h1
  rw [eval_lt w _ _ 0 0 _ (0) 0 (V + ((1 : ℤ), (0 : ℤ))) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) (by abel), vQ.2.2.2.2.1] at h1
  intro z hz1 hz2
  have h2 := hC z hz1 hz2
  rw [← placedAltEven_add]
  simp only [hBd, hV, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero, dot2, kEvenEF, Pi.zero_apply, zero_mul, add_zero, zero_add, hr1, hr2, hr3, hr4] at h1 h2 hB4 hV4 ⊢
  try simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, Prod.fst_neg, Prod.snd_neg, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, dotS, dot2, kEvenEF, hr1, hr2, hr3, hr4] at h1
  linarith

theorem base_ae32_1 (k : ℕ) (hk : 1 ≤ k) (w u1 u2 : Word) (hph : phase w ≠ 1)
    (hrel : (parentsAt w).odd.num = (1) ∧ (parentsAt w).odd.den = (2 * (k : ℤ) + 2) ∧ (parentsAt w).even.num = (1) ∧
      (parentsAt w).even.den = (2 * (k : ℤ) + 1))
    (oP oQ oH : PartialOdometer) (βP βQ : ℤ)
    (_hdP : oP.dom = Standard.oddTile u1) (hdQ : oQ.dom = Standard.evenTile u2)
    (_hcP : TileTranslation.StdCornerValues oP 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (hcQ : TileTranslation.StdCornerValues oQ 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (hdH : ∀ x : ℤ × ℤ, x ∈ oH.dom ↔ x + ((-1 : ℤ), (-1 : ℤ)) ∈ paperLadderAltTile (2 * (k : ℤ) + 2))
    (hvH : ∀ x ∈ oH.dom, oH.val x = paperLadderAltValue (2 * (k : ℤ) + 2) (x + ((-1 : ℤ), (-1 : ℤ))))
    (hpc : ∃ C : ℤ, ∀ z, z - (texV2 (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAE w u1 u2 1 →
      oH.val (z - (texV2 (parentsAt w).even)) + dot2 ((parentsAt w).even.num, -(parentsAt w).even.den) z - placedAltEven w oP.val oQ.val 0 1 z = C) :
    ∀ z, z - (texV2 (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAE w u1 u2 1 →
      oH.val (z - (texV2 (parentsAt w).even)) + dot2 ((parentsAt w).even.num, -(parentsAt w).even.den) z + (-h0 (texV2 (parentsAt w).even) + ((parentsAt w).even.den ^ 2 + 2 * (parentsAt w).even.den * (parentsAt w).even.num - (parentsAt w).even.num ^ 2)) = placedAltEven w oP.val oQ.val (kEvenEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 1 z := by
  obtain ⟨hD, hR, hAf, hSh⟩ := altEven_ef w hph
  obtain ⟨C, hC⟩ := hpc
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hrel
  have hB4 := h0_even (texV2 (parentsAt w).odd) (by simp only [texV2]; omega)
  have hV4 := h0_even (texV2 (parentsAt w).even) (by simp only [texV2]; omega)
  have mQ := corner_mem _ _ _ _ _ _ hcQ
  have vQ := corner_raw _ _ _ _ _ hcQ
  rw [hdQ] at mQ
  set p := (parentsAt w).odd with hpdef
  set q := (parentsAt w).even with hqdef
  set A := texV1Odd p with hA
  set B := texV2 p with hBd
  set U := texV1Even q with hU
  set V := texV2 q with hV
  set S := shiftQ w with hSdef
  have ez : S + 0 + (U + V + ((1 : ℤ), (-1 : ℤ))) - V + ((-1 : ℤ), (-1 : ℤ)) = ((-2 * (k : ℤ) - 1), (2 * (k : ℤ) + 1)) := by
    rw [hSh]; ext <;> simp only [hBd, hU, hV, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, Prod.fst_neg, Prod.snd_neg, hr1, hr2, hr3, hr4] <;> ring
  have m1 : S + 0 + (U + V + ((1 : ℤ), (-1 : ℤ))) - (texV2 (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) := by
    rw [Finset.mem_coe, hdH, show S + 0 + (U + V + ((1 : ℤ), (-1 : ℤ))) - (texV2 (parentsAt w).even) = S + 0 + (U + V + ((1 : ℤ), (-1 : ℤ))) - V from rfl, ez]
    simp only [paperLadderAltTile, paperLadderAltA, paperLadderAltB, paperLadderAltC, paperLadderAltD, Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq]
    omega
  have m2 : S + 0 + (U + V + ((1 : ℤ), (-1 : ℤ))) ∈ ClosedPathAlt.dAE w u1 u2 1 := by
    have hdj : ClosedPathAlt.dAE w u1 u2 1 = shiftS (tEvenSet u2) (S + 0) := by simp [ClosedPathAlt.dAE, pieceSet, hD]
    rw [hdj]
    exact mem_shift _ _ _ (U + V + ((1 : ℤ), (-1 : ℤ))) mQ.2.2.2.2.2.2.1 (by abel)
  have h1 := hC _ m1 m2
  have hval : paperLadderAltValue (2 * (k : ℤ) + 2) ((-2 * (k : ℤ) - 1), (2 * (k : ℤ) + 1)) = (-2 * (k : ℤ) ^ 2 - 5 * (k : ℤ) - 2) := by
    have hq : ((2 * (k : ℤ) + 1) : ℤ) * ((2 * (k : ℤ) + 1) + 1) = 2 * (2 * (k : ℤ) ^ 2 + 3 * (k : ℤ) + 1) + 0 := by ring
    simp only [paperLadderAltValue, Set.indicator_apply, Set.mem_union, paperLadderAltA, paperLadderAltB, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_setOf_eq, Prod.mk.injEq]
    split_ifs <;> (try simp only [not_or, not_and] at *) <;> omega
  rw [hvH _ m1, ez, hval] at h1
  rw [eval_lt w _ _ 0 1 _ (S + 0) (p.num, -p.den) (U + V + ((1 : ℤ), (-1 : ℤ))) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) (by abel), vQ.2.2.2.2.2.2.1] at h1
  intro z hz1 hz2
  have h2 := hC z hz1 hz2
  rw [← placedAltEven_add]
  simp only [hBd, hU, hV, texV1Even, texV2, Prod.fst_add, Prod.snd_add, dot2, kEvenEF, Pi.zero_apply, add_zero, hr1, hr2, hr3, hr4] at h1 h2 hB4 hV4 ⊢
  rw [hSh] at h1
  try simp only [hBd, hU, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg, hr1, hr2, hr3, hr4] at h1
  linarith

theorem base_ae32_2 (k : ℕ) (hk : 1 ≤ k) (w u1 u2 : Word) (hph : phase w ≠ 1)
    (hrel : (parentsAt w).odd.num = (1) ∧ (parentsAt w).odd.den = (2 * (k : ℤ) + 2) ∧ (parentsAt w).even.num = (1) ∧
      (parentsAt w).even.den = (2 * (k : ℤ) + 1))
    (oP oQ oH : PartialOdometer) (βP βQ : ℤ)
    (_hdP : oP.dom = Standard.oddTile u1) (hdQ : oQ.dom = Standard.evenTile u2)
    (_hcP : TileTranslation.StdCornerValues oP 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (hcQ : TileTranslation.StdCornerValues oQ 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (hdH : ∀ x : ℤ × ℤ, x ∈ oH.dom ↔ x + ((-1 : ℤ), (-1 : ℤ)) ∈ paperLadderAltTile (2 * (k : ℤ) + 2))
    (hvH : ∀ x ∈ oH.dom, oH.val x = paperLadderAltValue (2 * (k : ℤ) + 2) (x + ((-1 : ℤ), (-1 : ℤ))))
    (hpc : ∃ C : ℤ, ∀ z, z - (texV2 (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAE w u1 u2 2 →
      oH.val (z - (texV2 (parentsAt w).even)) + dot2 ((parentsAt w).even.num, -(parentsAt w).even.den) z - placedAltEven w oP.val oQ.val 0 2 z = C) :
    ∀ z, z - (texV2 (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAE w u1 u2 2 →
      oH.val (z - (texV2 (parentsAt w).even)) + dot2 ((parentsAt w).even.num, -(parentsAt w).even.den) z + (-h0 (texV2 (parentsAt w).even) + ((parentsAt w).even.den ^ 2 + 2 * (parentsAt w).even.den * (parentsAt w).even.num - (parentsAt w).even.num ^ 2)) = placedAltEven w oP.val oQ.val (kEvenEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 2 z := by
  obtain ⟨hD, hR, hAf, hSh⟩ := altEven_ef w hph
  obtain ⟨C, hC⟩ := hpc
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hrel
  have hB4 := h0_even (texV2 (parentsAt w).odd) (by simp only [texV2]; omega)
  have hV4 := h0_even (texV2 (parentsAt w).even) (by simp only [texV2]; omega)
  have mQ := corner_mem _ _ _ _ _ _ hcQ
  have vQ := corner_raw _ _ _ _ _ hcQ
  rw [hdQ] at mQ
  set p := (parentsAt w).odd with hpdef
  set q := (parentsAt w).even with hqdef
  set A := texV1Odd p with hA
  set B := texV2 p with hBd
  set U := texV1Even q with hU
  set V := texV2 q with hV
  set S := shiftQ w with hSdef
  have ez : A + B + ((0 : ℤ × ℤ)) - V + ((-1 : ℤ), (-1 : ℤ)) = ((4 * (k : ℤ) + 2), (2)) := by
    ext <;> simp only [hA, hBd, hV, texV1Odd, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, hr1, hr2, hr3, hr4] <;> ring
  have m1 : A + B + ((0 : ℤ × ℤ)) - (texV2 (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) := by
    rw [Finset.mem_coe, hdH, show A + B + ((0 : ℤ × ℤ)) - (texV2 (parentsAt w).even) = A + B + ((0 : ℤ × ℤ)) - V from rfl, ez]
    simp only [paperLadderAltTile, paperLadderAltA, paperLadderAltB, paperLadderAltC, paperLadderAltD, Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq]
    omega
  have m2 : A + B + ((0 : ℤ × ℤ)) ∈ ClosedPathAlt.dAE w u1 u2 2 := by
    have hdj : ClosedPathAlt.dAE w u1 u2 2 = shiftS (tEvenSet u2) (A + B) := by simp [ClosedPathAlt.dAE, pieceSet, hD]
    rw [hdj]
    exact mem_shift _ _ _ ((0 : ℤ × ℤ)) mQ.1 (by abel)
  have h1 := hC _ m1 m2
  have hval : paperLadderAltValue (2 * (k : ℤ) + 2) ((4 * (k : ℤ) + 2), (2)) = (-2) := by
    have hq : ((2) : ℤ) * ((2) + 1) = 2 * (3) + 0 := by ring
    simp only [paperLadderAltValue, Set.indicator_apply, Set.mem_union, paperLadderAltA, paperLadderAltB, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_setOf_eq, Prod.mk.injEq]
    split_ifs <;> (try simp only [and_false, false_or,
      not_or, not_and] at *) <;> omega
  rw [hvH _ m1, ez, hval] at h1
  rw [eval_lt w _ _ 0 2 _ (A + B) (p.num, -p.den) ((0 : ℤ × ℤ)) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) (by abel), vQ.1] at h1
  intro z hz1 hz2
  have h2 := hC z hz1 hz2
  rw [← placedAltEven_add]
  simp only [hA, hBd, hV, texV1Odd, texV2, Prod.fst_add, Prod.snd_add, dot2, kEvenEF, Pi.zero_apply, add_zero, hr1, hr2, hr3, hr4] at h1 h2 hB4 hV4 ⊢
  try simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, Prod.fst_neg, Prod.snd_neg, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, dotS, dot2, kEvenEF, hr1, hr2, hr3, hr4] at h1
  linarith

theorem base_ae32_3 (k : ℕ) (hk : 1 ≤ k) (w u1 u2 : Word) (hph : phase w ≠ 1)
    (hrel : (parentsAt w).odd.num = (1) ∧ (parentsAt w).odd.den = (2 * (k : ℤ) + 2) ∧ (parentsAt w).even.num = (1) ∧
      (parentsAt w).even.den = (2 * (k : ℤ) + 1))
    (oP oQ oH : PartialOdometer) (βP βQ : ℤ)
    (_hdP : oP.dom = Standard.oddTile u1) (hdQ : oQ.dom = Standard.evenTile u2)
    (_hcP : TileTranslation.StdCornerValues oP 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (hcQ : TileTranslation.StdCornerValues oQ 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (hdH : ∀ x : ℤ × ℤ, x ∈ oH.dom ↔ x + ((-1 : ℤ), (-1 : ℤ)) ∈ paperLadderAltTile (2 * (k : ℤ) + 2))
    (hvH : ∀ x ∈ oH.dom, oH.val x = paperLadderAltValue (2 * (k : ℤ) + 2) (x + ((-1 : ℤ), (-1 : ℤ))))
    (hpc : ∃ C : ℤ, ∀ z, z - (texV2 (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAE w u1 u2 3 →
      oH.val (z - (texV2 (parentsAt w).even)) + dot2 ((parentsAt w).even.num, -(parentsAt w).even.den) z - placedAltEven w oP.val oQ.val 0 3 z = C) :
    ∀ z, z - (texV2 (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAE w u1 u2 3 →
      oH.val (z - (texV2 (parentsAt w).even)) + dot2 ((parentsAt w).even.num, -(parentsAt w).even.den) z + (-h0 (texV2 (parentsAt w).even) + ((parentsAt w).even.den ^ 2 + 2 * (parentsAt w).even.den * (parentsAt w).even.num - (parentsAt w).even.num ^ 2)) = placedAltEven w oP.val oQ.val (kEvenEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 3 z := by
  obtain ⟨hD, hR, hAf, hSh⟩ := altEven_ef w hph
  obtain ⟨C, hC⟩ := hpc
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hrel
  have hB4 := h0_even (texV2 (parentsAt w).odd) (by simp only [texV2]; omega)
  have hV4 := h0_even (texV2 (parentsAt w).even) (by simp only [texV2]; omega)
  have mQ := corner_mem _ _ _ _ _ _ hcQ
  have vQ := corner_raw _ _ _ _ _ hcQ
  rw [hdQ] at mQ
  set p := (parentsAt w).odd with hpdef
  set q := (parentsAt w).even with hqdef
  set A := texV1Odd p with hA
  set B := texV2 p with hBd
  set U := texV1Even q with hU
  set V := texV2 q with hV
  set S := shiftQ w with hSdef
  have ez : S + (A + B) + ((0 : ℤ × ℤ)) - V + ((-1 : ℤ), (-1 : ℤ)) = ((0), (2 * (k : ℤ) + 4)) := by
    rw [hSh]; ext <;> simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, Prod.fst_neg, Prod.snd_neg, hr1, hr2, hr3, hr4] <;> ring
  have m1 : S + (A + B) + ((0 : ℤ × ℤ)) - (texV2 (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) := by
    rw [Finset.mem_coe, hdH, show S + (A + B) + ((0 : ℤ × ℤ)) - (texV2 (parentsAt w).even) = S + (A + B) + ((0 : ℤ × ℤ)) - V from rfl, ez]
    simp only [paperLadderAltTile, paperLadderAltA, paperLadderAltB, paperLadderAltC, paperLadderAltD, Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq]
    omega
  have m2 : S + (A + B) + ((0 : ℤ × ℤ)) ∈ ClosedPathAlt.dAE w u1 u2 3 := by
    have hdj : ClosedPathAlt.dAE w u1 u2 3 = shiftS (tEvenSet u2) (S + (A + B)) := by simp [ClosedPathAlt.dAE, pieceSet, hD]
    rw [hdj]
    exact mem_shift _ _ _ ((0 : ℤ × ℤ)) mQ.1 (by abel)
  have h1 := hC _ m1 m2
  have hval : paperLadderAltValue (2 * (k : ℤ) + 2) ((0), (2 * (k : ℤ) + 4)) = (-2 * (k : ℤ) ^ 2 - 9 * (k : ℤ) - 8) := by
    have hq : ((2 * (k : ℤ) + 4) : ℤ) * ((2 * (k : ℤ) + 4) + 1) = 2 * (2 * (k : ℤ) ^ 2 + 9 * (k : ℤ) + 10) + 0 := by ring
    simp only [paperLadderAltValue, Set.indicator_apply, Set.mem_union, paperLadderAltA, paperLadderAltB, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_setOf_eq, Prod.mk.injEq]
    split_ifs <;> (try simp only [false_and, false_or,
      not_or, not_and] at *) <;> omega
  rw [hvH _ m1, ez, hval] at h1
  rw [eval_lt w _ _ 0 3 _ (S + (A + B)) ((p.num, -p.den) + (p.num, -p.den)) ((0 : ℤ × ℤ)) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) (by abel), vQ.1] at h1
  intro z hz1 hz2
  have h2 := hC z hz1 hz2
  rw [← placedAltEven_add]
  simp only [hA, hBd, hV, texV1Odd, texV2, Prod.fst_add, Prod.snd_add, dot2, kEvenEF, Pi.zero_apply, add_zero, hr1, hr2, hr3, hr4] at h1 h2 hB4 hV4 ⊢
  rw [hSh] at h1
  try simp only [hBd, hU, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg, hr1, hr2, hr3, hr4] at h1
  linarith

theorem base_ae32_4 (k : ℕ) (hk : 1 ≤ k) (w u1 u2 : Word) (hph : phase w ≠ 1)
    (hrel : (parentsAt w).odd.num = (1) ∧ (parentsAt w).odd.den = (2 * (k : ℤ) + 2) ∧ (parentsAt w).even.num = (1) ∧
      (parentsAt w).even.den = (2 * (k : ℤ) + 1))
    (oP oQ oH : PartialOdometer) (βP βQ : ℤ)
    (hdP : oP.dom = Standard.oddTile u1) (_hdQ : oQ.dom = Standard.evenTile u2)
    (hcP : TileTranslation.StdCornerValues oP 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (_hcQ : TileTranslation.StdCornerValues oQ 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (hdH : ∀ x : ℤ × ℤ, x ∈ oH.dom ↔ x + ((-1 : ℤ), (-1 : ℤ)) ∈ paperLadderAltTile (2 * (k : ℤ) + 2))
    (hvH : ∀ x ∈ oH.dom, oH.val x = paperLadderAltValue (2 * (k : ℤ) + 2) (x + ((-1 : ℤ), (-1 : ℤ))))
    (hpc : ∃ C : ℤ, ∀ z, z - (texV2 (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAE w u1 u2 4 →
      oH.val (z - (texV2 (parentsAt w).even)) + dot2 ((parentsAt w).even.num, -(parentsAt w).even.den) z - placedAltEven w oP.val oQ.val 0 4 z = C) :
    ∀ z, z - (texV2 (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAE w u1 u2 4 →
      oH.val (z - (texV2 (parentsAt w).even)) + dot2 ((parentsAt w).even.num, -(parentsAt w).even.den) z + (-h0 (texV2 (parentsAt w).even) + ((parentsAt w).even.den ^ 2 + 2 * (parentsAt w).even.den * (parentsAt w).even.num - (parentsAt w).even.num ^ 2)) = placedAltEven w oP.val oQ.val (kEvenEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 4 z := by
  obtain ⟨hD, hR, hAf, hSh⟩ := altEven_ef w hph
  obtain ⟨C, hC⟩ := hpc
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hrel
  have hB4 := h0_even (texV2 (parentsAt w).odd) (by simp only [texV2]; omega)
  have hV4 := h0_even (texV2 (parentsAt w).even) (by simp only [texV2]; omega)
  have mP := corner_mem _ _ _ _ _ _ hcP
  have vP := corner_raw _ _ _ _ _ hcP
  rw [hdP] at mP
  set p := (parentsAt w).odd with hpdef
  set q := (parentsAt w).even with hqdef
  set A := texV1Odd p with hA
  set B := texV2 p with hBd
  set U := texV1Even q with hU
  set V := texV2 q with hV
  set S := shiftQ w with hSdef
  have ez : U + (B + ((1 : ℤ), (0 : ℤ))) - V + ((-1 : ℤ), (-1 : ℤ)) = ((2 * (k : ℤ)), (1)) := by
    ext <;> simp only [hBd, hU, hV, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, hr1, hr2, hr3, hr4] <;> ring
  have m1 : U + (B + ((1 : ℤ), (0 : ℤ))) - (texV2 (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) := by
    rw [Finset.mem_coe, hdH, show U + (B + ((1 : ℤ), (0 : ℤ))) - (texV2 (parentsAt w).even) = U + (B + ((1 : ℤ), (0 : ℤ))) - V from rfl, ez]
    simp only [paperLadderAltTile, paperLadderAltA, paperLadderAltB, paperLadderAltC, paperLadderAltD, Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq]
    omega
  have m2 : U + (B + ((1 : ℤ), (0 : ℤ))) ∈ ClosedPathAlt.dAE w u1 u2 4 := by
    have hdj : ClosedPathAlt.dAE w u1 u2 4 = shiftS (tOddSet u1) (U) := by simp [ClosedPathAlt.dAE, pieceSet, hD, hR]
    rw [hdj]
    exact mem_shift _ _ _ (B + ((1 : ℤ), (0 : ℤ))) mP.2.2.2.2.1 (by abel)
  have h1 := hC _ m1 m2
  have hval : paperLadderAltValue (2 * (k : ℤ) + 2) ((2 * (k : ℤ)), (1)) = (-1) := by
    have hq : ((1) : ℤ) * ((1) + 1) = 2 * (1) + 0 := by ring
    simp only [paperLadderAltValue, Set.indicator_apply, Set.mem_union, paperLadderAltA, paperLadderAltB, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_setOf_eq, Prod.mk.injEq]
    split_ifs <;> (try simp only [and_false, false_or,
      not_or, not_and] at *) <;> omega
  rw [hvH _ m1, ez, hval] at h1
  rw [eval_ge w _ _ 0 4 _ (U) 0 (B + ((1 : ℤ), (0 : ℤ))) (by norm_num) (by rw [hR]; rfl) (by rw [hAf]; rfl) (by abel), vP.2.2.2.2.1] at h1
  intro z hz1 hz2
  have h2 := hC z hz1 hz2
  rw [← placedAltEven_add]
  simp only [hBd, hU, hV, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero, dot2, kEvenEF, Pi.zero_apply, zero_mul, add_zero, hr1, hr2, hr3, hr4] at h1 h2 hB4 hV4 ⊢
  try simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, Prod.fst_neg, Prod.snd_neg, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, dotS, dot2, kEvenEF, hr1, hr2, hr3, hr4] at h1
  linarith

theorem base_ae32_5 (k : ℕ) (hk : 1 ≤ k) (w u1 u2 : Word) (hph : phase w ≠ 1)
    (hrel : (parentsAt w).odd.num = (1) ∧ (parentsAt w).odd.den = (2 * (k : ℤ) + 2) ∧ (parentsAt w).even.num = (1) ∧
      (parentsAt w).even.den = (2 * (k : ℤ) + 1))
    (oP oQ oH : PartialOdometer) (βP βQ : ℤ)
    (hdP : oP.dom = Standard.oddTile u1) (_hdQ : oQ.dom = Standard.evenTile u2)
    (hcP : TileTranslation.StdCornerValues oP 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (_hcQ : TileTranslation.StdCornerValues oQ 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (hdH : ∀ x : ℤ × ℤ, x ∈ oH.dom ↔ x + ((-1 : ℤ), (-1 : ℤ)) ∈ paperLadderAltTile (2 * (k : ℤ) + 2))
    (hvH : ∀ x ∈ oH.dom, oH.val x = paperLadderAltValue (2 * (k : ℤ) + 2) (x + ((-1 : ℤ), (-1 : ℤ))))
    (hpc : ∃ C : ℤ, ∀ z, z - (texV2 (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAE w u1 u2 5 →
      oH.val (z - (texV2 (parentsAt w).even)) + dot2 ((parentsAt w).even.num, -(parentsAt w).even.den) z - placedAltEven w oP.val oQ.val 0 5 z = C) :
    ∀ z, z - (texV2 (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAE w u1 u2 5 →
      oH.val (z - (texV2 (parentsAt w).even)) + dot2 ((parentsAt w).even.num, -(parentsAt w).even.den) z + (-h0 (texV2 (parentsAt w).even) + ((parentsAt w).even.den ^ 2 + 2 * (parentsAt w).even.den * (parentsAt w).even.num - (parentsAt w).even.num ^ 2)) = placedAltEven w oP.val oQ.val (kEvenEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 5 z := by
  obtain ⟨hD, hR, hAf, hSh⟩ := altEven_ef w hph
  obtain ⟨C, hC⟩ := hpc
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hrel
  have hB4 := h0_even (texV2 (parentsAt w).odd) (by simp only [texV2]; omega)
  have hV4 := h0_even (texV2 (parentsAt w).even) (by simp only [texV2]; omega)
  have mP := corner_mem _ _ _ _ _ _ hcP
  have vP := corner_raw _ _ _ _ _ hcP
  rw [hdP] at mP
  set p := (parentsAt w).odd with hpdef
  set q := (parentsAt w).even with hqdef
  set A := texV1Odd p with hA
  set B := texV2 p with hBd
  set U := texV1Even q with hU
  set V := texV2 q with hV
  set S := shiftQ w with hSdef
  have ez : B - U + V + (A - ((0 : ℤ), (1 : ℤ))) - V + ((-1 : ℤ), (-1 : ℤ)) = ((1), (2 * (k : ℤ) + 2)) := by
    ext <;> simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, hr1, hr2, hr3, hr4] <;> ring
  have m1 : B - U + V + (A - ((0 : ℤ), (1 : ℤ))) - (texV2 (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) := by
    rw [Finset.mem_coe, hdH, show B - U + V + (A - ((0 : ℤ), (1 : ℤ))) - (texV2 (parentsAt w).even) = B - U + V + (A - ((0 : ℤ), (1 : ℤ))) - V from rfl, ez]
    simp only [paperLadderAltTile, paperLadderAltA, paperLadderAltB, paperLadderAltC, paperLadderAltD, Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq]
    omega
  have m2 : B - U + V + (A - ((0 : ℤ), (1 : ℤ))) ∈ ClosedPathAlt.dAE w u1 u2 5 := by
    have hdj : ClosedPathAlt.dAE w u1 u2 5 = shiftS (tOddSet u1) (B - U + V) := by simp [ClosedPathAlt.dAE, pieceSet, hD, hR]
    rw [hdj]
    exact mem_shift _ _ _ (A - ((0 : ℤ), (1 : ℤ))) mP.2.2.1 (by abel)
  have h1 := hC _ m1 m2
  have hval : paperLadderAltValue (2 * (k : ℤ) + 2) ((1), (2 * (k : ℤ) + 2)) = (-2 * (k : ℤ) ^ 2 - 5 * (k : ℤ) - 2) := by
    have hq : ((2 * (k : ℤ) + 2) : ℤ) * ((2 * (k : ℤ) + 2) + 1) = 2 * (2 * (k : ℤ) ^ 2 + 5 * (k : ℤ) + 3) + 0 := by ring
    simp only [paperLadderAltValue, Set.indicator_apply, Set.mem_union, paperLadderAltA, paperLadderAltB, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_setOf_eq, Prod.mk.injEq]
    split_ifs <;> (try simp only [false_and, false_or,
      not_or, not_and] at *) <;> omega
  rw [hvH _ m1, ez, hval] at h1
  rw [eval_ge w _ _ 0 5 _ (B - U + V) ((p.num, -p.den) + (q.num, -q.den)) (A - ((0 : ℤ), (1 : ℤ))) (by norm_num) (by rw [hR]; rfl) (by rw [hAf]; rfl) (by abel), vP.2.2.1] at h1
  intro z hz1 hz2
  have h2 := hC z hz1 hz2
  rw [← placedAltEven_add]
  simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, dot2, kEvenEF, Pi.zero_apply, add_zero, hr1, hr2, hr3, hr4] at h1 h2 hB4 hV4 ⊢
  try simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, Prod.fst_neg, Prod.snd_neg, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, dotS, dot2, kEvenEF, hr1, hr2, hr3, hr4] at h1
  linarith

theorem base_ae21_0 (k : ℕ) (hk : 0 ≤ k) (w u1 u2 : Word) (hph : phase w = 1)
    (hrel : (parentsAt w).odd.num = ((k : ℤ) + 1) ∧ (parentsAt w).odd.den = ((k : ℤ) + 2) ∧ (parentsAt w).even.num = (2 * (k : ℤ) + 1) ∧
      (parentsAt w).even.den = (2 * (k : ℤ) + 3))
    (oP oQ oH : PartialOdometer) (βP βQ : ℤ)
    (_hdP : oP.dom = Standard.oddTile u1) (hdQ : oQ.dom = Standard.evenTile u2)
    (_hcP : TileTranslation.StdCornerValues oP 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (hcQ : TileTranslation.StdCornerValues oQ 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (hdH : ∀ x : ℤ × ℤ, x ∈ oH.dom ↔ x + ((0 : ℤ), (1 : ℤ)) ∈ paperNearStairAltTile (2 * (k : ℤ) + 3))
    (hvH : ∀ x ∈ oH.dom, oH.val x = paperNearStairAltValue (2 * (k : ℤ) + 3) (x + ((0 : ℤ), (1 : ℤ))))
    (hpc : ∃ C : ℤ, ∀ z, z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAE w u1 u2 0 →
      oH.val (z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z - placedAltEven w oP.val oQ.val 0 0 z = C) :
    ∀ z, z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAE w u1 u2 0 →
      oH.val (z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z + (-h0 (texV2 (parentsAt w).odd) + ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2)) = placedAltEven w oP.val oQ.val (AltSixEvenOF.kEvenOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 0 z := by
  obtain ⟨hD, hR, hAf, hSh⟩ := altEven_of w hph
  obtain ⟨C, hC⟩ := hpc
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hrel
  have hB4 := h0_even (texV2 (parentsAt w).odd) (by simp only [texV2]; omega)
  have hV4 := h0_even (texV2 (parentsAt w).even) (by simp only [texV2]; omega)
  have mQ := corner_mem _ _ _ _ _ _ hcQ
  have vQ := corner_raw _ _ _ _ _ hcQ
  rw [hdQ] at mQ
  set p := (parentsAt w).odd with hpdef
  set q := (parentsAt w).even with hqdef
  set A := texV1Odd p with hA
  set B := texV2 p with hBd
  set U := texV1Even q with hU
  set V := texV2 q with hV
  set S := shiftQ w with hSdef
  have ez : A + (V + ((1 : ℤ), (0 : ℤ))) - (B + U) + ((0 : ℤ), (1 : ℤ)) = ((1), (2 * (k : ℤ) + 3)) := by
    ext <;> simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, hr1, hr2, hr3, hr4] <;> ring
  have m1 : A + (V + ((1 : ℤ), (0 : ℤ))) - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) := by
    rw [Finset.mem_coe, hdH, show A + (V + ((1 : ℤ), (0 : ℤ))) - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) = A + (V + ((1 : ℤ), (0 : ℤ))) - (B + U) from rfl, ez]
    simp only [paperNearStairAltTile, paperNearStairAltA, paperNearStairAltB, paperNearStairAltC, paperNearStairAltD, Set.mem_union, Set.mem_setOf_eq, true_and]
    omega
  have m2 : A + (V + ((1 : ℤ), (0 : ℤ))) ∈ ClosedPathAlt.dAE w u1 u2 0 := by
    have hdj : ClosedPathAlt.dAE w u1 u2 0 = shiftS (tEvenSet u2) (A) := by simp [ClosedPathAlt.dAE, pieceSet, hD]
    rw [hdj]
    exact mem_shift _ _ _ (V + ((1 : ℤ), (0 : ℤ))) mQ.2.2.2.2.1 (by abel)
  have h1 := hC _ m1 m2
  have hval : paperNearStairAltValue (2 * (k : ℤ) + 3) ((1), (2 * (k : ℤ) + 3)) = (-(k : ℤ) ^ 2 - 2 * (k : ℤ) - 1) := by
    have hq : (((2 * (k : ℤ) + 3) : ℤ) - (1)) ^ 2 = 4 * ((k : ℤ) ^ 2 + 2 * (k : ℤ) + 1) + 0 := by ring
    simp only [paperNearStairAltValue, Set.indicator_apply, Set.mem_union, paperNearStairAltA, paperNearStairAltB,
      Set.mem_setOf_eq, true_and]
    split_ifs <;> (try simp only [not_or, not_and] at *) <;> omega
  rw [hvH _ m1, ez, hval] at h1
  rw [eval_lt w _ _ 0 0 _ (A) 0 (V + ((1 : ℤ), (0 : ℤ))) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) (by abel), vQ.2.2.2.2.1] at h1
  intro z hz1 hz2
  have h2 := hC z hz1 hz2
  rw [← placedAltEven_add]
  simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero, dot2, AltSixEvenOF.kEvenOF, Pi.zero_apply, zero_mul, add_zero, hr1, hr2, hr3, hr4] at h1 h2 hB4 hV4 ⊢
  try simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, Prod.fst_neg, Prod.snd_neg, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, dotS, dot2, AltSixEvenOF.kEvenOF, hr1, hr2, hr3, hr4] at h1
  linarith

theorem base_ae21_1 (k : ℕ) (hk : 0 ≤ k) (w u1 u2 : Word) (hph : phase w = 1)
    (hrel : (parentsAt w).odd.num = ((k : ℤ) + 1) ∧ (parentsAt w).odd.den = ((k : ℤ) + 2) ∧ (parentsAt w).even.num = (2 * (k : ℤ) + 1) ∧
      (parentsAt w).even.den = (2 * (k : ℤ) + 3))
    (oP oQ oH : PartialOdometer) (βP βQ : ℤ)
    (_hdP : oP.dom = Standard.oddTile u1) (hdQ : oQ.dom = Standard.evenTile u2)
    (_hcP : TileTranslation.StdCornerValues oP 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (hcQ : TileTranslation.StdCornerValues oQ 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (hdH : ∀ x : ℤ × ℤ, x ∈ oH.dom ↔ x + ((0 : ℤ), (1 : ℤ)) ∈ paperNearStairAltTile (2 * (k : ℤ) + 3))
    (hvH : ∀ x ∈ oH.dom, oH.val x = paperNearStairAltValue (2 * (k : ℤ) + 3) (x + ((0 : ℤ), (1 : ℤ))))
    (hpc : ∃ C : ℤ, ∀ z, z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAE w u1 u2 1 →
      oH.val (z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z - placedAltEven w oP.val oQ.val 0 1 z = C) :
    ∀ z, z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAE w u1 u2 1 →
      oH.val (z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z + (-h0 (texV2 (parentsAt w).odd) + ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2)) = placedAltEven w oP.val oQ.val (AltSixEvenOF.kEvenOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 1 z := by
  obtain ⟨hD, hR, hAf, hSh⟩ := altEven_of w hph
  obtain ⟨C, hC⟩ := hpc
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hrel
  have hB4 := h0_even (texV2 (parentsAt w).odd) (by simp only [texV2]; omega)
  have hV4 := h0_even (texV2 (parentsAt w).even) (by simp only [texV2]; omega)
  have mQ := corner_mem _ _ _ _ _ _ hcQ
  have vQ := corner_raw _ _ _ _ _ hcQ
  rw [hdQ] at mQ
  set p := (parentsAt w).odd with hpdef
  set q := (parentsAt w).even with hqdef
  set A := texV1Odd p with hA
  set B := texV2 p with hBd
  set U := texV1Even q with hU
  set V := texV2 q with hV
  set S := shiftQ w with hSdef
  have ez : S + A + ((0 : ℤ × ℤ)) - (B + U) + ((0 : ℤ), (1 : ℤ)) = ((2 * (k : ℤ) + 4), (2 * (k : ℤ) + 3)) := by
    rw [hSh]; ext <;> simp only [hA, hBd, hU, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, hr1, hr2, hr3, hr4] <;> ring
  have m1 : S + A + ((0 : ℤ × ℤ)) - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) := by
    rw [Finset.mem_coe, hdH, show S + A + ((0 : ℤ × ℤ)) - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) = S + A + ((0 : ℤ × ℤ)) - (B + U) from rfl, ez]
    simp only [paperNearStairAltTile, paperNearStairAltA, paperNearStairAltB, paperNearStairAltC, paperNearStairAltD, Set.mem_union, Set.mem_setOf_eq]
    omega
  have m2 : S + A + ((0 : ℤ × ℤ)) ∈ ClosedPathAlt.dAE w u1 u2 1 := by
    have hdj : ClosedPathAlt.dAE w u1 u2 1 = shiftS (tEvenSet u2) (S + A) := by simp [ClosedPathAlt.dAE, pieceSet, hD]
    rw [hdj]
    exact mem_shift _ _ _ ((0 : ℤ × ℤ)) mQ.1 (by abel)
  have h1 := hC _ m1 m2
  have hval : paperNearStairAltValue (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 4), (2 * (k : ℤ) + 3)) = (-1) := by
    have hq : (((2 * (k : ℤ) + 3) : ℤ) - (2 * (k : ℤ) + 4)) ^ 2 = 4 * (0) + 1 := by ring
    simp only [paperNearStairAltValue, Set.indicator_apply, Set.mem_union, paperNearStairAltA, paperNearStairAltB,
      Set.mem_setOf_eq]
    split_ifs <;> (try simp only [not_or, not_and] at *) <;> omega
  rw [hvH _ m1, ez, hval] at h1
  rw [eval_lt w _ _ 0 1 _ (S + A) (p.num, -p.den) ((0 : ℤ × ℤ)) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) (by abel), vQ.1] at h1
  intro z hz1 hz2
  have h2 := hC z hz1 hz2
  rw [← placedAltEven_add]
  simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, dot2, AltSixEvenOF.kEvenOF, Pi.zero_apply, add_zero, hr1, hr2, hr3, hr4] at h1 h2 hB4 hV4 ⊢
  rw [hSh] at h1
  try simp only [hBd, hU, texV1Even, texV2, Prod.fst_add, Prod.snd_add, hr1, hr2, hr3, hr4] at h1
  linarith

theorem base_ae21_2 (k : ℕ) (hk : 0 ≤ k) (w u1 u2 : Word) (hph : phase w = 1)
    (hrel : (parentsAt w).odd.num = ((k : ℤ) + 1) ∧ (parentsAt w).odd.den = ((k : ℤ) + 2) ∧ (parentsAt w).even.num = (2 * (k : ℤ) + 1) ∧
      (parentsAt w).even.den = (2 * (k : ℤ) + 3))
    (oP oQ oH : PartialOdometer) (βP βQ : ℤ)
    (_hdP : oP.dom = Standard.oddTile u1) (hdQ : oQ.dom = Standard.evenTile u2)
    (_hcP : TileTranslation.StdCornerValues oP 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (hcQ : TileTranslation.StdCornerValues oQ 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (hdH : ∀ x : ℤ × ℤ, x ∈ oH.dom ↔ x + ((0 : ℤ), (1 : ℤ)) ∈ paperNearStairAltTile (2 * (k : ℤ) + 3))
    (hvH : ∀ x ∈ oH.dom, oH.val x = paperNearStairAltValue (2 * (k : ℤ) + 3) (x + ((0 : ℤ), (1 : ℤ))))
    (hpc : ∃ C : ℤ, ∀ z, z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAE w u1 u2 2 →
      oH.val (z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z - placedAltEven w oP.val oQ.val 0 2 z = C) :
    ∀ z, z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAE w u1 u2 2 →
      oH.val (z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z + (-h0 (texV2 (parentsAt w).odd) + ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2)) = placedAltEven w oP.val oQ.val (AltSixEvenOF.kEvenOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 2 z := by
  obtain ⟨hD, hR, hAf, hSh⟩ := altEven_of w hph
  obtain ⟨C, hC⟩ := hpc
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hrel
  have hB4 := h0_even (texV2 (parentsAt w).odd) (by simp only [texV2]; omega)
  have hV4 := h0_even (texV2 (parentsAt w).even) (by simp only [texV2]; omega)
  have mQ := corner_mem _ _ _ _ _ _ hcQ
  have vQ := corner_raw _ _ _ _ _ hcQ
  rw [hdQ] at mQ
  set p := (parentsAt w).odd with hpdef
  set q := (parentsAt w).even with hqdef
  set A := texV1Odd p with hA
  set B := texV2 p with hBd
  set U := texV1Even q with hU
  set V := texV2 q with hV
  set S := shiftQ w with hSdef
  have ez : B + (U) - (B + U) + ((0 : ℤ), (1 : ℤ)) = ((0), (1)) := by
    ext <;> simp only [hBd, hU, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, hr1, hr2, hr3, hr4] <;> ring
  have m1 : B + (U) - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) := by
    rw [Finset.mem_coe, hdH, show B + (U) - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) = B + (U) - (B + U) from rfl, ez]
    simp only [paperNearStairAltTile, paperNearStairAltA, paperNearStairAltB, paperNearStairAltC, paperNearStairAltD, Set.mem_union, Set.mem_setOf_eq]
    omega
  have m2 : B + (U) ∈ ClosedPathAlt.dAE w u1 u2 2 := by
    have hdj : ClosedPathAlt.dAE w u1 u2 2 = shiftS (tEvenSet u2) (B) := by simp [ClosedPathAlt.dAE, pieceSet, hD]
    rw [hdj]
    exact mem_shift _ _ _ (U) mQ.2.2.2.1 (by abel)
  have h1 := hC _ m1 m2
  have hval : paperNearStairAltValue (2 * (k : ℤ) + 3) ((0), (1)) = (0) := by
    have hq : (((1) : ℤ) - (0)) ^ 2 = 4 * (0) + 1 := by ring
    simp only [paperNearStairAltValue, Set.indicator_apply, Set.mem_union, paperNearStairAltA, paperNearStairAltB,
      Set.mem_setOf_eq]
    split_ifs <;> (try simp only [not_or, not_and] at *) <;> omega
  rw [hvH _ m1, ez, hval] at h1
  rw [eval_lt w _ _ 0 2 _ (B) (p.num, -p.den) (U) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) (by abel), vQ.2.2.2.1] at h1
  intro z hz1 hz2
  have h2 := hC z hz1 hz2
  rw [← placedAltEven_add]
  simp only [hBd, hU, hV, texV1Even, texV2, Prod.fst_add, Prod.snd_add, dot2, AltSixEvenOF.kEvenOF, Pi.zero_apply, add_zero, zero_add, hr1, hr2, hr3, hr4] at h1 h2 hB4 hV4 ⊢
  try simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, Prod.fst_neg, Prod.snd_neg, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, dotS, dot2, AltSixEvenOF.kEvenOF, hr1, hr2, hr3, hr4] at h1
  linarith

theorem base_ae21_3 (k : ℕ) (hk : 0 ≤ k) (w u1 u2 : Word) (hph : phase w = 1)
    (hrel : (parentsAt w).odd.num = ((k : ℤ) + 1) ∧ (parentsAt w).odd.den = ((k : ℤ) + 2) ∧ (parentsAt w).even.num = (2 * (k : ℤ) + 1) ∧
      (parentsAt w).even.den = (2 * (k : ℤ) + 3))
    (oP oQ oH : PartialOdometer) (βP βQ : ℤ)
    (_hdP : oP.dom = Standard.oddTile u1) (hdQ : oQ.dom = Standard.evenTile u2)
    (_hcP : TileTranslation.StdCornerValues oP 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (hcQ : TileTranslation.StdCornerValues oQ 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (hdH : ∀ x : ℤ × ℤ, x ∈ oH.dom ↔ x + ((0 : ℤ), (1 : ℤ)) ∈ paperNearStairAltTile (2 * (k : ℤ) + 3))
    (hvH : ∀ x ∈ oH.dom, oH.val x = paperNearStairAltValue (2 * (k : ℤ) + 3) (x + ((0 : ℤ), (1 : ℤ))))
    (hpc : ∃ C : ℤ, ∀ z, z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAE w u1 u2 3 →
      oH.val (z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z - placedAltEven w oP.val oQ.val 0 3 z = C) :
    ∀ z, z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAE w u1 u2 3 →
      oH.val (z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z + (-h0 (texV2 (parentsAt w).odd) + ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2)) = placedAltEven w oP.val oQ.val (AltSixEvenOF.kEvenOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 3 z := by
  obtain ⟨hD, hR, hAf, hSh⟩ := altEven_of w hph
  obtain ⟨C, hC⟩ := hpc
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hrel
  have hB4 := h0_even (texV2 (parentsAt w).odd) (by simp only [texV2]; omega)
  have hV4 := h0_even (texV2 (parentsAt w).even) (by simp only [texV2]; omega)
  have mQ := corner_mem _ _ _ _ _ _ hcQ
  have vQ := corner_raw _ _ _ _ _ hcQ
  rw [hdQ] at mQ
  set p := (parentsAt w).odd with hpdef
  set q := (parentsAt w).even with hqdef
  set A := texV1Odd p with hA
  set B := texV2 p with hBd
  set U := texV1Even q with hU
  set V := texV2 q with hV
  set S := shiftQ w with hSdef
  have ez : S + B + ((0 : ℤ × ℤ)) - (B + U) + ((0 : ℤ), (1 : ℤ)) = ((-1), (2 * (k : ℤ) + 4)) := by
    rw [hSh]; ext <;> simp only [hBd, hU, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, hr1, hr2, hr3, hr4] <;> ring
  have m1 : S + B + ((0 : ℤ × ℤ)) - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) := by
    rw [Finset.mem_coe, hdH, show S + B + ((0 : ℤ × ℤ)) - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) = S + B + ((0 : ℤ × ℤ)) - (B + U) from rfl, ez]
    simp only [paperNearStairAltTile, paperNearStairAltA, paperNearStairAltB, paperNearStairAltC, paperNearStairAltD, Set.mem_union, Set.mem_setOf_eq, true_and]
    omega
  have m2 : S + B + ((0 : ℤ × ℤ)) ∈ ClosedPathAlt.dAE w u1 u2 3 := by
    have hdj : ClosedPathAlt.dAE w u1 u2 3 = shiftS (tEvenSet u2) (S + B) := by simp [ClosedPathAlt.dAE, pieceSet, hD]
    rw [hdj]
    exact mem_shift _ _ _ ((0 : ℤ × ℤ)) mQ.1 (by abel)
  have h1 := hC _ m1 m2
  have hval : paperNearStairAltValue (2 * (k : ℤ) + 3) ((-1), (2 * (k : ℤ) + 4)) = (-(k : ℤ) ^ 2 - 5 * (k : ℤ) - 5) := by
    have hq : (((2 * (k : ℤ) + 4) : ℤ) - (-1)) ^ 2 = 4 * ((k : ℤ) ^ 2 + 5 * (k : ℤ) + 6) + 1 := by ring
    simp only [paperNearStairAltValue, Set.indicator_apply, Set.mem_union, paperNearStairAltA, paperNearStairAltB,
      Set.mem_setOf_eq]
    split_ifs <;> (try simp only [not_or, not_and] at *) <;> omega
  rw [hvH _ m1, ez, hval] at h1
  rw [eval_lt w _ _ 0 3 _ (S + B) ((p.num, -p.den) + (p.num, -p.den)) ((0 : ℤ × ℤ)) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) (by abel), vQ.1] at h1
  intro z hz1 hz2
  have h2 := hC z hz1 hz2
  rw [← placedAltEven_add]
  simp only [hBd, hU, hV, texV1Even, texV2, Prod.fst_add, Prod.snd_add, dot2, AltSixEvenOF.kEvenOF, Pi.zero_apply, add_zero, hr1, hr2, hr3, hr4] at h1 h2 hB4 hV4 ⊢
  rw [hSh] at h1
  try simp only [hBd, hU, texV1Even, texV2, Prod.fst_add, Prod.snd_add, hr1, hr2, hr3, hr4] at h1
  linarith

theorem base_ae21_4 (k : ℕ) (hk : 0 ≤ k) (w u1 u2 : Word) (hph : phase w = 1)
    (hrel : (parentsAt w).odd.num = ((k : ℤ) + 1) ∧ (parentsAt w).odd.den = ((k : ℤ) + 2) ∧ (parentsAt w).even.num = (2 * (k : ℤ) + 1) ∧
      (parentsAt w).even.den = (2 * (k : ℤ) + 3))
    (oP oQ oH : PartialOdometer) (βP βQ : ℤ)
    (hdP : oP.dom = Standard.oddTile u1) (_hdQ : oQ.dom = Standard.evenTile u2)
    (hcP : TileTranslation.StdCornerValues oP 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (_hcQ : TileTranslation.StdCornerValues oQ 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (hdH : ∀ x : ℤ × ℤ, x ∈ oH.dom ↔ x + ((0 : ℤ), (1 : ℤ)) ∈ paperNearStairAltTile (2 * (k : ℤ) + 3))
    (hvH : ∀ x ∈ oH.dom, oH.val x = paperNearStairAltValue (2 * (k : ℤ) + 3) (x + ((0 : ℤ), (1 : ℤ))))
    (hpc : ∃ C : ℤ, ∀ z, z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAE w u1 u2 4 →
      oH.val (z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z - placedAltEven w oP.val oQ.val 0 4 z = C) :
    ∀ z, z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAE w u1 u2 4 →
      oH.val (z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z + (-h0 (texV2 (parentsAt w).odd) + ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2)) = placedAltEven w oP.val oQ.val (AltSixEvenOF.kEvenOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 4 z := by
  obtain ⟨hD, hR, hAf, hSh⟩ := altEven_of w hph
  obtain ⟨C, hC⟩ := hpc
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hrel
  have hB4 := h0_even (texV2 (parentsAt w).odd) (by simp only [texV2]; omega)
  have hV4 := h0_even (texV2 (parentsAt w).even) (by simp only [texV2]; omega)
  have mP := corner_mem _ _ _ _ _ _ hcP
  have vP := corner_raw _ _ _ _ _ hcP
  rw [hdP] at mP
  set p := (parentsAt w).odd with hpdef
  set q := (parentsAt w).even with hqdef
  set A := texV1Odd p with hA
  set B := texV2 p with hBd
  set U := texV1Even q with hU
  set V := texV2 q with hV
  set S := shiftQ w with hSdef
  have ez : 0 + (A + B + ((1 : ℤ), (-1 : ℤ))) - (B + U) + ((0 : ℤ), (1 : ℤ)) = ((2), (1)) := by
    ext <;> simp only [hA, hBd, hU, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, hr1, hr2, hr3, hr4] <;> ring
  have m1 : 0 + (A + B + ((1 : ℤ), (-1 : ℤ))) - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) := by
    rw [Finset.mem_coe, hdH, show 0 + (A + B + ((1 : ℤ), (-1 : ℤ))) - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) = 0 + (A + B + ((1 : ℤ), (-1 : ℤ))) - (B + U) from rfl, ez]
    simp only [paperNearStairAltTile, paperNearStairAltA, paperNearStairAltB, paperNearStairAltC, paperNearStairAltD, Set.mem_union, Set.mem_setOf_eq]
    omega
  have m2 : 0 + (A + B + ((1 : ℤ), (-1 : ℤ))) ∈ ClosedPathAlt.dAE w u1 u2 4 := by
    have hdj : ClosedPathAlt.dAE w u1 u2 4 = shiftS (tOddSet u1) (0) := by simp [ClosedPathAlt.dAE, pieceSet, hD, hR]
    rw [hdj]
    exact mem_shift _ _ _ (A + B + ((1 : ℤ), (-1 : ℤ))) mP.2.2.2.2.2.2.1 (by abel)
  have h1 := hC _ m1 m2
  have hval : paperNearStairAltValue (2 * (k : ℤ) + 3) ((2), (1)) = (0) := by
    have hq : (((1) : ℤ) - (2)) ^ 2 = 4 * (0) + 1 := by ring
    simp only [paperNearStairAltValue, Set.indicator_apply, Set.mem_union, paperNearStairAltA, paperNearStairAltB,
      Set.mem_setOf_eq]
    split_ifs <;> (try simp only [not_or, not_and] at *) <;> omega
  rw [hvH _ m1, ez, hval] at h1
  rw [eval_ge w _ _ 0 4 _ (0) 0 (A + B + ((1 : ℤ), (-1 : ℤ))) (by norm_num) (by rw [hR]; rfl) (by rw [hAf]; rfl) (by abel), vP.2.2.2.2.2.2.1] at h1
  intro z hz1 hz2
  have h2 := hC z hz1 hz2
  rw [← placedAltEven_add]
  simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero, dot2, AltSixEvenOF.kEvenOF, Pi.zero_apply, zero_mul, add_zero, zero_add, hr1, hr2, hr3, hr4] at h1 h2 hB4 hV4 ⊢
  try simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, Prod.fst_neg, Prod.snd_neg, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, dotS, dot2, AltSixEvenOF.kEvenOF, hr1, hr2, hr3, hr4] at h1
  linarith

theorem base_ae21_5 (k : ℕ) (hk : 0 ≤ k) (w u1 u2 : Word) (hph : phase w = 1)
    (hrel : (parentsAt w).odd.num = ((k : ℤ) + 1) ∧ (parentsAt w).odd.den = ((k : ℤ) + 2) ∧ (parentsAt w).even.num = (2 * (k : ℤ) + 1) ∧
      (parentsAt w).even.den = (2 * (k : ℤ) + 3))
    (oP oQ oH : PartialOdometer) (βP βQ : ℤ)
    (hdP : oP.dom = Standard.oddTile u1) (_hdQ : oQ.dom = Standard.evenTile u2)
    (hcP : TileTranslation.StdCornerValues oP 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (_hcQ : TileTranslation.StdCornerValues oQ 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (hdH : ∀ x : ℤ × ℤ, x ∈ oH.dom ↔ x + ((0 : ℤ), (1 : ℤ)) ∈ paperNearStairAltTile (2 * (k : ℤ) + 3))
    (hvH : ∀ x ∈ oH.dom, oH.val x = paperNearStairAltValue (2 * (k : ℤ) + 3) (x + ((0 : ℤ), (1 : ℤ))))
    (hpc : ∃ C : ℤ, ∀ z, z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAE w u1 u2 5 →
      oH.val (z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z - placedAltEven w oP.val oQ.val 0 5 z = C) :
    ∀ z, z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAE w u1 u2 5 →
      oH.val (z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z + (-h0 (texV2 (parentsAt w).odd) + ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2)) = placedAltEven w oP.val oQ.val (AltSixEvenOF.kEvenOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 5 z := by
  obtain ⟨hD, hR, hAf, hSh⟩ := altEven_of w hph
  obtain ⟨C, hC⟩ := hpc
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hrel
  have hB4 := h0_even (texV2 (parentsAt w).odd) (by simp only [texV2]; omega)
  have hV4 := h0_even (texV2 (parentsAt w).even) (by simp only [texV2]; omega)
  have mP := corner_mem _ _ _ _ _ _ hcP
  have vP := corner_raw _ _ _ _ _ hcP
  rw [hdP] at mP
  set p := (parentsAt w).odd with hpdef
  set q := (parentsAt w).even with hqdef
  set A := texV1Odd p with hA
  set B := texV2 p with hBd
  set U := texV1Even q with hU
  set V := texV2 q with hV
  set S := shiftQ w with hSdef
  have ez : B + U + U + V + ((0 : ℤ × ℤ)) - (B + U) + ((0 : ℤ), (1 : ℤ)) = ((2 * (k : ℤ) + 1), (6 * (k : ℤ) + 6)) := by
    ext <;> simp only [hBd, hU, hV, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, hr1, hr2, hr3, hr4] <;> ring
  have m1 : B + U + U + V + ((0 : ℤ × ℤ)) - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) := by
    rw [Finset.mem_coe, hdH, show B + U + U + V + ((0 : ℤ × ℤ)) - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) = B + U + U + V + ((0 : ℤ × ℤ)) - (B + U) from rfl, ez]
    simp only [paperNearStairAltTile, paperNearStairAltA, paperNearStairAltB, paperNearStairAltC, paperNearStairAltD, Set.mem_union, Set.mem_setOf_eq]
    omega
  have m2 : B + U + U + V + ((0 : ℤ × ℤ)) ∈ ClosedPathAlt.dAE w u1 u2 5 := by
    have hdj : ClosedPathAlt.dAE w u1 u2 5 = shiftS (tOddSet u1) (B + U + U + V) := by simp [ClosedPathAlt.dAE, pieceSet, hD, hR]
    rw [hdj]
    exact mem_shift _ _ _ ((0 : ℤ × ℤ)) mP.1 (by abel)
  have h1 := hC _ m1 m2
  have hval : paperNearStairAltValue (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 1), (6 * (k : ℤ) + 6)) = (-4 * (k : ℤ) ^ 2 - 14 * (k : ℤ) - 8) := by
    have hq : (((6 * (k : ℤ) + 6) : ℤ) - (2 * (k : ℤ) + 1)) ^ 2 = 4 * (4 * (k : ℤ) ^ 2 + 10 * (k : ℤ) + 6) + 1 := by ring
    simp only [paperNearStairAltValue, Set.indicator_apply, Set.mem_union, paperNearStairAltA, paperNearStairAltB,
      Set.mem_setOf_eq]
    split_ifs <;> (try simp only [not_or, not_and] at *) <;> omega
  rw [hvH _ m1, ez, hval] at h1
  rw [eval_ge w _ _ 0 5 _ (B + U + U + V) ((p.num, -p.den) + (q.num, -q.den)) ((0 : ℤ × ℤ)) (by norm_num) (by rw [hR]; rfl) (by rw [hAf]; rfl) (by abel), vP.1] at h1
  intro z hz1 hz2
  have h2 := hC z hz1 hz2
  rw [← placedAltEven_add]
  simp only [hBd, hU, hV, texV1Even, texV2, Prod.fst_add, Prod.snd_add, dot2, AltSixEvenOF.kEvenOF, Pi.zero_apply, add_zero, hr1, hr2, hr3, hr4] at h1 h2 hB4 hV4 ⊢
  try simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, Prod.fst_neg, Prod.snd_neg, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, dotS, dot2, AltSixEvenOF.kEvenOF, hr1, hr2, hr3, hr4] at h1
  linarith

theorem base_ao31_0 (k : ℕ) (hk : 0 ≤ k) (w u1 u2 : Word) (hph : phase w = 1)
    (hrel : (parentsAt w).odd.num = (1) ∧ (parentsAt w).odd.den = (2 * (k : ℤ) + 2) ∧ (parentsAt w).even.num = (1) ∧
      (parentsAt w).even.den = (2 * (k : ℤ) + 3))
    (oP oQ oH : PartialOdometer) (βP βQ : ℤ)
    (hdP : oP.dom = Standard.oddTile u1) (_hdQ : oQ.dom = Standard.evenTile u2)
    (hcP : TileTranslation.StdCornerValues oP 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (_hcQ : TileTranslation.StdCornerValues oQ 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (hdH : ∀ x : ℤ × ℤ, x ∈ oH.dom ↔ x + ((0 : ℤ), (0 : ℤ)) ∈ paperStairAltTile (2 * (k : ℤ) + 3))
    (hvH : ∀ x ∈ oH.dom, oH.val x = paperStairAltValue (2 * (k : ℤ) + 3) (x + ((0 : ℤ), (0 : ℤ))))
    (hpc : ∃ C : ℤ, ∀ z, z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAO w u1 u2 0 →
      oH.val (z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z - placedAltOdd w oP.val oQ.val 0 0 z = C) :
    ∀ z, z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAO w u1 u2 0 →
      oH.val (z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z + (-h0 (texV2 (parentsAt w).odd) + ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2)) = placedAltOdd w oP.val oQ.val (kOddOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 0 z := by
  obtain ⟨hD, hR, hAf, hSh⟩ := altOdd_of w hph
  obtain ⟨C, hC⟩ := hpc
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hrel
  have hB4 := h0_even (texV2 (parentsAt w).odd) (by simp only [texV2]; omega)
  have hV4 := h0_even (texV2 (parentsAt w).even) (by simp only [texV2]; omega)
  have mP := corner_mem _ _ _ _ _ _ hcP
  have vP := corner_raw _ _ _ _ _ hcP
  rw [hdP] at mP
  set p := (parentsAt w).odd with hpdef
  set q := (parentsAt w).even with hqdef
  set A := texV1Odd p with hA
  set B := texV2 p with hBd
  set U := texV1Even q with hU
  set V := texV2 q with hV
  set S := shiftP w with hSdef
  have ez : 0 + (B + ((1 : ℤ), (0 : ℤ))) - (A + B - U) + ((0 : ℤ), (0 : ℤ)) = ((-2 * (k : ℤ)), (-1)) := by
    ext <;> simp only [hA, hBd, hU, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, hr1, hr2, hr3, hr4] <;> ring
  have m1 : 0 + (B + ((1 : ℤ), (0 : ℤ))) - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) := by
    rw [Finset.mem_coe, hdH, show 0 + (B + ((1 : ℤ), (0 : ℤ))) - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) = 0 + (B + ((1 : ℤ), (0 : ℤ))) - (A + B - U) from rfl, ez]
    simp only [paperStairAltTile, paperStairAltA, paperStairAltB, paperStairAltC, paperStairAltD, Set.mem_union, Set.mem_setOf_eq, and_true]
    omega
  have m2 : 0 + (B + ((1 : ℤ), (0 : ℤ))) ∈ ClosedPathAlt.dAO w u1 u2 0 := by
    have hdj : ClosedPathAlt.dAO w u1 u2 0 = shiftS (tOddSet u1) (0) := by simp [ClosedPathAlt.dAO, pieceSet, hD]
    rw [hdj]
    exact mem_shift _ _ _ (B + ((1 : ℤ), (0 : ℤ))) mP.2.2.2.2.1 (by abel)
  have h1 := hC _ m1 m2
  have hval : paperStairAltValue (2 * (k : ℤ) + 3) ((-2 * (k : ℤ)), (-1)) = (0) := by
    have hq : ((-1) : ℤ) * ((-1) + 1) = 2 * (0) + 0 := by ring
    simp only [paperStairAltValue, Set.indicator_apply, Set.mem_union, paperStairAltA, paperStairAltB,
      Set.mem_setOf_eq]
    split_ifs <;> (try simp only [not_or, not_and] at *) <;> omega
  rw [hvH _ m1, ez, hval] at h1
  rw [evalO_lt w _ _ 0 0 _ (0) 0 (B + ((1 : ℤ), (0 : ℤ))) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) (by abel), vP.2.2.2.2.1] at h1
  intro z hz1 hz2
  have h2 := hC z hz1 hz2
  rw [← placedAltOdd_add]
  simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero, dot2, kOddOF, Pi.zero_apply, zero_mul, add_zero, zero_add, hr1, hr2, hr3, hr4] at h1 h2 hB4 hV4 ⊢
  try simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, Prod.fst_neg, Prod.snd_neg, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, dotS, dot2, kOddOF, hr1, hr2, hr3, hr4] at h1
  linarith

theorem base_ao31_1 (k : ℕ) (hk : 0 ≤ k) (w u1 u2 : Word) (hph : phase w = 1)
    (hrel : (parentsAt w).odd.num = (1) ∧ (parentsAt w).odd.den = (2 * (k : ℤ) + 2) ∧ (parentsAt w).even.num = (1) ∧
      (parentsAt w).even.den = (2 * (k : ℤ) + 3))
    (oP oQ oH : PartialOdometer) (βP βQ : ℤ)
    (hdP : oP.dom = Standard.oddTile u1) (_hdQ : oQ.dom = Standard.evenTile u2)
    (hcP : TileTranslation.StdCornerValues oP 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (_hcQ : TileTranslation.StdCornerValues oQ 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (hdH : ∀ x : ℤ × ℤ, x ∈ oH.dom ↔ x + ((0 : ℤ), (0 : ℤ)) ∈ paperStairAltTile (2 * (k : ℤ) + 3))
    (hvH : ∀ x ∈ oH.dom, oH.val x = paperStairAltValue (2 * (k : ℤ) + 3) (x + ((0 : ℤ), (0 : ℤ))))
    (hpc : ∃ C : ℤ, ∀ z, z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAO w u1 u2 1 →
      oH.val (z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z - placedAltOdd w oP.val oQ.val 0 1 z = C) :
    ∀ z, z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAO w u1 u2 1 →
      oH.val (z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z + (-h0 (texV2 (parentsAt w).odd) + ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2)) = placedAltOdd w oP.val oQ.val (kOddOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 1 z := by
  obtain ⟨hD, hR, hAf, hSh⟩ := altOdd_of w hph
  obtain ⟨C, hC⟩ := hpc
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hrel
  have hB4 := h0_even (texV2 (parentsAt w).odd) (by simp only [texV2]; omega)
  have hV4 := h0_even (texV2 (parentsAt w).even) (by simp only [texV2]; omega)
  have mP := corner_mem _ _ _ _ _ _ hcP
  have vP := corner_raw _ _ _ _ _ hcP
  rw [hdP] at mP
  set p := (parentsAt w).odd with hpdef
  set q := (parentsAt w).even with hqdef
  set A := texV1Odd p with hA
  set B := texV2 p with hBd
  set U := texV1Even q with hU
  set V := texV2 q with hV
  set S := shiftP w with hSdef
  have ez : S + 0 + (A - ((0 : ℤ), (1 : ℤ))) - (A + B - U) + ((0 : ℤ), (0 : ℤ)) = ((0), (-1)) := by
    rw [hSh]; ext <;> simp only [hA, hBd, hU, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, Prod.fst_neg, Prod.snd_neg, hr1, hr2, hr3, hr4] <;> ring
  have m1 : S + 0 + (A - ((0 : ℤ), (1 : ℤ))) - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) := by
    rw [Finset.mem_coe, hdH, show S + 0 + (A - ((0 : ℤ), (1 : ℤ))) - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) = S + 0 + (A - ((0 : ℤ), (1 : ℤ))) - (A + B - U) from rfl, ez]
    simp only [paperStairAltTile, paperStairAltA, paperStairAltB, paperStairAltC, paperStairAltD, Set.mem_union, Set.mem_setOf_eq, and_true]
    omega
  have m2 : S + 0 + (A - ((0 : ℤ), (1 : ℤ))) ∈ ClosedPathAlt.dAO w u1 u2 1 := by
    have hdj : ClosedPathAlt.dAO w u1 u2 1 = shiftS (tOddSet u1) (S + 0) := by simp [ClosedPathAlt.dAO, pieceSet, hD]
    rw [hdj]
    exact mem_shift _ _ _ (A - ((0 : ℤ), (1 : ℤ))) mP.2.2.1 (by abel)
  have h1 := hC _ m1 m2
  have hval : paperStairAltValue (2 * (k : ℤ) + 3) ((0), (-1)) = (0) := by
    have hq : ((-1) : ℤ) * ((-1) + 1) = 2 * (0) + 0 := by ring
    simp only [paperStairAltValue, Set.indicator_apply, Set.mem_union, paperStairAltA, paperStairAltB,
      Set.mem_setOf_eq]
    split_ifs <;> (try simp only [not_or, not_and] at *) <;> omega
  rw [hvH _ m1, ez, hval] at h1
  rw [evalO_lt w _ _ 0 1 _ (S + 0) (p.num, -p.den) (A - ((0 : ℤ), (1 : ℤ))) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) (by abel), vP.2.2.1] at h1
  intro z hz1 hz2
  have h2 := hC z hz1 hz2
  rw [← placedAltOdd_add]
  simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, dot2, kOddOF, Pi.zero_apply, add_zero, zero_add, hr1, hr2, hr3, hr4] at h1 h2 hB4 hV4 ⊢
  rw [hSh] at h1
  try simp only [hBd, hU, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg, hr1, hr2, hr3, hr4] at h1
  linarith

theorem base_ao31_2 (k : ℕ) (hk : 0 ≤ k) (w u1 u2 : Word) (hph : phase w = 1)
    (hrel : (parentsAt w).odd.num = (1) ∧ (parentsAt w).odd.den = (2 * (k : ℤ) + 2) ∧ (parentsAt w).even.num = (1) ∧
      (parentsAt w).even.den = (2 * (k : ℤ) + 3))
    (oP oQ oH : PartialOdometer) (βP βQ : ℤ)
    (hdP : oP.dom = Standard.oddTile u1) (_hdQ : oQ.dom = Standard.evenTile u2)
    (hcP : TileTranslation.StdCornerValues oP 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (_hcQ : TileTranslation.StdCornerValues oQ 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (hdH : ∀ x : ℤ × ℤ, x ∈ oH.dom ↔ x + ((0 : ℤ), (0 : ℤ)) ∈ paperStairAltTile (2 * (k : ℤ) + 3))
    (hvH : ∀ x ∈ oH.dom, oH.val x = paperStairAltValue (2 * (k : ℤ) + 3) (x + ((0 : ℤ), (0 : ℤ))))
    (hpc : ∃ C : ℤ, ∀ z, z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAO w u1 u2 2 →
      oH.val (z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z - placedAltOdd w oP.val oQ.val 0 2 z = C) :
    ∀ z, z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAO w u1 u2 2 →
      oH.val (z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z + (-h0 (texV2 (parentsAt w).odd) + ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2)) = placedAltOdd w oP.val oQ.val (kOddOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 2 z := by
  obtain ⟨hD, hR, hAf, hSh⟩ := altOdd_of w hph
  obtain ⟨C, hC⟩ := hpc
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hrel
  have hB4 := h0_even (texV2 (parentsAt w).odd) (by simp only [texV2]; omega)
  have hV4 := h0_even (texV2 (parentsAt w).even) (by simp only [texV2]; omega)
  have mP := corner_mem _ _ _ _ _ _ hcP
  have vP := corner_raw _ _ _ _ _ hcP
  rw [hdP] at mP
  set p := (parentsAt w).odd with hpdef
  set q := (parentsAt w).even with hqdef
  set A := texV1Odd p with hA
  set B := texV2 p with hBd
  set U := texV1Even q with hU
  set V := texV2 q with hV
  set S := shiftP w with hSdef
  have ez : U + V + ((0 : ℤ × ℤ)) - (A + B - U) + ((0 : ℤ), (0 : ℤ)) = ((1), (1)) := by
    ext <;> simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, hr1, hr2, hr3, hr4] <;> ring
  have m1 : U + V + ((0 : ℤ × ℤ)) - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) := by
    rw [Finset.mem_coe, hdH, show U + V + ((0 : ℤ × ℤ)) - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) = U + V + ((0 : ℤ × ℤ)) - (A + B - U) from rfl, ez]
    simp only [paperStairAltTile, paperStairAltA, paperStairAltB, paperStairAltC, paperStairAltD, Set.mem_union, Set.mem_setOf_eq]
    omega
  have m2 : U + V + ((0 : ℤ × ℤ)) ∈ ClosedPathAlt.dAO w u1 u2 2 := by
    have hdj : ClosedPathAlt.dAO w u1 u2 2 = shiftS (tOddSet u1) (U + V) := by simp [ClosedPathAlt.dAO, pieceSet, hD]
    rw [hdj]
    exact mem_shift _ _ _ ((0 : ℤ × ℤ)) mP.1 (by abel)
  have h1 := hC _ m1 m2
  have hval : paperStairAltValue (2 * (k : ℤ) + 3) ((1), (1)) = (0) := by
    have hq : ((1) : ℤ) * ((1) + 1) = 2 * (1) + 0 := by ring
    simp only [paperStairAltValue, Set.indicator_apply, Set.mem_union, paperStairAltA, paperStairAltB,
      Set.mem_setOf_eq]
    split_ifs <;> (try simp only [not_or, not_and] at *) <;> omega
  rw [hvH _ m1, ez, hval] at h1
  rw [evalO_lt w _ _ 0 2 _ (U + V) (q.num, -q.den) ((0 : ℤ × ℤ)) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) (by abel), vP.1] at h1
  intro z hz1 hz2
  have h2 := hC z hz1 hz2
  rw [← placedAltOdd_add]
  simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, dot2, kOddOF, Pi.zero_apply, add_zero, zero_add, hr1, hr2, hr3, hr4] at h1 h2 hB4 hV4 ⊢
  try simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, Prod.fst_neg, Prod.snd_neg, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, dotS, dot2, kOddOF, hr1, hr2, hr3, hr4] at h1
  linarith

theorem base_ao31_3 (k : ℕ) (hk : 0 ≤ k) (w u1 u2 : Word) (hph : phase w = 1)
    (hrel : (parentsAt w).odd.num = (1) ∧ (parentsAt w).odd.den = (2 * (k : ℤ) + 2) ∧ (parentsAt w).even.num = (1) ∧
      (parentsAt w).even.den = (2 * (k : ℤ) + 3))
    (oP oQ oH : PartialOdometer) (βP βQ : ℤ)
    (hdP : oP.dom = Standard.oddTile u1) (_hdQ : oQ.dom = Standard.evenTile u2)
    (hcP : TileTranslation.StdCornerValues oP 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (_hcQ : TileTranslation.StdCornerValues oQ 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (hdH : ∀ x : ℤ × ℤ, x ∈ oH.dom ↔ x + ((0 : ℤ), (0 : ℤ)) ∈ paperStairAltTile (2 * (k : ℤ) + 3))
    (hvH : ∀ x ∈ oH.dom, oH.val x = paperStairAltValue (2 * (k : ℤ) + 3) (x + ((0 : ℤ), (0 : ℤ))))
    (hpc : ∃ C : ℤ, ∀ z, z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAO w u1 u2 3 →
      oH.val (z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z - placedAltOdd w oP.val oQ.val 0 3 z = C) :
    ∀ z, z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAO w u1 u2 3 →
      oH.val (z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z + (-h0 (texV2 (parentsAt w).odd) + ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2)) = placedAltOdd w oP.val oQ.val (kOddOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 3 z := by
  obtain ⟨hD, hR, hAf, hSh⟩ := altOdd_of w hph
  obtain ⟨C, hC⟩ := hpc
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hrel
  have hB4 := h0_even (texV2 (parentsAt w).odd) (by simp only [texV2]; omega)
  have hV4 := h0_even (texV2 (parentsAt w).even) (by simp only [texV2]; omega)
  have mP := corner_mem _ _ _ _ _ _ hcP
  have vP := corner_raw _ _ _ _ _ hcP
  rw [hdP] at mP
  set p := (parentsAt w).odd with hpdef
  set q := (parentsAt w).even with hqdef
  set A := texV1Odd p with hA
  set B := texV2 p with hBd
  set U := texV1Even q with hU
  set V := texV2 q with hV
  set S := shiftP w with hSdef
  have ez : S + (U + V) + (((1 : ℤ), (0 : ℤ))) - (A + B - U) + ((0 : ℤ), (0 : ℤ)) = ((-4 * (k : ℤ) - 2), (2 * (k : ℤ) + 3)) := by
    rw [hSh]; ext <;> simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_neg, Prod.snd_neg, hr1, hr2, hr3, hr4] <;> ring
  have m1 : S + (U + V) + (((1 : ℤ), (0 : ℤ))) - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) := by
    rw [Finset.mem_coe, hdH, show S + (U + V) + (((1 : ℤ), (0 : ℤ))) - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) = S + (U + V) + (((1 : ℤ), (0 : ℤ))) - (A + B - U) from rfl, ez]
    simp only [paperStairAltTile, paperStairAltA, paperStairAltB, paperStairAltC, paperStairAltD, Set.mem_union, Set.mem_setOf_eq]
    omega
  have m2 : S + (U + V) + (((1 : ℤ), (0 : ℤ))) ∈ ClosedPathAlt.dAO w u1 u2 3 := by
    have hdj : ClosedPathAlt.dAO w u1 u2 3 = shiftS (tOddSet u1) (S + (U + V)) := by simp [ClosedPathAlt.dAO, pieceSet, hD]
    rw [hdj]
    exact mem_shift _ _ _ (((1 : ℤ), (0 : ℤ))) mP.2.1 (by abel)
  have h1 := hC _ m1 m2
  have hval : paperStairAltValue (2 * (k : ℤ) + 3) ((-4 * (k : ℤ) - 2), (2 * (k : ℤ) + 3)) = (-2 * (k : ℤ) ^ 2 - 9 * (k : ℤ) - 7) := by
    have hq : ((2 * (k : ℤ) + 3) : ℤ) * ((2 * (k : ℤ) + 3) + 1) = 2 * (2 * (k : ℤ) ^ 2 + 7 * (k : ℤ) + 6) + 0 := by ring
    simp only [paperStairAltValue, Set.indicator_apply, Set.mem_union, paperStairAltA, paperStairAltB,
      Set.mem_setOf_eq]
    split_ifs <;> (try simp only [not_or, not_and] at *) <;> omega
  rw [hvH _ m1, ez, hval] at h1
  rw [evalO_lt w _ _ 0 3 _ (S + (U + V)) ((q.num, -q.den) + (p.num, -p.den)) (((1 : ℤ), (0 : ℤ))) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) (by abel), vP.2.1] at h1
  intro z hz1 hz2
  have h2 := hC z hz1 hz2
  rw [← placedAltOdd_add]
  simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, dot2, kOddOF, Pi.zero_apply, add_zero, hr1, hr2, hr3, hr4] at h1 h2 hB4 hV4 ⊢
  rw [hSh] at h1
  try simp only [hBd, hU, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg, hr1, hr2, hr3, hr4] at h1
  linarith

theorem base_ao31_4 (k : ℕ) (hk : 0 ≤ k) (w u1 u2 : Word) (hph : phase w = 1)
    (hrel : (parentsAt w).odd.num = (1) ∧ (parentsAt w).odd.den = (2 * (k : ℤ) + 2) ∧ (parentsAt w).even.num = (1) ∧
      (parentsAt w).even.den = (2 * (k : ℤ) + 3))
    (oP oQ oH : PartialOdometer) (βP βQ : ℤ)
    (_hdP : oP.dom = Standard.oddTile u1) (hdQ : oQ.dom = Standard.evenTile u2)
    (_hcP : TileTranslation.StdCornerValues oP 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (hcQ : TileTranslation.StdCornerValues oQ 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (hdH : ∀ x : ℤ × ℤ, x ∈ oH.dom ↔ x + ((0 : ℤ), (0 : ℤ)) ∈ paperStairAltTile (2 * (k : ℤ) + 3))
    (hvH : ∀ x ∈ oH.dom, oH.val x = paperStairAltValue (2 * (k : ℤ) + 3) (x + ((0 : ℤ), (0 : ℤ))))
    (hpc : ∃ C : ℤ, ∀ z, z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAO w u1 u2 4 →
      oH.val (z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z - placedAltOdd w oP.val oQ.val 0 4 z = C) :
    ∀ z, z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAO w u1 u2 4 →
      oH.val (z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z + (-h0 (texV2 (parentsAt w).odd) + ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2)) = placedAltOdd w oP.val oQ.val (kOddOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 4 z := by
  obtain ⟨hD, hR, hAf, hSh⟩ := altOdd_of w hph
  obtain ⟨C, hC⟩ := hpc
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hrel
  have hB4 := h0_even (texV2 (parentsAt w).odd) (by simp only [texV2]; omega)
  have hV4 := h0_even (texV2 (parentsAt w).even) (by simp only [texV2]; omega)
  have mQ := corner_mem _ _ _ _ _ _ hcQ
  have vQ := corner_raw _ _ _ _ _ hcQ
  rw [hdQ] at mQ
  set p := (parentsAt w).odd with hpdef
  set q := (parentsAt w).even with hqdef
  set A := texV1Odd p with hA
  set B := texV2 p with hBd
  set U := texV1Even q with hU
  set V := texV2 q with hV
  set S := shiftP w with hSdef
  have ez : A + (V + ((1 : ℤ), (0 : ℤ))) - (A + B - U) + ((0 : ℤ), (0 : ℤ)) = ((2 * (k : ℤ) + 3), (2)) := by
    ext <;> simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, hr1, hr2, hr3, hr4] <;> ring
  have m1 : A + (V + ((1 : ℤ), (0 : ℤ))) - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) := by
    rw [Finset.mem_coe, hdH, show A + (V + ((1 : ℤ), (0 : ℤ))) - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) = A + (V + ((1 : ℤ), (0 : ℤ))) - (A + B - U) from rfl, ez]
    simp only [paperStairAltTile, paperStairAltA, paperStairAltB, paperStairAltC, paperStairAltD, Set.mem_union, Set.mem_setOf_eq]
    omega
  have m2 : A + (V + ((1 : ℤ), (0 : ℤ))) ∈ ClosedPathAlt.dAO w u1 u2 4 := by
    have hdj : ClosedPathAlt.dAO w u1 u2 4 = shiftS (tEvenSet u2) (A) := by simp [ClosedPathAlt.dAO, pieceSet, hD, hR]
    rw [hdj]
    exact mem_shift _ _ _ (V + ((1 : ℤ), (0 : ℤ))) mQ.2.2.2.2.1 (by abel)
  have h1 := hC _ m1 m2
  have hval : paperStairAltValue (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3), (2)) = (-1) := by
    have hq : ((2) : ℤ) * ((2) + 1) = 2 * (3) + 0 := by ring
    simp only [paperStairAltValue, Set.indicator_apply, Set.mem_union, paperStairAltA, paperStairAltB,
      Set.mem_setOf_eq]
    split_ifs <;> (try simp only [not_or, not_and] at *) <;> omega
  rw [hvH _ m1, ez, hval] at h1
  rw [evalO_ge w _ _ 0 4 _ (A) 0 (V + ((1 : ℤ), (0 : ℤ))) (by norm_num) (by rw [hR]; rfl) (by rw [hAf]; rfl) (by abel), vQ.2.2.2.2.1] at h1
  intro z hz1 hz2
  have h2 := hC z hz1 hz2
  rw [← placedAltOdd_add]
  simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero, dot2, kOddOF, Pi.zero_apply, zero_mul, add_zero, hr1, hr2, hr3, hr4] at h1 h2 hB4 hV4 ⊢
  try simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, Prod.fst_neg, Prod.snd_neg, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, dotS, dot2, kOddOF, hr1, hr2, hr3, hr4] at h1
  linarith

theorem base_ao31_5 (k : ℕ) (hk : 0 ≤ k) (w u1 u2 : Word) (hph : phase w = 1)
    (hrel : (parentsAt w).odd.num = (1) ∧ (parentsAt w).odd.den = (2 * (k : ℤ) + 2) ∧ (parentsAt w).even.num = (1) ∧
      (parentsAt w).even.den = (2 * (k : ℤ) + 3))
    (oP oQ oH : PartialOdometer) (βP βQ : ℤ)
    (_hdP : oP.dom = Standard.oddTile u1) (hdQ : oQ.dom = Standard.evenTile u2)
    (_hcP : TileTranslation.StdCornerValues oP 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (hcQ : TileTranslation.StdCornerValues oQ 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (hdH : ∀ x : ℤ × ℤ, x ∈ oH.dom ↔ x + ((0 : ℤ), (0 : ℤ)) ∈ paperStairAltTile (2 * (k : ℤ) + 3))
    (hvH : ∀ x ∈ oH.dom, oH.val x = paperStairAltValue (2 * (k : ℤ) + 3) (x + ((0 : ℤ), (0 : ℤ))))
    (hpc : ∃ C : ℤ, ∀ z, z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAO w u1 u2 5 →
      oH.val (z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z - placedAltOdd w oP.val oQ.val 0 5 z = C) :
    ∀ z, z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAO w u1 u2 5 →
      oH.val (z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z + (-h0 (texV2 (parentsAt w).odd) + ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2)) = placedAltOdd w oP.val oQ.val (kOddOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 5 z := by
  obtain ⟨hD, hR, hAf, hSh⟩ := altOdd_of w hph
  obtain ⟨C, hC⟩ := hpc
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hrel
  have hB4 := h0_even (texV2 (parentsAt w).odd) (by simp only [texV2]; omega)
  have hV4 := h0_even (texV2 (parentsAt w).even) (by simp only [texV2]; omega)
  have mQ := corner_mem _ _ _ _ _ _ hcQ
  have vQ := corner_raw _ _ _ _ _ hcQ
  rw [hdQ] at mQ
  set p := (parentsAt w).odd with hpdef
  set q := (parentsAt w).even with hqdef
  set A := texV1Odd p with hA
  set B := texV2 p with hBd
  set U := texV1Even q with hU
  set V := texV2 q with hV
  set S := shiftP w with hSdef
  have ez : B + B - U + (U - ((0 : ℤ), (1 : ℤ))) - (A + B - U) + ((0 : ℤ), (0 : ℤ)) = ((-4 * (k : ℤ) - 2), (2 * (k : ℤ) + 1)) := by
    ext <;> simp only [hA, hBd, hU, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, hr1, hr2, hr3, hr4] <;> ring
  have m1 : B + B - U + (U - ((0 : ℤ), (1 : ℤ))) - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) := by
    rw [Finset.mem_coe, hdH, show B + B - U + (U - ((0 : ℤ), (1 : ℤ))) - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) = B + B - U + (U - ((0 : ℤ), (1 : ℤ))) - (A + B - U) from rfl, ez]
    simp only [paperStairAltTile, paperStairAltA, paperStairAltB, paperStairAltC, paperStairAltD, Set.mem_union, Set.mem_setOf_eq]
    omega
  have m2 : B + B - U + (U - ((0 : ℤ), (1 : ℤ))) ∈ ClosedPathAlt.dAO w u1 u2 5 := by
    have hdj : ClosedPathAlt.dAO w u1 u2 5 = shiftS (tEvenSet u2) (B + B - U) := by simp [ClosedPathAlt.dAO, pieceSet, hD, hR]
    rw [hdj]
    exact mem_shift _ _ _ (U - ((0 : ℤ), (1 : ℤ))) mQ.2.2.1 (by abel)
  have h1 := hC _ m1 m2
  have hval : paperStairAltValue (2 * (k : ℤ) + 3) ((-4 * (k : ℤ) - 2), (2 * (k : ℤ) + 1)) = (-2 * (k : ℤ) ^ 2 - 5 * (k : ℤ) - 2) := by
    have hq : ((2 * (k : ℤ) + 1) : ℤ) * ((2 * (k : ℤ) + 1) + 1) = 2 * (2 * (k : ℤ) ^ 2 + 3 * (k : ℤ) + 1) + 0 := by ring
    simp only [paperStairAltValue, Set.indicator_apply, Set.mem_union, paperStairAltA, paperStairAltB,
      Set.mem_setOf_eq]
    split_ifs <;> (try simp only [not_or, not_and] at *) <;> omega
  rw [hvH _ m1, ez, hval] at h1
  rw [evalO_ge w _ _ 0 5 _ (B + B - U) ((p.num, -p.den) + (p.num, -p.den)) (U - ((0 : ℤ), (1 : ℤ))) (by norm_num) (by rw [hR]; rfl) (by rw [hAf]; rfl) (by abel), vQ.2.2.1] at h1
  intro z hz1 hz2
  have h2 := hC z hz1 hz2
  rw [← placedAltOdd_add]
  simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, dot2, kOddOF, Pi.zero_apply, add_zero, hr1, hr2, hr3, hr4] at h1 h2 hB4 hV4 ⊢
  try simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, Prod.fst_neg, Prod.snd_neg, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, dotS, dot2, kOddOF, hr1, hr2, hr3, hr4] at h1
  linarith

theorem base_ao21_0 (k : ℕ) (hk : 1 ≤ k) (w u1 u2 : Word) (hph : phase w = 1)
    (hrel : (parentsAt w).odd.num = ((k : ℤ) + 1) ∧ (parentsAt w).odd.den = ((k : ℤ) + 2) ∧ (parentsAt w).even.num = (2 * (k : ℤ) + 1) ∧
      (parentsAt w).even.den = (2 * (k : ℤ) + 3))
    (oP oQ oH : PartialOdometer) (βP βQ : ℤ)
    (hdP : oP.dom = Standard.oddTile u1) (_hdQ : oQ.dom = Standard.evenTile u2)
    (hcP : TileTranslation.StdCornerValues oP 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (_hcQ : TileTranslation.StdCornerValues oQ 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (hdH : ∀ x : ℤ × ℤ, x ∈ oH.dom ↔ x + ((0 : ℤ), (1 : ℤ)) ∈ paperNearLadderAltTile (2 * (k : ℤ) + 2))
    (hvH : ∀ x ∈ oH.dom, oH.val x = paperNearLadderAltValue (2 * (k : ℤ) + 2) (x + ((0 : ℤ), (1 : ℤ))))
    (hpc : ∃ C : ℤ, ∀ z, z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAO w u1 u2 0 →
      oH.val (z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z - placedAltOdd w oP.val oQ.val 0 0 z = C) :
    ∀ z, z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAO w u1 u2 0 →
      oH.val (z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z + (-h0 (texV2 (parentsAt w).odd) + ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2)) = placedAltOdd w oP.val oQ.val (kOddOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 0 z := by
  obtain ⟨hD, hR, hAf, hSh⟩ := altOdd_of w hph
  obtain ⟨C, hC⟩ := hpc
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hrel
  have hB4 := h0_even (texV2 (parentsAt w).odd) (by simp only [texV2]; omega)
  have hV4 := h0_even (texV2 (parentsAt w).even) (by simp only [texV2]; omega)
  have mP := corner_mem _ _ _ _ _ _ hcP
  have vP := corner_raw _ _ _ _ _ hcP
  rw [hdP] at mP
  set p := (parentsAt w).odd with hpdef
  set q := (parentsAt w).even with hqdef
  set A := texV1Odd p with hA
  set B := texV2 p with hBd
  set U := texV1Even q with hU
  set V := texV2 q with hV
  set S := shiftP w with hSdef
  have ez : 0 + (A + B + ((1 : ℤ), (-1 : ℤ)) - ((1 : ℤ), (0 : ℤ))) - (A + B - U) + ((0 : ℤ), (1 : ℤ)) = ((2 * (k : ℤ) + 3), (2 * (k : ℤ) + 1)) := by
    ext <;> simp only [hA, hBd, hU, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, hr1, hr2, hr3, hr4] <;> ring
  have m1 : 0 + (A + B + ((1 : ℤ), (-1 : ℤ)) - ((1 : ℤ), (0 : ℤ))) - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) := by
    rw [Finset.mem_coe, hdH, show 0 + (A + B + ((1 : ℤ), (-1 : ℤ)) - ((1 : ℤ), (0 : ℤ))) - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) = 0 + (A + B + ((1 : ℤ), (-1 : ℤ)) - ((1 : ℤ), (0 : ℤ))) - (A + B - U) from rfl, ez]
    simp only [paperNearLadderAltTile, paperNearLadderAltA, paperNearLadderAltB, paperNearLadderAltC, paperNearLadderAltD, Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq]
    omega
  have m2 : 0 + (A + B + ((1 : ℤ), (-1 : ℤ)) - ((1 : ℤ), (0 : ℤ))) ∈ ClosedPathAlt.dAO w u1 u2 0 := by
    have hdj : ClosedPathAlt.dAO w u1 u2 0 = shiftS (tOddSet u1) (0) := by simp [ClosedPathAlt.dAO, pieceSet, hD]
    rw [hdj]
    exact mem_shift _ _ _ (A + B + ((1 : ℤ), (-1 : ℤ)) - ((1 : ℤ), (0 : ℤ))) mP.2.2.2.2.2.2.2 (by abel)
  have h1 := hC _ m1 m2
  have hval : paperNearLadderAltValue (2 * (k : ℤ) + 2) ((2 * (k : ℤ) + 3), (2 * (k : ℤ) + 1)) = (0) := by
    have hq : (((2 * (k : ℤ) + 1) : ℤ) - (2 * (k : ℤ) + 3)) ^ 2 = 4 * (1) + 0 := by ring
    simp only [paperNearLadderAltValue, Set.indicator_apply, Set.mem_union, paperNearLadderAltA, paperNearLadderAltB, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_setOf_eq, Prod.mk.injEq]
    split_ifs <;> (try simp only [not_or, not_and] at *) <;> omega
  rw [hvH _ m1, ez, hval] at h1
  rw [evalO_lt w _ _ 0 0 _ (0) 0 (A + B + ((1 : ℤ), (-1 : ℤ)) - ((1 : ℤ), (0 : ℤ))) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) (by abel), vP.2.2.2.2.2.2.2] at h1
  intro z hz1 hz2
  have h2 := hC z hz1 hz2
  rw [← placedAltOdd_add]
  simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, dot2, kOddOF, Pi.zero_apply, zero_mul, add_zero, zero_add, hr1, hr2, hr3, hr4] at h1 h2 hB4 hV4 ⊢
  try simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, Prod.fst_neg, Prod.snd_neg, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, dotS, dot2, kOddOF, hr1, hr2, hr3, hr4] at h1
  linarith

theorem base_ao21_1 (k : ℕ) (hk : 1 ≤ k) (w u1 u2 : Word) (hph : phase w = 1)
    (hrel : (parentsAt w).odd.num = ((k : ℤ) + 1) ∧ (parentsAt w).odd.den = ((k : ℤ) + 2) ∧ (parentsAt w).even.num = (2 * (k : ℤ) + 1) ∧
      (parentsAt w).even.den = (2 * (k : ℤ) + 3))
    (oP oQ oH : PartialOdometer) (βP βQ : ℤ)
    (hdP : oP.dom = Standard.oddTile u1) (_hdQ : oQ.dom = Standard.evenTile u2)
    (hcP : TileTranslation.StdCornerValues oP 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (_hcQ : TileTranslation.StdCornerValues oQ 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (hdH : ∀ x : ℤ × ℤ, x ∈ oH.dom ↔ x + ((0 : ℤ), (1 : ℤ)) ∈ paperNearLadderAltTile (2 * (k : ℤ) + 2))
    (hvH : ∀ x ∈ oH.dom, oH.val x = paperNearLadderAltValue (2 * (k : ℤ) + 2) (x + ((0 : ℤ), (1 : ℤ))))
    (hpc : ∃ C : ℤ, ∀ z, z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAO w u1 u2 1 →
      oH.val (z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z - placedAltOdd w oP.val oQ.val 0 1 z = C) :
    ∀ z, z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAO w u1 u2 1 →
      oH.val (z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z + (-h0 (texV2 (parentsAt w).odd) + ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2)) = placedAltOdd w oP.val oQ.val (kOddOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 1 z := by
  obtain ⟨hD, hR, hAf, hSh⟩ := altOdd_of w hph
  obtain ⟨C, hC⟩ := hpc
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hrel
  have hB4 := h0_even (texV2 (parentsAt w).odd) (by simp only [texV2]; omega)
  have hV4 := h0_even (texV2 (parentsAt w).even) (by simp only [texV2]; omega)
  have mP := corner_mem _ _ _ _ _ _ hcP
  have vP := corner_raw _ _ _ _ _ hcP
  rw [hdP] at mP
  set p := (parentsAt w).odd with hpdef
  set q := (parentsAt w).even with hqdef
  set A := texV1Odd p with hA
  set B := texV2 p with hBd
  set U := texV1Even q with hU
  set V := texV2 q with hV
  set S := shiftP w with hSdef
  have ez : S + 0 + (A) - (A + B - U) + ((0 : ℤ), (1 : ℤ)) = ((0), (1)) := by
    rw [hSh]; ext <;> simp only [hA, hBd, hU, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, Prod.fst_neg, Prod.snd_neg, hr1, hr2, hr3, hr4] <;> ring
  have m1 : S + 0 + (A) - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) := by
    rw [Finset.mem_coe, hdH, show S + 0 + (A) - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) = S + 0 + (A) - (A + B - U) from rfl, ez]
    simp only [paperNearLadderAltTile, paperNearLadderAltA, paperNearLadderAltB, paperNearLadderAltC, paperNearLadderAltD, Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq]
    omega
  have m2 : S + 0 + (A) ∈ ClosedPathAlt.dAO w u1 u2 1 := by
    have hdj : ClosedPathAlt.dAO w u1 u2 1 = shiftS (tOddSet u1) (S + 0) := by simp [ClosedPathAlt.dAO, pieceSet, hD]
    rw [hdj]
    exact mem_shift _ _ _ (A) mP.2.2.2.1 (by abel)
  have h1 := hC _ m1 m2
  have hval : paperNearLadderAltValue (2 * (k : ℤ) + 2) ((0), (1)) = (0) := by
    have hq : (((1) : ℤ) - (0)) ^ 2 = 4 * (0) + 1 := by ring
    simp only [paperNearLadderAltValue, Set.indicator_apply, Set.mem_union, paperNearLadderAltA, paperNearLadderAltB, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_setOf_eq, Prod.mk.injEq]
    split_ifs <;> (try simp only [false_and, false_or,
      not_or, not_and] at *) <;> omega
  rw [hvH _ m1, ez, hval] at h1
  rw [evalO_lt w _ _ 0 1 _ (S + 0) (p.num, -p.den) (A) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) (by abel), vP.2.2.2.1] at h1
  intro z hz1 hz2
  have h2 := hC z hz1 hz2
  rw [← placedAltOdd_add]
  simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, dot2, kOddOF, Pi.zero_apply, add_zero, zero_add, hr1, hr2, hr3, hr4] at h1 h2 hB4 hV4 ⊢
  rw [hSh] at h1
  try simp only [hBd, hU, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg, hr1, hr2, hr3, hr4] at h1
  linarith

theorem base_ao21_2 (k : ℕ) (hk : 1 ≤ k) (w u1 u2 : Word) (hph : phase w = 1)
    (hrel : (parentsAt w).odd.num = ((k : ℤ) + 1) ∧ (parentsAt w).odd.den = ((k : ℤ) + 2) ∧ (parentsAt w).even.num = (2 * (k : ℤ) + 1) ∧
      (parentsAt w).even.den = (2 * (k : ℤ) + 3))
    (oP oQ oH : PartialOdometer) (βP βQ : ℤ)
    (hdP : oP.dom = Standard.oddTile u1) (_hdQ : oQ.dom = Standard.evenTile u2)
    (hcP : TileTranslation.StdCornerValues oP 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (_hcQ : TileTranslation.StdCornerValues oQ 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (hdH : ∀ x : ℤ × ℤ, x ∈ oH.dom ↔ x + ((0 : ℤ), (1 : ℤ)) ∈ paperNearLadderAltTile (2 * (k : ℤ) + 2))
    (hvH : ∀ x ∈ oH.dom, oH.val x = paperNearLadderAltValue (2 * (k : ℤ) + 2) (x + ((0 : ℤ), (1 : ℤ))))
    (hpc : ∃ C : ℤ, ∀ z, z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAO w u1 u2 2 →
      oH.val (z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z - placedAltOdd w oP.val oQ.val 0 2 z = C) :
    ∀ z, z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAO w u1 u2 2 →
      oH.val (z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z + (-h0 (texV2 (parentsAt w).odd) + ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2)) = placedAltOdd w oP.val oQ.val (kOddOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 2 z := by
  obtain ⟨hD, hR, hAf, hSh⟩ := altOdd_of w hph
  obtain ⟨C, hC⟩ := hpc
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hrel
  have hB4 := h0_even (texV2 (parentsAt w).odd) (by simp only [texV2]; omega)
  have hV4 := h0_even (texV2 (parentsAt w).even) (by simp only [texV2]; omega)
  have mP := corner_mem _ _ _ _ _ _ hcP
  have vP := corner_raw _ _ _ _ _ hcP
  rw [hdP] at mP
  set p := (parentsAt w).odd with hpdef
  set q := (parentsAt w).even with hqdef
  set A := texV1Odd p with hA
  set B := texV2 p with hBd
  set U := texV1Even q with hU
  set V := texV2 q with hV
  set S := shiftP w with hSdef
  have ez : U + V + ((0 : ℤ × ℤ)) - (A + B - U) + ((0 : ℤ), (1 : ℤ)) = ((2 * (k : ℤ) + 1), (4 * (k : ℤ) + 2)) := by
    ext <;> simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, hr1, hr2, hr3, hr4] <;> ring
  have m1 : U + V + ((0 : ℤ × ℤ)) - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) := by
    rw [Finset.mem_coe, hdH, show U + V + ((0 : ℤ × ℤ)) - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) = U + V + ((0 : ℤ × ℤ)) - (A + B - U) from rfl, ez]
    simp only [paperNearLadderAltTile, paperNearLadderAltA, paperNearLadderAltB, paperNearLadderAltC, paperNearLadderAltD, Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq]
    omega
  have m2 : U + V + ((0 : ℤ × ℤ)) ∈ ClosedPathAlt.dAO w u1 u2 2 := by
    have hdj : ClosedPathAlt.dAO w u1 u2 2 = shiftS (tOddSet u1) (U + V) := by simp [ClosedPathAlt.dAO, pieceSet, hD]
    rw [hdj]
    exact mem_shift _ _ _ ((0 : ℤ × ℤ)) mP.1 (by abel)
  have h1 := hC _ m1 m2
  have hval : paperNearLadderAltValue (2 * (k : ℤ) + 2) ((2 * (k : ℤ) + 1), (4 * (k : ℤ) + 2)) = (-(k : ℤ) ^ 2 - 3 * (k : ℤ)) := by
    have hq : (((4 * (k : ℤ) + 2) : ℤ) - (2 * (k : ℤ) + 1)) ^ 2 = 4 * ((k : ℤ) ^ 2 + (k : ℤ)) + 1 := by ring
    simp only [paperNearLadderAltValue, Set.indicator_apply, Set.mem_union, paperNearLadderAltA, paperNearLadderAltB, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_setOf_eq, Prod.mk.injEq]
    split_ifs <;> (try simp only [not_or, not_and] at *) <;> omega
  rw [hvH _ m1, ez, hval] at h1
  rw [evalO_lt w _ _ 0 2 _ (U + V) (q.num, -q.den) ((0 : ℤ × ℤ)) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) (by abel), vP.1] at h1
  intro z hz1 hz2
  have h2 := hC z hz1 hz2
  rw [← placedAltOdd_add]
  simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, dot2, kOddOF, Pi.zero_apply, add_zero, hr1, hr2, hr3, hr4] at h1 h2 hB4 hV4 ⊢
  try simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, Prod.fst_neg, Prod.snd_neg, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, dotS, dot2, kOddOF, hr1, hr2, hr3, hr4] at h1
  linarith

theorem base_ao21_3 (k : ℕ) (hk : 1 ≤ k) (w u1 u2 : Word) (hph : phase w = 1)
    (hrel : (parentsAt w).odd.num = ((k : ℤ) + 1) ∧ (parentsAt w).odd.den = ((k : ℤ) + 2) ∧ (parentsAt w).even.num = (2 * (k : ℤ) + 1) ∧
      (parentsAt w).even.den = (2 * (k : ℤ) + 3))
    (oP oQ oH : PartialOdometer) (βP βQ : ℤ)
    (hdP : oP.dom = Standard.oddTile u1) (_hdQ : oQ.dom = Standard.evenTile u2)
    (hcP : TileTranslation.StdCornerValues oP 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (_hcQ : TileTranslation.StdCornerValues oQ 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (hdH : ∀ x : ℤ × ℤ, x ∈ oH.dom ↔ x + ((0 : ℤ), (1 : ℤ)) ∈ paperNearLadderAltTile (2 * (k : ℤ) + 2))
    (hvH : ∀ x ∈ oH.dom, oH.val x = paperNearLadderAltValue (2 * (k : ℤ) + 2) (x + ((0 : ℤ), (1 : ℤ))))
    (hpc : ∃ C : ℤ, ∀ z, z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAO w u1 u2 3 →
      oH.val (z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z - placedAltOdd w oP.val oQ.val 0 3 z = C) :
    ∀ z, z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAO w u1 u2 3 →
      oH.val (z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z + (-h0 (texV2 (parentsAt w).odd) + ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2)) = placedAltOdd w oP.val oQ.val (kOddOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 3 z := by
  obtain ⟨hD, hR, hAf, hSh⟩ := altOdd_of w hph
  obtain ⟨C, hC⟩ := hpc
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hrel
  have hB4 := h0_even (texV2 (parentsAt w).odd) (by simp only [texV2]; omega)
  have hV4 := h0_even (texV2 (parentsAt w).even) (by simp only [texV2]; omega)
  have mP := corner_mem _ _ _ _ _ _ hcP
  have vP := corner_raw _ _ _ _ _ hcP
  rw [hdP] at mP
  set p := (parentsAt w).odd with hpdef
  set q := (parentsAt w).even with hqdef
  set A := texV1Odd p with hA
  set B := texV2 p with hBd
  set U := texV1Even q with hU
  set V := texV2 q with hV
  set S := shiftP w with hSdef
  have ez : S + (U + V) + (((1 : ℤ), (0 : ℤ))) - (A + B - U) + ((0 : ℤ), (1 : ℤ)) = ((-2), (4 * (k : ℤ) + 4)) := by
    rw [hSh]; ext <;> simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_neg, Prod.snd_neg, hr1, hr2, hr3, hr4] <;> ring
  have m1 : S + (U + V) + (((1 : ℤ), (0 : ℤ))) - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) := by
    rw [Finset.mem_coe, hdH, show S + (U + V) + (((1 : ℤ), (0 : ℤ))) - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) = S + (U + V) + (((1 : ℤ), (0 : ℤ))) - (A + B - U) from rfl, ez]
    simp only [paperNearLadderAltTile, paperNearLadderAltA, paperNearLadderAltB, paperNearLadderAltC, paperNearLadderAltD, Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq, true_and]
    omega
  have m2 : S + (U + V) + (((1 : ℤ), (0 : ℤ))) ∈ ClosedPathAlt.dAO w u1 u2 3 := by
    have hdj : ClosedPathAlt.dAO w u1 u2 3 = shiftS (tOddSet u1) (S + (U + V)) := by simp [ClosedPathAlt.dAO, pieceSet, hD]
    rw [hdj]
    exact mem_shift _ _ _ (((1 : ℤ), (0 : ℤ))) mP.2.1 (by abel)
  have h1 := hC _ m1 m2
  have hval : paperNearLadderAltValue (2 * (k : ℤ) + 2) ((-2), (4 * (k : ℤ) + 4)) = (-4 * (k : ℤ) ^ 2 - 12 * (k : ℤ) - 7) := by
    have hq : (((4 * (k : ℤ) + 4) : ℤ) - (-2)) ^ 2 = 4 * (4 * (k : ℤ) ^ 2 + 12 * (k : ℤ) + 9) + 0 := by ring
    simp only [paperNearLadderAltValue, Set.indicator_apply, Set.mem_union, paperNearLadderAltA, paperNearLadderAltB, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_setOf_eq, Prod.mk.injEq, true_and]
    split_ifs <;> (try simp only [not_or, not_and] at *) <;> omega
  rw [hvH _ m1, ez, hval] at h1
  rw [evalO_lt w _ _ 0 3 _ (S + (U + V)) ((q.num, -q.den) + (p.num, -p.den)) (((1 : ℤ), (0 : ℤ))) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) (by abel), vP.2.1] at h1
  intro z hz1 hz2
  have h2 := hC z hz1 hz2
  rw [← placedAltOdd_add]
  simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, dot2, kOddOF, Pi.zero_apply, add_zero, hr1, hr2, hr3, hr4] at h1 h2 hB4 hV4 ⊢
  rw [hSh] at h1
  try simp only [hBd, hU, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg, hr1, hr2, hr3, hr4] at h1
  linarith

theorem base_ao21_4 (k : ℕ) (hk : 1 ≤ k) (w u1 u2 : Word) (hph : phase w = 1)
    (hrel : (parentsAt w).odd.num = ((k : ℤ) + 1) ∧ (parentsAt w).odd.den = ((k : ℤ) + 2) ∧ (parentsAt w).even.num = (2 * (k : ℤ) + 1) ∧
      (parentsAt w).even.den = (2 * (k : ℤ) + 3))
    (oP oQ oH : PartialOdometer) (βP βQ : ℤ)
    (_hdP : oP.dom = Standard.oddTile u1) (hdQ : oQ.dom = Standard.evenTile u2)
    (_hcP : TileTranslation.StdCornerValues oP 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (hcQ : TileTranslation.StdCornerValues oQ 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (hdH : ∀ x : ℤ × ℤ, x ∈ oH.dom ↔ x + ((0 : ℤ), (1 : ℤ)) ∈ paperNearLadderAltTile (2 * (k : ℤ) + 2))
    (hvH : ∀ x ∈ oH.dom, oH.val x = paperNearLadderAltValue (2 * (k : ℤ) + 2) (x + ((0 : ℤ), (1 : ℤ))))
    (hpc : ∃ C : ℤ, ∀ z, z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAO w u1 u2 4 →
      oH.val (z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z - placedAltOdd w oP.val oQ.val 0 4 z = C) :
    ∀ z, z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAO w u1 u2 4 →
      oH.val (z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z + (-h0 (texV2 (parentsAt w).odd) + ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2)) = placedAltOdd w oP.val oQ.val (kOddOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 4 z := by
  obtain ⟨hD, hR, hAf, hSh⟩ := altOdd_of w hph
  obtain ⟨C, hC⟩ := hpc
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hrel
  have hB4 := h0_even (texV2 (parentsAt w).odd) (by simp only [texV2]; omega)
  have hV4 := h0_even (texV2 (parentsAt w).even) (by simp only [texV2]; omega)
  have mQ := corner_mem _ _ _ _ _ _ hcQ
  have vQ := corner_raw _ _ _ _ _ hcQ
  rw [hdQ] at mQ
  set p := (parentsAt w).odd with hpdef
  set q := (parentsAt w).even with hqdef
  set A := texV1Odd p with hA
  set B := texV2 p with hBd
  set U := texV1Even q with hU
  set V := texV2 q with hV
  set S := shiftP w with hSdef
  have ez : A + (V + ((1 : ℤ), (0 : ℤ))) - (A + B - U) + ((0 : ℤ), (1 : ℤ)) = ((2 * (k : ℤ) + 3), (4 * (k : ℤ) + 3)) := by
    ext <;> simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, hr1, hr2, hr3, hr4] <;> ring
  have m1 : A + (V + ((1 : ℤ), (0 : ℤ))) - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) := by
    rw [Finset.mem_coe, hdH, show A + (V + ((1 : ℤ), (0 : ℤ))) - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) = A + (V + ((1 : ℤ), (0 : ℤ))) - (A + B - U) from rfl, ez]
    simp only [paperNearLadderAltTile, paperNearLadderAltA, paperNearLadderAltB, paperNearLadderAltC, paperNearLadderAltD, Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq]
    omega
  have m2 : A + (V + ((1 : ℤ), (0 : ℤ))) ∈ ClosedPathAlt.dAO w u1 u2 4 := by
    have hdj : ClosedPathAlt.dAO w u1 u2 4 = shiftS (tEvenSet u2) (A) := by simp [ClosedPathAlt.dAO, pieceSet, hD, hR]
    rw [hdj]
    exact mem_shift _ _ _ (V + ((1 : ℤ), (0 : ℤ))) mQ.2.2.2.2.1 (by abel)
  have h1 := hC _ m1 m2
  have hval : paperNearLadderAltValue (2 * (k : ℤ) + 2) ((2 * (k : ℤ) + 3), (4 * (k : ℤ) + 3)) = (-(k : ℤ) ^ 2 - 2 * (k : ℤ) - 1) := by
    have hq : (((4 * (k : ℤ) + 3) : ℤ) - (2 * (k : ℤ) + 3)) ^ 2 = 4 * ((k : ℤ) ^ 2) + 0 := by ring
    simp only [paperNearLadderAltValue, Set.indicator_apply, Set.mem_union, paperNearLadderAltA, paperNearLadderAltB, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_setOf_eq, Prod.mk.injEq]
    split_ifs <;> (try simp only [not_or, not_and] at *) <;> omega
  rw [hvH _ m1, ez, hval] at h1
  rw [evalO_ge w _ _ 0 4 _ (A) 0 (V + ((1 : ℤ), (0 : ℤ))) (by norm_num) (by rw [hR]; rfl) (by rw [hAf]; rfl) (by abel), vQ.2.2.2.2.1] at h1
  intro z hz1 hz2
  have h2 := hC z hz1 hz2
  rw [← placedAltOdd_add]
  simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero, dot2, kOddOF, Pi.zero_apply, zero_mul, add_zero, hr1, hr2, hr3, hr4] at h1 h2 hB4 hV4 ⊢
  try simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, Prod.fst_neg, Prod.snd_neg, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, dotS, dot2, kOddOF, hr1, hr2, hr3, hr4] at h1
  linarith

theorem base_ao21_5 (k : ℕ) (hk : 1 ≤ k) (w u1 u2 : Word) (hph : phase w = 1)
    (hrel : (parentsAt w).odd.num = ((k : ℤ) + 1) ∧ (parentsAt w).odd.den = ((k : ℤ) + 2) ∧ (parentsAt w).even.num = (2 * (k : ℤ) + 1) ∧
      (parentsAt w).even.den = (2 * (k : ℤ) + 3))
    (oP oQ oH : PartialOdometer) (βP βQ : ℤ)
    (_hdP : oP.dom = Standard.oddTile u1) (hdQ : oQ.dom = Standard.evenTile u2)
    (_hcP : TileTranslation.StdCornerValues oP 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (hcQ : TileTranslation.StdCornerValues oQ 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (hdH : ∀ x : ℤ × ℤ, x ∈ oH.dom ↔ x + ((0 : ℤ), (1 : ℤ)) ∈ paperNearLadderAltTile (2 * (k : ℤ) + 2))
    (hvH : ∀ x ∈ oH.dom, oH.val x = paperNearLadderAltValue (2 * (k : ℤ) + 2) (x + ((0 : ℤ), (1 : ℤ))))
    (hpc : ∃ C : ℤ, ∀ z, z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAO w u1 u2 5 →
      oH.val (z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z - placedAltOdd w oP.val oQ.val 0 5 z = C) :
    ∀ z, z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAO w u1 u2 5 →
      oH.val (z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z + (-h0 (texV2 (parentsAt w).odd) + ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2)) = placedAltOdd w oP.val oQ.val (kOddOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 5 z := by
  obtain ⟨hD, hR, hAf, hSh⟩ := altOdd_of w hph
  obtain ⟨C, hC⟩ := hpc
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hrel
  have hB4 := h0_even (texV2 (parentsAt w).odd) (by simp only [texV2]; omega)
  have hV4 := h0_even (texV2 (parentsAt w).even) (by simp only [texV2]; omega)
  have mQ := corner_mem _ _ _ _ _ _ hcQ
  have vQ := corner_raw _ _ _ _ _ hcQ
  rw [hdQ] at mQ
  set p := (parentsAt w).odd with hpdef
  set q := (parentsAt w).even with hqdef
  set A := texV1Odd p with hA
  set B := texV2 p with hBd
  set U := texV1Even q with hU
  set V := texV2 q with hV
  set S := shiftP w with hSdef
  have ez : B + B - U + (U - ((0 : ℤ), (1 : ℤ))) - (A + B - U) + ((0 : ℤ), (1 : ℤ)) = ((-2), (2 * (k : ℤ) + 2)) := by
    ext <;> simp only [hA, hBd, hU, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, hr1, hr2, hr3, hr4] <;> ring
  have m1 : B + B - U + (U - ((0 : ℤ), (1 : ℤ))) - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) := by
    rw [Finset.mem_coe, hdH, show B + B - U + (U - ((0 : ℤ), (1 : ℤ))) - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) = B + B - U + (U - ((0 : ℤ), (1 : ℤ))) - (A + B - U) from rfl, ez]
    simp only [paperNearLadderAltTile, paperNearLadderAltA, paperNearLadderAltB, paperNearLadderAltC, paperNearLadderAltD, Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq, true_and]
    omega
  have m2 : B + B - U + (U - ((0 : ℤ), (1 : ℤ))) ∈ ClosedPathAlt.dAO w u1 u2 5 := by
    have hdj : ClosedPathAlt.dAO w u1 u2 5 = shiftS (tEvenSet u2) (B + B - U) := by simp [ClosedPathAlt.dAO, pieceSet, hD, hR]
    rw [hdj]
    exact mem_shift _ _ _ (U - ((0 : ℤ), (1 : ℤ))) mQ.2.2.1 (by abel)
  have h1 := hC _ m1 m2
  have hval : paperNearLadderAltValue (2 * (k : ℤ) + 2) ((-2), (2 * (k : ℤ) + 2)) = (-(k : ℤ) ^ 2 - 4 * (k : ℤ) - 2) := by
    have hq : (((2 * (k : ℤ) + 2) : ℤ) - (-2)) ^ 2 = 4 * ((k : ℤ) ^ 2 + 4 * (k : ℤ) + 4) + 0 := by ring
    simp only [paperNearLadderAltValue, Set.indicator_apply, Set.mem_union, paperNearLadderAltA, paperNearLadderAltB, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_setOf_eq, Prod.mk.injEq, true_and]
    split_ifs <;> (try simp only [not_or, not_and] at *) <;> omega
  rw [hvH _ m1, ez, hval] at h1
  rw [evalO_ge w _ _ 0 5 _ (B + B - U) ((p.num, -p.den) + (p.num, -p.den)) (U - ((0 : ℤ), (1 : ℤ))) (by norm_num) (by rw [hR]; rfl) (by rw [hAf]; rfl) (by abel), vQ.2.2.1] at h1
  intro z hz1 hz2
  have h2 := hC z hz1 hz2
  rw [← placedAltOdd_add]
  simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, dot2, kOddOF, Pi.zero_apply, add_zero, hr1, hr2, hr3, hr4] at h1 h2 hB4 hV4 ⊢
  try simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, Prod.fst_neg, Prod.snd_neg, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, dotS, dot2, kOddOF, hr1, hr2, hr3, hr4] at h1
  linarith

theorem base_ao23_0 (k : ℕ) (hk : 1 ≤ k) (w u1 u2 : Word) (hph : phase w ≠ 1)
    (hrel : (parentsAt w).odd.num = ((k : ℤ)) ∧ (parentsAt w).odd.den = ((k : ℤ) + 1) ∧ (parentsAt w).even.num = (2 * (k : ℤ) + 1) ∧
      (parentsAt w).even.den = (2 * (k : ℤ) + 3))
    (oP oQ oH : PartialOdometer) (βP βQ : ℤ)
    (hdP : oP.dom = Standard.oddTile u1) (_hdQ : oQ.dom = Standard.evenTile u2)
    (hcP : TileTranslation.StdCornerValues oP 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (_hcQ : TileTranslation.StdCornerValues oQ 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (hdH : ∀ x : ℤ × ℤ, x ∈ oH.dom ↔ x + ((0 : ℤ), (1 : ℤ)) ∈ paperNearLadderAltTile (2 * (k : ℤ) + 2))
    (hvH : ∀ x ∈ oH.dom, oH.val x = paperNearLadderAltValue (2 * (k : ℤ) + 2) (x + ((0 : ℤ), (1 : ℤ))))
    (hpc : ∃ C : ℤ, ∀ z, z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAO w u1 u2 0 →
      oH.val (z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z - placedAltOdd w oP.val oQ.val 0 0 z = C) :
    ∀ z, z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAO w u1 u2 0 →
      oH.val (z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z + (-h0 (texV2 (parentsAt w).odd) + ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num + (parentsAt w).odd.den * (parentsAt w).even.num - (parentsAt w).even.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2)) = placedAltOdd w oP.val oQ.val (kOddEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 0 z := by
  obtain ⟨hD, hR, hAf, hSh⟩ := altOdd_ef w hph
  obtain ⟨C, hC⟩ := hpc
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hrel
  have hB4 := h0_even (texV2 (parentsAt w).odd) (by simp only [texV2]; omega)
  have hV4 := h0_even (texV2 (parentsAt w).even) (by simp only [texV2]; omega)
  have mP := corner_mem _ _ _ _ _ _ hcP
  have vP := corner_raw _ _ _ _ _ hcP
  rw [hdP] at mP
  set p := (parentsAt w).odd with hpdef
  set q := (parentsAt w).even with hqdef
  set A := texV1Odd p with hA
  set B := texV2 p with hBd
  set U := texV1Even q with hU
  set V := texV2 q with hV
  set S := shiftP w with hSdef
  have ez : U + (B + ((1 : ℤ), (0 : ℤ))) - (B + U) + ((0 : ℤ), (1 : ℤ)) = ((1), (1)) := by
    ext <;> simp only [hBd, hU, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, hr1, hr2, hr3, hr4] <;> ring
  have m1 : U + (B + ((1 : ℤ), (0 : ℤ))) - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) := by
    rw [Finset.mem_coe, hdH, show U + (B + ((1 : ℤ), (0 : ℤ))) - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) = U + (B + ((1 : ℤ), (0 : ℤ))) - (B + U) from rfl, ez]
    simp only [paperNearLadderAltTile, paperNearLadderAltA, paperNearLadderAltB, paperNearLadderAltC, paperNearLadderAltD, Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq]
    omega
  have m2 : U + (B + ((1 : ℤ), (0 : ℤ))) ∈ ClosedPathAlt.dAO w u1 u2 0 := by
    have hdj : ClosedPathAlt.dAO w u1 u2 0 = shiftS (tOddSet u1) (U) := by simp [ClosedPathAlt.dAO, pieceSet, hD]
    rw [hdj]
    exact mem_shift _ _ _ (B + ((1 : ℤ), (0 : ℤ))) mP.2.2.2.2.1 (by abel)
  have h1 := hC _ m1 m2
  have hval : paperNearLadderAltValue (2 * (k : ℤ) + 2) ((1), (1)) = (0) := by
    have hq : (((1) : ℤ) - (1)) ^ 2 = 4 * (0) + 0 := by ring
    simp only [paperNearLadderAltValue, Set.indicator_apply, Set.mem_union, paperNearLadderAltA, paperNearLadderAltB, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_setOf_eq, Prod.mk.injEq]
    split_ifs <;> (try simp only [false_and, false_or,
      not_or, not_and] at *) <;> omega
  rw [hvH _ m1, ez, hval] at h1
  rw [evalO_lt w _ _ 0 0 _ (U) 0 (B + ((1 : ℤ), (0 : ℤ))) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) (by abel), vP.2.2.2.2.1] at h1
  intro z hz1 hz2
  have h2 := hC z hz1 hz2
  rw [← placedAltOdd_add]
  simp only [hBd, hU, hV, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero, dot2, kOddEF, Pi.zero_apply, zero_mul, add_zero, zero_add, hr1, hr2, hr3, hr4] at h1 h2 hB4 hV4 ⊢
  try simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, Prod.fst_neg, Prod.snd_neg, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, dotS, dot2, kOddEF, hr1, hr2, hr3, hr4] at h1
  linarith

theorem base_ao23_1 (k : ℕ) (hk : 1 ≤ k) (w u1 u2 : Word) (hph : phase w ≠ 1)
    (hrel : (parentsAt w).odd.num = ((k : ℤ)) ∧ (parentsAt w).odd.den = ((k : ℤ) + 1) ∧ (parentsAt w).even.num = (2 * (k : ℤ) + 1) ∧
      (parentsAt w).even.den = (2 * (k : ℤ) + 3))
    (oP oQ oH : PartialOdometer) (βP βQ : ℤ)
    (hdP : oP.dom = Standard.oddTile u1) (_hdQ : oQ.dom = Standard.evenTile u2)
    (hcP : TileTranslation.StdCornerValues oP 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (_hcQ : TileTranslation.StdCornerValues oQ 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (hdH : ∀ x : ℤ × ℤ, x ∈ oH.dom ↔ x + ((0 : ℤ), (1 : ℤ)) ∈ paperNearLadderAltTile (2 * (k : ℤ) + 2))
    (hvH : ∀ x ∈ oH.dom, oH.val x = paperNearLadderAltValue (2 * (k : ℤ) + 2) (x + ((0 : ℤ), (1 : ℤ))))
    (hpc : ∃ C : ℤ, ∀ z, z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAO w u1 u2 1 →
      oH.val (z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z - placedAltOdd w oP.val oQ.val 0 1 z = C) :
    ∀ z, z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAO w u1 u2 1 →
      oH.val (z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z + (-h0 (texV2 (parentsAt w).odd) + ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num + (parentsAt w).odd.den * (parentsAt w).even.num - (parentsAt w).even.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2)) = placedAltOdd w oP.val oQ.val (kOddEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 1 z := by
  obtain ⟨hD, hR, hAf, hSh⟩ := altOdd_ef w hph
  obtain ⟨C, hC⟩ := hpc
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hrel
  have hB4 := h0_even (texV2 (parentsAt w).odd) (by simp only [texV2]; omega)
  have hV4 := h0_even (texV2 (parentsAt w).even) (by simp only [texV2]; omega)
  have mP := corner_mem _ _ _ _ _ _ hcP
  have vP := corner_raw _ _ _ _ _ hcP
  rw [hdP] at mP
  set p := (parentsAt w).odd with hpdef
  set q := (parentsAt w).even with hqdef
  set A := texV1Odd p with hA
  set B := texV2 p with hBd
  set U := texV1Even q with hU
  set V := texV2 q with hV
  set S := shiftP w with hSdef
  have ez : S + U + ((0 : ℤ × ℤ)) - (B + U) + ((0 : ℤ), (1 : ℤ)) = ((2 * (k : ℤ) + 3), (2 * (k : ℤ) + 2)) := by
    rw [hSh]; ext <;> simp only [hBd, hU, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, hr1, hr2, hr3, hr4] <;> ring
  have m1 : S + U + ((0 : ℤ × ℤ)) - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) := by
    rw [Finset.mem_coe, hdH, show S + U + ((0 : ℤ × ℤ)) - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) = S + U + ((0 : ℤ × ℤ)) - (B + U) from rfl, ez]
    simp only [paperNearLadderAltTile, paperNearLadderAltA, paperNearLadderAltB, paperNearLadderAltC, paperNearLadderAltD, Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq]
    omega
  have m2 : S + U + ((0 : ℤ × ℤ)) ∈ ClosedPathAlt.dAO w u1 u2 1 := by
    have hdj : ClosedPathAlt.dAO w u1 u2 1 = shiftS (tOddSet u1) (S + U) := by simp [ClosedPathAlt.dAO, pieceSet, hD]
    rw [hdj]
    exact mem_shift _ _ _ ((0 : ℤ × ℤ)) mP.1 (by abel)
  have h1 := hC _ m1 m2
  have hval : paperNearLadderAltValue (2 * (k : ℤ) + 2) ((2 * (k : ℤ) + 3), (2 * (k : ℤ) + 2)) = (0) := by
    have hq : (((2 * (k : ℤ) + 2) : ℤ) - (2 * (k : ℤ) + 3)) ^ 2 = 4 * (0) + 1 := by ring
    simp only [paperNearLadderAltValue, Set.indicator_apply, Set.mem_union, paperNearLadderAltA, paperNearLadderAltB, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_setOf_eq, Prod.mk.injEq]
    split_ifs <;> (try simp only [not_or, not_and] at *) <;> omega
  rw [hvH _ m1, ez, hval] at h1
  rw [evalO_lt w _ _ 0 1 _ (S + U) (p.num, -p.den) ((0 : ℤ × ℤ)) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) (by abel), vP.1] at h1
  intro z hz1 hz2
  have h2 := hC z hz1 hz2
  rw [← placedAltOdd_add]
  simp only [hBd, hU, hV, texV1Even, texV2, Prod.fst_add, Prod.snd_add, dot2, kOddEF, Pi.zero_apply, add_zero, zero_add, hr1, hr2, hr3, hr4] at h1 h2 hB4 hV4 ⊢
  rw [hSh] at h1
  try simp only [hBd, hU, texV1Even, texV2, Prod.fst_add, Prod.snd_add, hr1, hr2, hr3, hr4] at h1
  linarith

theorem base_ao23_2 (k : ℕ) (hk : 1 ≤ k) (w u1 u2 : Word) (hph : phase w ≠ 1)
    (hrel : (parentsAt w).odd.num = ((k : ℤ)) ∧ (parentsAt w).odd.den = ((k : ℤ) + 1) ∧ (parentsAt w).even.num = (2 * (k : ℤ) + 1) ∧
      (parentsAt w).even.den = (2 * (k : ℤ) + 3))
    (oP oQ oH : PartialOdometer) (βP βQ : ℤ)
    (hdP : oP.dom = Standard.oddTile u1) (_hdQ : oQ.dom = Standard.evenTile u2)
    (hcP : TileTranslation.StdCornerValues oP 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (_hcQ : TileTranslation.StdCornerValues oQ 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (hdH : ∀ x : ℤ × ℤ, x ∈ oH.dom ↔ x + ((0 : ℤ), (1 : ℤ)) ∈ paperNearLadderAltTile (2 * (k : ℤ) + 2))
    (hvH : ∀ x ∈ oH.dom, oH.val x = paperNearLadderAltValue (2 * (k : ℤ) + 2) (x + ((0 : ℤ), (1 : ℤ))))
    (hpc : ∃ C : ℤ, ∀ z, z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAO w u1 u2 2 →
      oH.val (z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z - placedAltOdd w oP.val oQ.val 0 2 z = C) :
    ∀ z, z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAO w u1 u2 2 →
      oH.val (z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z + (-h0 (texV2 (parentsAt w).odd) + ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num + (parentsAt w).odd.den * (parentsAt w).even.num - (parentsAt w).even.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2)) = placedAltOdd w oP.val oQ.val (kOddEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 2 z := by
  obtain ⟨hD, hR, hAf, hSh⟩ := altOdd_ef w hph
  obtain ⟨C, hC⟩ := hpc
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hrel
  have hB4 := h0_even (texV2 (parentsAt w).odd) (by simp only [texV2]; omega)
  have hV4 := h0_even (texV2 (parentsAt w).even) (by simp only [texV2]; omega)
  have mP := corner_mem _ _ _ _ _ _ hcP
  have vP := corner_raw _ _ _ _ _ hcP
  rw [hdP] at mP
  set p := (parentsAt w).odd with hpdef
  set q := (parentsAt w).even with hqdef
  set A := texV1Odd p with hA
  set B := texV2 p with hBd
  set U := texV1Even q with hU
  set V := texV2 q with hV
  set S := shiftP w with hSdef
  have ez : V + (A - ((0 : ℤ), (1 : ℤ))) - (B + U) + ((0 : ℤ), (1 : ℤ)) = ((-2), (2 * (k : ℤ) + 2)) := by
    ext <;> simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, hr1, hr2, hr3, hr4] <;> ring
  have m1 : V + (A - ((0 : ℤ), (1 : ℤ))) - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) := by
    rw [Finset.mem_coe, hdH, show V + (A - ((0 : ℤ), (1 : ℤ))) - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) = V + (A - ((0 : ℤ), (1 : ℤ))) - (B + U) from rfl, ez]
    simp only [paperNearLadderAltTile, paperNearLadderAltA, paperNearLadderAltB, paperNearLadderAltC, paperNearLadderAltD, Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq, true_and]
    omega
  have m2 : V + (A - ((0 : ℤ), (1 : ℤ))) ∈ ClosedPathAlt.dAO w u1 u2 2 := by
    have hdj : ClosedPathAlt.dAO w u1 u2 2 = shiftS (tOddSet u1) (V) := by simp [ClosedPathAlt.dAO, pieceSet, hD]
    rw [hdj]
    exact mem_shift _ _ _ (A - ((0 : ℤ), (1 : ℤ))) mP.2.2.1 (by abel)
  have h1 := hC _ m1 m2
  have hval : paperNearLadderAltValue (2 * (k : ℤ) + 2) ((-2), (2 * (k : ℤ) + 2)) = (-(k : ℤ) ^ 2 - 4 * (k : ℤ) - 2) := by
    have hq : (((2 * (k : ℤ) + 2) : ℤ) - (-2)) ^ 2 = 4 * ((k : ℤ) ^ 2 + 4 * (k : ℤ) + 4) + 0 := by ring
    simp only [paperNearLadderAltValue, Set.indicator_apply, Set.mem_union, paperNearLadderAltA, paperNearLadderAltB, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_setOf_eq, Prod.mk.injEq, true_and]
    split_ifs <;> (try simp only [not_or, not_and] at *) <;> omega
  rw [hvH _ m1, ez, hval] at h1
  rw [evalO_lt w _ _ 0 2 _ (V) (q.num, -q.den) (A - ((0 : ℤ), (1 : ℤ))) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) (by abel), vP.2.2.1] at h1
  intro z hz1 hz2
  have h2 := hC z hz1 hz2
  rw [← placedAltOdd_add]
  simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, dot2, kOddEF, Pi.zero_apply, add_zero, hr1, hr2, hr3, hr4] at h1 h2 hB4 hV4 ⊢
  try simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, Prod.fst_neg, Prod.snd_neg, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, dotS, dot2, kOddEF, hr1, hr2, hr3, hr4] at h1
  linarith

theorem base_ao23_3 (k : ℕ) (hk : 1 ≤ k) (w u1 u2 : Word) (hph : phase w ≠ 1)
    (hrel : (parentsAt w).odd.num = ((k : ℤ)) ∧ (parentsAt w).odd.den = ((k : ℤ) + 1) ∧ (parentsAt w).even.num = (2 * (k : ℤ) + 1) ∧
      (parentsAt w).even.den = (2 * (k : ℤ) + 3))
    (oP oQ oH : PartialOdometer) (βP βQ : ℤ)
    (hdP : oP.dom = Standard.oddTile u1) (_hdQ : oQ.dom = Standard.evenTile u2)
    (hcP : TileTranslation.StdCornerValues oP 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (_hcQ : TileTranslation.StdCornerValues oQ 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (hdH : ∀ x : ℤ × ℤ, x ∈ oH.dom ↔ x + ((0 : ℤ), (1 : ℤ)) ∈ paperNearLadderAltTile (2 * (k : ℤ) + 2))
    (hvH : ∀ x ∈ oH.dom, oH.val x = paperNearLadderAltValue (2 * (k : ℤ) + 2) (x + ((0 : ℤ), (1 : ℤ))))
    (hpc : ∃ C : ℤ, ∀ z, z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAO w u1 u2 3 →
      oH.val (z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z - placedAltOdd w oP.val oQ.val 0 3 z = C) :
    ∀ z, z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAO w u1 u2 3 →
      oH.val (z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z + (-h0 (texV2 (parentsAt w).odd) + ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num + (parentsAt w).odd.den * (parentsAt w).even.num - (parentsAt w).even.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2)) = placedAltOdd w oP.val oQ.val (kOddEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 3 z := by
  obtain ⟨hD, hR, hAf, hSh⟩ := altOdd_ef w hph
  obtain ⟨C, hC⟩ := hpc
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hrel
  have hB4 := h0_even (texV2 (parentsAt w).odd) (by simp only [texV2]; omega)
  have hV4 := h0_even (texV2 (parentsAt w).even) (by simp only [texV2]; omega)
  have mP := corner_mem _ _ _ _ _ _ hcP
  have vP := corner_raw _ _ _ _ _ hcP
  rw [hdP] at mP
  set p := (parentsAt w).odd with hpdef
  set q := (parentsAt w).even with hqdef
  set A := texV1Odd p with hA
  set B := texV2 p with hBd
  set U := texV1Even q with hU
  set V := texV2 q with hV
  set S := shiftP w with hSdef
  have ez : S + V + (A - ((0 : ℤ), (1 : ℤ))) - (B + U) + ((0 : ℤ), (1 : ℤ)) = ((2 * (k : ℤ)), (6 * (k : ℤ) + 4)) := by
    rw [hSh]; ext <;> simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, hr1, hr2, hr3, hr4] <;> ring
  have m1 : S + V + (A - ((0 : ℤ), (1 : ℤ))) - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) := by
    rw [Finset.mem_coe, hdH, show S + V + (A - ((0 : ℤ), (1 : ℤ))) - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) = S + V + (A - ((0 : ℤ), (1 : ℤ))) - (B + U) from rfl, ez]
    simp only [paperNearLadderAltTile, paperNearLadderAltA, paperNearLadderAltB, paperNearLadderAltC, paperNearLadderAltD, Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq]
    omega
  have m2 : S + V + (A - ((0 : ℤ), (1 : ℤ))) ∈ ClosedPathAlt.dAO w u1 u2 3 := by
    have hdj : ClosedPathAlt.dAO w u1 u2 3 = shiftS (tOddSet u1) (S + V) := by simp [ClosedPathAlt.dAO, pieceSet, hD]
    rw [hdj]
    exact mem_shift _ _ _ (A - ((0 : ℤ), (1 : ℤ))) mP.2.2.1 (by abel)
  have h1 := hC _ m1 m2
  have hval : paperNearLadderAltValue (2 * (k : ℤ) + 2) ((2 * (k : ℤ)), (6 * (k : ℤ) + 4)) = (-4 * (k : ℤ) ^ 2 - 12 * (k : ℤ) - 5) := by
    have hq : (((6 * (k : ℤ) + 4) : ℤ) - (2 * (k : ℤ))) ^ 2 = 4 * (4 * (k : ℤ) ^ 2 + 8 * (k : ℤ) + 4) + 0 := by ring
    simp only [paperNearLadderAltValue, Set.indicator_apply, Set.mem_union, paperNearLadderAltA, paperNearLadderAltB, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_setOf_eq, Prod.mk.injEq]
    split_ifs <;> (try simp only [not_or, not_and] at *) <;> omega
  rw [hvH _ m1, ez, hval] at h1
  rw [evalO_lt w _ _ 0 3 _ (S + V) ((q.num, -q.den) + (p.num, -p.den)) (A - ((0 : ℤ), (1 : ℤ))) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) (by abel), vP.2.2.1] at h1
  intro z hz1 hz2
  have h2 := hC z hz1 hz2
  rw [← placedAltOdd_add]
  simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, dot2, kOddEF, Pi.zero_apply, add_zero, hr1, hr2, hr3, hr4] at h1 h2 hB4 hV4 ⊢
  rw [hSh] at h1
  try simp only [hBd, hU, texV1Even, texV2, Prod.fst_add, Prod.snd_add, hr1, hr2, hr3, hr4] at h1
  linarith

theorem base_ao23_4 (k : ℕ) (hk : 1 ≤ k) (w u1 u2 : Word) (hph : phase w ≠ 1)
    (hrel : (parentsAt w).odd.num = ((k : ℤ)) ∧ (parentsAt w).odd.den = ((k : ℤ) + 1) ∧ (parentsAt w).even.num = (2 * (k : ℤ) + 1) ∧
      (parentsAt w).even.den = (2 * (k : ℤ) + 3))
    (oP oQ oH : PartialOdometer) (βP βQ : ℤ)
    (_hdP : oP.dom = Standard.oddTile u1) (hdQ : oQ.dom = Standard.evenTile u2)
    (_hcP : TileTranslation.StdCornerValues oP 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (hcQ : TileTranslation.StdCornerValues oQ 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (hdH : ∀ x : ℤ × ℤ, x ∈ oH.dom ↔ x + ((0 : ℤ), (1 : ℤ)) ∈ paperNearLadderAltTile (2 * (k : ℤ) + 2))
    (hvH : ∀ x ∈ oH.dom, oH.val x = paperNearLadderAltValue (2 * (k : ℤ) + 2) (x + ((0 : ℤ), (1 : ℤ))))
    (hpc : ∃ C : ℤ, ∀ z, z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAO w u1 u2 4 →
      oH.val (z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z - placedAltOdd w oP.val oQ.val 0 4 z = C) :
    ∀ z, z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAO w u1 u2 4 →
      oH.val (z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z + (-h0 (texV2 (parentsAt w).odd) + ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num + (parentsAt w).odd.den * (parentsAt w).even.num - (parentsAt w).even.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2)) = placedAltOdd w oP.val oQ.val (kOddEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 4 z := by
  obtain ⟨hD, hR, hAf, hSh⟩ := altOdd_ef w hph
  obtain ⟨C, hC⟩ := hpc
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hrel
  have hB4 := h0_even (texV2 (parentsAt w).odd) (by simp only [texV2]; omega)
  have hV4 := h0_even (texV2 (parentsAt w).even) (by simp only [texV2]; omega)
  have mQ := corner_mem _ _ _ _ _ _ hcQ
  have vQ := corner_raw _ _ _ _ _ hcQ
  rw [hdQ] at mQ
  set p := (parentsAt w).odd with hpdef
  set q := (parentsAt w).even with hqdef
  set A := texV1Odd p with hA
  set B := texV2 p with hBd
  set U := texV1Even q with hU
  set V := texV2 q with hV
  set S := shiftP w with hSdef
  have ez : 0 + (U + V + ((1 : ℤ), (-1 : ℤ))) - (B + U) + ((0 : ℤ), (1 : ℤ)) = ((0), (2 * (k : ℤ) + 3)) := by
    ext <;> simp only [hBd, hU, hV, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, hr1, hr2, hr3, hr4] <;> ring
  have m1 : 0 + (U + V + ((1 : ℤ), (-1 : ℤ))) - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) := by
    rw [Finset.mem_coe, hdH, show 0 + (U + V + ((1 : ℤ), (-1 : ℤ))) - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) = 0 + (U + V + ((1 : ℤ), (-1 : ℤ))) - (B + U) from rfl, ez]
    simp only [paperNearLadderAltTile, paperNearLadderAltA, paperNearLadderAltB, paperNearLadderAltC, paperNearLadderAltD, Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq]
    omega
  have m2 : 0 + (U + V + ((1 : ℤ), (-1 : ℤ))) ∈ ClosedPathAlt.dAO w u1 u2 4 := by
    have hdj : ClosedPathAlt.dAO w u1 u2 4 = shiftS (tEvenSet u2) (0) := by simp [ClosedPathAlt.dAO, pieceSet, hD, hR]
    rw [hdj]
    exact mem_shift _ _ _ (U + V + ((1 : ℤ), (-1 : ℤ))) mQ.2.2.2.2.2.2.1 (by abel)
  have h1 := hC _ m1 m2
  have hval : paperNearLadderAltValue (2 * (k : ℤ) + 2) ((0), (2 * (k : ℤ) + 3)) = (-(k : ℤ) ^ 2 - 3 * (k : ℤ) - 2) := by
    have hq : (((2 * (k : ℤ) + 3) : ℤ) - (0)) ^ 2 = 4 * ((k : ℤ) ^ 2 + 3 * (k : ℤ) + 2) + 1 := by ring
    simp only [paperNearLadderAltValue, Set.indicator_apply, Set.mem_union, paperNearLadderAltA, paperNearLadderAltB, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_setOf_eq, Prod.mk.injEq]
    split_ifs <;> (try simp only [false_and, false_or,
      not_or, not_and] at *) <;> omega
  rw [hvH _ m1, ez, hval] at h1
  rw [evalO_ge w _ _ 0 4 _ (0) 0 (U + V + ((1 : ℤ), (-1 : ℤ))) (by norm_num) (by rw [hR]; rfl) (by rw [hAf]; rfl) (by abel), vQ.2.2.2.2.2.2.1] at h1
  intro z hz1 hz2
  have h2 := hC z hz1 hz2
  rw [← placedAltOdd_add]
  simp only [hBd, hU, hV, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero, dot2, kOddEF, Pi.zero_apply, zero_mul, add_zero, zero_add, hr1, hr2, hr3, hr4] at h1 h2 hB4 hV4 ⊢
  try simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, Prod.fst_neg, Prod.snd_neg, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, dotS, dot2, kOddEF, hr1, hr2, hr3, hr4] at h1
  linarith

theorem base_ao23_5 (k : ℕ) (hk : 1 ≤ k) (w u1 u2 : Word) (hph : phase w ≠ 1)
    (hrel : (parentsAt w).odd.num = ((k : ℤ)) ∧ (parentsAt w).odd.den = ((k : ℤ) + 1) ∧ (parentsAt w).even.num = (2 * (k : ℤ) + 1) ∧
      (parentsAt w).even.den = (2 * (k : ℤ) + 3))
    (oP oQ oH : PartialOdometer) (βP βQ : ℤ)
    (_hdP : oP.dom = Standard.oddTile u1) (hdQ : oQ.dom = Standard.evenTile u2)
    (_hcP : TileTranslation.StdCornerValues oP 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (hcQ : TileTranslation.StdCornerValues oQ 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (hdH : ∀ x : ℤ × ℤ, x ∈ oH.dom ↔ x + ((0 : ℤ), (1 : ℤ)) ∈ paperNearLadderAltTile (2 * (k : ℤ) + 2))
    (hvH : ∀ x ∈ oH.dom, oH.val x = paperNearLadderAltValue (2 * (k : ℤ) + 2) (x + ((0 : ℤ), (1 : ℤ))))
    (hpc : ∃ C : ℤ, ∀ z, z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAO w u1 u2 5 →
      oH.val (z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z - placedAltOdd w oP.val oQ.val 0 5 z = C) :
    ∀ z, z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAO w u1 u2 5 →
      oH.val (z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z + (-h0 (texV2 (parentsAt w).odd) + ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num + (parentsAt w).odd.den * (parentsAt w).even.num - (parentsAt w).even.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2)) = placedAltOdd w oP.val oQ.val (kOddEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 5 z := by
  obtain ⟨hD, hR, hAf, hSh⟩ := altOdd_ef w hph
  obtain ⟨C, hC⟩ := hpc
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hrel
  have hB4 := h0_even (texV2 (parentsAt w).odd) (by simp only [texV2]; omega)
  have hV4 := h0_even (texV2 (parentsAt w).even) (by simp only [texV2]; omega)
  have mQ := corner_mem _ _ _ _ _ _ hcQ
  have vQ := corner_raw _ _ _ _ _ hcQ
  rw [hdQ] at mQ
  set p := (parentsAt w).odd with hpdef
  set q := (parentsAt w).even with hqdef
  set A := texV1Odd p with hA
  set B := texV2 p with hBd
  set U := texV1Even q with hU
  set V := texV2 q with hV
  set S := shiftP w with hSdef
  have ez : A + B + B + U + ((0 : ℤ × ℤ)) - (B + U) + ((0 : ℤ), (1 : ℤ)) = ((2 * (k : ℤ) + 1), (4 * (k : ℤ) + 2)) := by
    ext <;> simp only [hA, hBd, hU, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, hr1, hr2, hr3, hr4] <;> ring
  have m1 : A + B + B + U + ((0 : ℤ × ℤ)) - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) := by
    rw [Finset.mem_coe, hdH, show A + B + B + U + ((0 : ℤ × ℤ)) - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) = A + B + B + U + ((0 : ℤ × ℤ)) - (B + U) from rfl, ez]
    simp only [paperNearLadderAltTile, paperNearLadderAltA, paperNearLadderAltB, paperNearLadderAltC, paperNearLadderAltD, Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq]
    omega
  have m2 : A + B + B + U + ((0 : ℤ × ℤ)) ∈ ClosedPathAlt.dAO w u1 u2 5 := by
    have hdj : ClosedPathAlt.dAO w u1 u2 5 = shiftS (tEvenSet u2) (A + B + B + U) := by simp [ClosedPathAlt.dAO, pieceSet, hD, hR]
    rw [hdj]
    exact mem_shift _ _ _ ((0 : ℤ × ℤ)) mQ.1 (by abel)
  have h1 := hC _ m1 m2
  have hval : paperNearLadderAltValue (2 * (k : ℤ) + 2) ((2 * (k : ℤ) + 1), (4 * (k : ℤ) + 2)) = (-(k : ℤ) ^ 2 - 3 * (k : ℤ)) := by
    have hq : (((4 * (k : ℤ) + 2) : ℤ) - (2 * (k : ℤ) + 1)) ^ 2 = 4 * ((k : ℤ) ^ 2 + (k : ℤ)) + 1 := by ring
    simp only [paperNearLadderAltValue, Set.indicator_apply, Set.mem_union, paperNearLadderAltA, paperNearLadderAltB, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_setOf_eq, Prod.mk.injEq]
    split_ifs <;> (try simp only [not_or, not_and] at *) <;> omega
  rw [hvH _ m1, ez, hval] at h1
  rw [evalO_ge w _ _ 0 5 _ (A + B + B + U) ((p.num, -p.den) + (p.num, -p.den)) ((0 : ℤ × ℤ)) (by norm_num) (by rw [hR]; rfl) (by rw [hAf]; rfl) (by abel), vQ.1] at h1
  intro z hz1 hz2
  have h2 := hC z hz1 hz2
  rw [← placedAltOdd_add]
  simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, dot2, kOddEF, Pi.zero_apply, add_zero, hr1, hr2, hr3, hr4] at h1 h2 hB4 hV4 ⊢
  try simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, Prod.fst_neg, Prod.snd_neg, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, dotS, dot2, kOddEF, hr1, hr2, hr3, hr4] at h1
  linarith

end FLatticePaper.Tiles.AltBaseContacts




