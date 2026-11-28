import FLatticePaper.Tiles.BaseVertVp
import FLatticePaper.Tiles.BaseVertOdoFamily
import FLatticePaper.Tiles.RegisterLink
import FLatticePaper.Tiles.AltRotStep
import FLatticePaper.Tiles.BaseTileProps
import FLatticePaper.Tiles.TexVPositions
import FLatticePaper.Tiles.StandardClauseA
import FLatticePaper.Construction.BaseCaseRecurrence

/-! # The vertical base pieces of the even `3^k` word (`k ≥ 0`, so also the empty word's even child)

The vertical word of the even child of `3^k` is `p^(2k+2) q`, its anchor is `(2k+2, 0)`, and the odometer of both pieces is
the stair value `paperStairValue (2k+3)`. The forward piece `Vp` has zero tiles at `c + (-j, j)`, `0 ≤ j ≤ 2k+1`, and a one
tile at `c + (-(2k+1), 2k+3)`. The reversed piece `Vm` (anchor `(0,0)`) has a one tile at `(0,0)` and zero tiles at
`(-(j-1), j)`, `1 ≤ j ≤ 2k+2`. -/

namespace FLatticePaper.Tiles.BaseThreeEven

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.SiteStrings
open FLatticePaper.Tiles.BaseVertOdo FLatticePaper.Tiles.BaseVertOdoFamily FLatticePaper.Tiles.BaseVertVp
open FLatticePaper.Tiles.StandardClause

theorem wv_three_even (k : ℕ) :
    vWordOf (List.replicate k Digit.three) true = List.replicate (2 * k + 2) Letter.p ++ [Letter.q] := by
  unfold vWordOf
  rw [FLatticePaper.Tiles.AltRotStep.swapW_replicate_three, if_pos rfl,
    (FLatticePaper.Tiles.RegisterLink.quad_twos k).1]
  simp [List.map_append, swapLetter, List.map_replicate]

theorem hz0 : letterZTile Letter.p = ZTile.zero := rfl

theorem hz1 : letterZTile Letter.q = ZTile.one := rfl

theorem anchor_three_even (k : ℕ) :
    lastPosOf (hStringAt (hWordOf (List.replicate k Digit.three) true) (0, 0)) = (2 * (k : ℤ) + 2, 0) := by
  rw [TexVPositions.lastPos_hWordOf_true_tex]
  unfold fracEven
  rw [BaseTileProps.cur_even_three]
  unfold texV1Even
  ext
  all_goals simp
  all_goals ring

/-! ### The forward piece: the top tile and its constant -/

theorem posF_fwd_top2 (k : ℕ) :
    posF .vertical false (lettersOf (List.replicate (2 * k + 2) Letter.p ++ [Letter.q]) false) (2 * k + 2)
      = (-(2 * (k : ℤ) + 1), 2 * (k : ℤ) + 3) := by
  rw [show posF .vertical false (lettersOf (List.replicate (2 * k + 2) Letter.p ++ [Letter.q]) false) (2 * k + 2)
      = posF .vertical false (lettersOf (List.replicate (2 * k + 2) Letter.p ++ [Letter.q]) false) (2 * k + 1)
        + stepOf .vertical false (lettersOf (List.replicate (2 * k + 2) Letter.p ++ [Letter.q]) false (2 * k + 1))
          (lettersOf (List.replicate (2 * k + 2) Letter.p ++ [Letter.q]) false (2 * k + 2)) from rfl,
    posF_fwd_zero (2 * k + 2) (2 * k + 1) (by omega), lettersOf_fwd (2 * k + 2) (2 * k + 2), if_pos rfl]
  simp only [stepOf, zeroOneVerticalStep]
  ext
  all_goals simp
  all_goals ring

theorem vtCP_fwd_top2 (k : ℕ) :
    2 * vtCP (lettersOf (List.replicate (2 * k + 2) Letter.p ++ [Letter.q]) false) (2 * k + 2)
      = -((2 * (k : ℤ) + 1) * (2 * (k : ℤ))) - 2 - 4 * (2 * (k : ℤ) + 1) := by
  have hprev := vtCP_fwd (2 * k + 2) (2 * k + 1) (by omega)
  have hA : vtAff (lettersOf (List.replicate (2 * k + 2) Letter.p ++ [Letter.q]) false) (2 * k + 1)
      = (0, -(2 * (k : ℤ) + 1)) := by
    simp [vtAff, vtCnt_fwd (2 * k + 2) (2 * k + 1) (by omega)]
  rw [show vtCP (lettersOf (List.replicate (2 * k + 2) Letter.p ++ [Letter.q]) false) (2 * k + 2)
      = vtCP (lettersOf (List.replicate (2 * k + 2) Letter.p ++ [Letter.q]) false) (2 * k + 1)
        + vtBetaP (lettersOf (List.replicate (2 * k + 2) Letter.p ++ [Letter.q]) false (2 * k + 1))
          (lettersOf (List.replicate (2 * k + 2) Letter.p ++ [Letter.q]) false (2 * k + 2))
        + ptDot (vtAff (lettersOf (List.replicate (2 * k + 2) Letter.p ++ [Letter.q]) false) (2 * k + 1))
          (zeroOneVerticalStep (lettersOf (List.replicate (2 * k + 2) Letter.p ++ [Letter.q]) false (2 * k + 2)))
      from rfl]
  rw [lettersOf_fwd (2 * k + 2) (2 * k + 1), lettersOf_fwd (2 * k + 2) (2 * k + 2),
    if_neg (show ¬(2 * k + 1 = 2 * k + 2) by omega), if_pos rfl, hA]
  simp only [vtBetaP, zeroOneVerticalStep, ptDot]
  push_cast at hprev ⊢
  linarith

/-! ### The stair value on the tiles -/

/-- The zero tile `j` of the forward piece: the stair value at `(2k+2-j+a, j+b)`. -/
theorem paper_stair_zero (k j a b : ℤ) (hj : j ≤ 2 * k + 1) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb2 : b ≤ 2) :
    paperStairValue (2 * k + 3) (2 * k + 2 - j + a, j + b) = -((j + b) * (j + b + 1) / 2) + (j + b) := by
  unfold paperStairValue
  dsimp only
  rw [min_eq_right (show (0 : ℤ) ≤ 2 * k + 2 - j + a - 1 by omega),
    if_neg (show ¬((2 * k + 2 - j + a, j + b) = (0, 0) ∨ (2 * k + 2 - j + a, j + b) = (2, 2 * k + 3 + 1)) from by
      rintro (h | h) <;> simp only [Prod.mk.injEq] at h <;> omega)]
  ring

/-- The one tile `2k+2` of the forward piece: the stair value at `(1+a, 2k+3+b)`. -/
theorem paper_stair_one (k a b : ℤ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    paperStairValue (2 * k + 3) (1 + a, 2 * k + 3 + b) =
      -((2 * k + 3 + b) * (2 * k + 3 + b + 1) / 2) + (2 * k + 3 + b) + (if a = 1 ∧ b = 1 then 1 else 0) := by
  unfold paperStairValue
  dsimp only
  rw [min_eq_right (show (0 : ℤ) ≤ 1 + a - 1 by omega)]
  by_cases h11 : a = 1 ∧ b = 1
  · rw [if_pos h11, if_pos (show (1 + a, 2 * k + 3 + b) = (0, 0) ∨ (1 + a, 2 * k + 3 + b) = (2, 2 * k + 3 + 1)
      from Or.inr (Prod.ext (by omega) (by omega)))]
    ring
  · rw [if_neg h11, if_neg (show ¬((1 + a, 2 * k + 3 + b) = (0, 0) ∨ (1 + a, 2 * k + 3 + b) = (2, 2 * k + 3 + 1))
      from by rintro (h | h) <;> simp only [Prod.mk.injEq] at h <;> omega)]
    ring

/-! ### The tile identities of the forward piece -/

theorem vp3e_zero_pt (k j : ℕ) (hj : j ≤ 2 * k + 1) (y : GInt) (hy : y ∈ tileShape ZTile.zero) :
    paperStairValue (2 * (k : ℤ) + 3) (y + ((-(j : ℤ), (j : ℤ)) + (2 * (k : ℤ) + 2, 0))) =
      (vpPiece (List.replicate (2 * k + 2) Letter.p ++ [Letter.q]) (2 * (k : ℤ) + 2, 0)).odo j
        (y + ((-(j : ℤ), (j : ℤ)) + (2 * (k : ℤ) + 2, 0))) := by
  obtain ⟨a, b⟩ := y
  have hab : (a, b) = (0, 0) ∨ (a, b) = (0, 1) ∨ (a, b) = (0, 2) ∨ (a, b) = (1, 0) ∨ (a, b) = (1, 1)
      ∨ (a, b) = (1, 2) := by
    simpa [tileShape] using hy
  have ha : 0 ≤ a ∧ a ≤ 1 := by
    rcases hab with h | h | h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> omega
  have hb : 0 ≤ b ∧ b ≤ 2 := by
    rcases hab with h | h | h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> omega
  have hV := vtCP_fwd (2 * k + 2) j (by omega)
  have hA : vtAff (lettersOf (List.replicate (2 * k + 2) Letter.p ++ [Letter.q]) false) j = (0, -(j : ℤ)) := by
    simp [vtAff, vtCnt_fwd (2 * k + 2) j (by omega)]
  rw [vpPiece_odo _ _ j (by simp only [List.length_append, List.length_replicate, List.length_singleton]; omega),
    posF_fwd_zero (2 * k + 2) j (by omega), lettersOf_fwd (2 * k + 2) j,
    if_neg (show ¬(j = 2 * k + 2) by omega), hz0, hA]
  have e1 : (a, b) + ((-(j : ℤ), (j : ℤ)) + (2 * (k : ℤ) + 2, 0)) = (2 * (k : ℤ) + 2 - j + a, j + b) :=
    Prod.ext (by simp only [Prod.fst_add]; ring) (by simp only [Prod.snd_add]; ring)
  have e2 : (2 * (k : ℤ) + 2 - j + a, j + b) - ((-(j : ℤ), (j : ℤ)) + (2 * (k : ℤ) + 2, 0)) = (a, b) :=
    Prod.ext (by simp only [Prod.fst_sub, Prod.fst_add]; ring) (by simp only [Prod.snd_sub, Prod.snd_add]; ring)
  rw [e1, e2, paper_stair_zero (k : ℤ) (j : ℤ) a b (by omega) ha.1 ha.2 hb.1 hb.2]
  have hT := Int.two_mul_ediv_two_of_even (Int.even_mul_succ_self ((j : ℤ) + b))
  generalize ((j : ℤ) + b) * ((j : ℤ) + b + 1) / 2 = T at hT ⊢
  simp only [zTileOdo, ptDot]
  rcases hab with h | h | h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h <;>
    norm_num [zeroOdometer] at hT hV ⊢ <;> linarith

theorem vp3e_top_pt (k : ℕ) (y : GInt) (hy : y ∈ tileShape ZTile.one) :
    paperStairValue (2 * (k : ℤ) + 3) (y + ((-(2 * (k : ℤ) + 1), 2 * (k : ℤ) + 3) + (2 * (k : ℤ) + 2, 0))) =
      (vpPiece (List.replicate (2 * k + 2) Letter.p ++ [Letter.q]) (2 * (k : ℤ) + 2, 0)).odo (2 * k + 2)
        (y + ((-(2 * (k : ℤ) + 1), 2 * (k : ℤ) + 3) + (2 * (k : ℤ) + 2, 0))) := by
  obtain ⟨a, b⟩ := y
  have hab : (a, b) = (0, 0) ∨ (a, b) = (0, 1) ∨ (a, b) = (1, 0) ∨ (a, b) = (1, 1) := by
    simpa [tileShape] using hy
  have ha : 0 ≤ a ∧ a ≤ 1 := by
    rcases hab with h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> omega
  have hb : 0 ≤ b ∧ b ≤ 1 := by
    rcases hab with h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> omega
  have hV := vtCP_fwd_top2 k
  have hA : vtAff (lettersOf (List.replicate (2 * k + 2) Letter.p ++ [Letter.q]) false) (2 * k + 2)
      = (0, -(2 * (k : ℤ) + 2)) := by
    simp [vtAff, vtCnt_fwd (2 * k + 2) (2 * k + 2) le_rfl]
  rw [vpPiece_odo _ _ (2 * k + 2) (by simp only [List.length_append, List.length_replicate, List.length_singleton]; omega),
    posF_fwd_top2 k, lettersOf_fwd (2 * k + 2) (2 * k + 2), if_pos rfl, hz1, hA]
  have e1 : (a, b) + ((-(2 * (k : ℤ) + 1), 2 * (k : ℤ) + 3) + (2 * (k : ℤ) + 2, 0)) = (1 + a, 2 * (k : ℤ) + 3 + b) :=
    Prod.ext (by simp only [Prod.fst_add]; ring) (by simp only [Prod.snd_add]; ring)
  have e2 : (1 + a, 2 * (k : ℤ) + 3 + b) - ((-(2 * (k : ℤ) + 1), 2 * (k : ℤ) + 3) + (2 * (k : ℤ) + 2, 0)) = (a, b) :=
    Prod.ext (by simp only [Prod.fst_sub, Prod.fst_add]; ring) (by simp only [Prod.snd_sub, Prod.snd_add]; ring)
  rw [e1, e2, paper_stair_one (k : ℤ) a b ha.1 ha.2]
  have hT := Int.two_mul_ediv_two_of_even (Int.even_mul_succ_self (2 * (k : ℤ) + 3 + b))
  generalize (2 * (k : ℤ) + 3 + b) * (2 * (k : ℤ) + 3 + b + 1) / 2 = T at hT ⊢
  simp only [zTileOdo, ptDot]
  rcases hab with h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h <;>
    norm_num [oneOdometer] at hT hV ⊢ <;> linarith

/-- The forward vertical base piece of the even `3^k` word (`k ≥ 0`, so also the empty word's even child) respects its
string, with the stair value as odometer. -/
theorem vp3e_respects (k : ℕ) :
    RespectsTiles .vertical false
      (vStringAt (vWordOf (List.replicate k Digit.three) true)
        (lastPosOf (hStringAt (hWordOf (List.replicate k Digit.three) true) (0, 0))))
      (paperStairValue (2 * (k : ℤ) + 3)) := by
  rw [anchor_three_even k, wv_three_even k]
  have hR : (vpPiece (List.replicate (2 * k + 2) Letter.p ++ [Letter.q]) (2 * (k : ℤ) + 2, 0)).Respects
      .vertical false :=
    PTFamily.translate_respects _ _ _ _ (vtP_respects _)
  refine ⟨vpPiece (List.replicate (2 * k + 2) Letter.p ++ [Letter.q]) (2 * (k : ℤ) + 2, 0), vpPiece_ts _ _, ?_, hR⟩
  intro J hJ x hx
  rw [vpPiece_n] at hJ
  simp only [List.length_append, List.length_replicate, List.length_singleton] at hJ
  rcases (show J ≤ 2 * k + 1 ∨ J = 2 * k + 2 by omega) with hJk | rfl
  · unfold PTFamily.dom at hx
    rw [vpPiece_tile _ _ J (by simp only [List.length_append, List.length_replicate, List.length_singleton]; omega),
      lettersOf_fwd (2 * k + 2) J, if_neg (show ¬(J = 2 * k + 2) by omega),
      posF_fwd_zero (2 * k + 2) J (by omega), hz0] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact vp3e_zero_pt k J hJk y hy
  · unfold PTFamily.dom at hx
    rw [vpPiece_tile _ _ (2 * k + 2) (by simp only [List.length_append, List.length_replicate, List.length_singleton]; omega),
      lettersOf_fwd (2 * k + 2) (2 * k + 2), if_pos rfl, posF_fwd_top2 k, hz1] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact vp3e_top_pt k y hy

/-! ### The tile identities of the reversed piece -/

theorem vm3e_one_pt (k : ℕ) (y : GInt) (hy : y ∈ tileShape ZTile.one) :
    paperStairValue (2 * (k : ℤ) + 3) y =
      (piece (List.replicate (2 * k + 2) Letter.p ++ [Letter.q])).odo 0 y := by
  obtain ⟨a, b⟩ := y
  have hab : (a, b) = (0, 0) ∨ (a, b) = (0, 1) ∨ (a, b) = (1, 0) ∨ (a, b) = (1, 1) := by
    simpa [tileShape] using hy
  rw [piece_odo_zero (2 * k + 2)]
  rcases hab with h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h <;>
    norm_num [paperStairValue, oneOdometer]

theorem paper_stair_vm (k j a b : ℤ) (hj0 : 0 ≤ j) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) :
    paperStairValue (2 * k + 3) (-j + a, j + 1 + b) =
      -((j + 1 + b) * (j + 1 + b + 1) / 2) + (j + 1 + b) + (-j + a - 1) := by
  unfold paperStairValue
  dsimp only
  rw [min_eq_left (show -j + a - 1 ≤ 0 by omega),
    if_neg (show ¬((-j + a, j + 1 + b) = (0, 0) ∨ (-j + a, j + 1 + b) = (2, 2 * k + 3 + 1)) from by
      rintro (h | h) <;> simp only [Prod.mk.injEq] at h <;> omega)]
  ring

theorem vm3e_zero_pt (k j : ℕ) (hj : j + 1 ≤ 2 * k + 2) (y : GInt) (hy : y ∈ tileShape ZTile.zero) :
    paperStairValue (2 * (k : ℤ) + 3) (y + (-(j : ℤ), (j : ℤ) + 1)) =
      (piece (List.replicate (2 * k + 2) Letter.p ++ [Letter.q])).odo (j + 1)
        (y + (-(j : ℤ), (j : ℤ) + 1)) := by
  obtain ⟨a, b⟩ := y
  have hab : (a, b) = (0, 0) ∨ (a, b) = (0, 1) ∨ (a, b) = (0, 2) ∨ (a, b) = (1, 0) ∨ (a, b) = (1, 1)
      ∨ (a, b) = (1, 2) := by
    simpa [tileShape] using hy
  have ha : 0 ≤ a ∧ a ≤ 1 := by
    rcases hab with h | h | h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> omega
  have hb : 0 ≤ b ∧ b ≤ 2 := by
    rcases hab with h | h | h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> omega
  have h0 := (lettersOf_rev_lv (2 * k + 2)).1
  have hs := (lettersOf_rev_lv (2 * k + 2)).2
  have hV := vtCM_closed _ h0 hs j
  have hj0 : (0 : ℤ) ≤ (j : ℤ) := by positivity
  rw [piece_odo_succ (2 * k + 2) j (by omega)]
  have e1 : (a, b) + (-(j : ℤ), (j : ℤ) + 1) = (-(j : ℤ) + a, (j : ℤ) + 1 + b) :=
    Prod.ext (by simp only [Prod.fst_add]; ring) (by simp only [Prod.snd_add]; ring)
  have e2 : (-(j : ℤ) + a, (j : ℤ) + 1 + b) - (-(j : ℤ), (j : ℤ) + 1) = (a, b) :=
    Prod.ext (by simp only [Prod.fst_sub]; ring) (by simp only [Prod.snd_sub]; ring)
  rw [e1, e2, paper_stair_vm (k : ℤ) (j : ℤ) a b hj0 ha.1 ha.2 hb.1]
  have hT := Int.two_mul_ediv_two_of_even (Int.even_mul_succ_self ((j : ℤ) + 1 + b))
  generalize ((j : ℤ) + 1 + b) * ((j : ℤ) + 1 + b + 1) / 2 = T at hT ⊢
  rcases hab with h | h | h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h <;>
    norm_num [zeroOdometer] at hT hV ⊢ <;> linarith

/-- The zero tiles of the reversed piece, at `(-j, j+1)`. -/
theorem vm3e_respects (k : ℕ) :
    RespectsTiles .vertical true
      (vRevStringAt (vWordOf (List.replicate k Digit.three) true).reverse (0, 0))
      (paperStairValue (2 * (k : ℤ) + 3)) := by
  rw [wv_three_even k]
  have hR : (piece (List.replicate (2 * k + 2) Letter.p ++ [Letter.q])).Respects .vertical true :=
    PTFamily.translate_respects _ _ _ _ (vtM_respects _)
  refine ⟨piece (List.replicate (2 * k + 2) Letter.p ++ [Letter.q]), piece_ts _, ?_, hR⟩
  intro J hJ x hx
  rw [piece_n] at hJ
  simp only [List.length_append, List.length_replicate, List.length_singleton] at hJ
  rcases (show J = 0 ∨ 1 ≤ J by omega) with rfl | hJ1
  · unfold PTFamily.dom at hx
    have hp0 : posF .vertical true (lettersOf (List.replicate (2 * k + 2) Letter.p ++ [Letter.q]) true) 0
        = (0, 0) := by
      simp [posF]
      rfl
    rw [piece_tile _ 0 (by simp only [List.length_append, List.length_replicate, List.length_singleton]; omega),
      (lettersOf_rev_lv (2 * k + 2)).1, hz1, hp0] at hx
    simp only [Prod.mk_zero_zero, add_zero] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact vm3e_one_pt k y hy
  · obtain ⟨j, rfl⟩ : ∃ j, J = j + 1 := ⟨J - 1, by omega⟩
    unfold PTFamily.dom at hx
    rw [piece_tile _ (j + 1) (by simp only [List.length_append, List.length_replicate, List.length_singleton]; omega),
      (lettersOf_rev_lv (2 * k + 2)).2 j, hz0,
      posF_vert_succ _ (lettersOf_rev_lv (2 * k + 2)).1 (lettersOf_rev_lv (2 * k + 2)).2 j] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact vm3e_zero_pt k j (by omega) y hy

end FLatticePaper.Tiles.BaseThreeEven
