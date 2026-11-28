import FLatticePaper.Tiles.BaseVertOdoFamily
import FLatticePaper.Tiles.BaseTileProps
import FLatticePaper.Tiles.TexVPositions
import FLatticePaper.Tiles.StandardClauseA
import FLatticePaper.Tiles.VerticalIdentities

/-! # The forward vertical base piece of the odd `3^k` word respects its string

The forward vertical string of `p^(2k+1) q`, anchored at the lower-left point `c = lastPosOf (hStringAt (hWordOf 3^k false) 0)`,
which is `(4k+3, 1)`, is covered by the translated family `vpPiece w c = (vtP w).translate c`. Its tiles are the `zero` tiles at
`c + (-j, j)`, `0 ≤ j ≤ 2k`, and the `one` tile at `c + (-2k, 2k+2)`; the slopes are `(0,-j)` and the constants `j(j+3)/2`. On each
domain the odometer equals the paper ladder value of depth `2k+2`. -/

namespace FLatticePaper.Tiles.BaseVertVp

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.SiteStrings
open FLatticePaper.Tiles.BaseVertOdo FLatticePaper.Tiles.BaseVertOdoFamily FLatticePaper.Tiles.StandardClause

/-- The anchor of the forward vertical string of the odd child of `3^k`: `(4k+3, 1)`. -/
theorem anchor_three (k : ℕ) :
    lastPosOf (hStringAt (hWordOf (List.replicate k Digit.three) false) (0, 0)) = (4 * (k : ℤ) + 3, 1) := by
  rw [TexVPositions.lastPos_hWordOf_false_tex]
  unfold fracOdd
  rw [BaseTileProps.cur_odd_three]
  unfold texV1Odd
  ext
  all_goals simp
  all_goals ring

/-- The forward vertical family of `w`, translated to the anchor `c`. -/
def vpPiece (w : BinaryWord) (c : GInt) : PTFamily := (vtP w).translate c

theorem vpPiece_ts (w : BinaryWord) (c : GInt) : (vpPiece w c).ts = vStringAt w c := by
  have h := zoForwardV_eq w
  have e := vStringAt_add w 0 c
  rw [zero_add] at e
  simp only [vpPiece, PTFamily.translate, vtP]
  rw [h, e]

theorem vpPiece_ts_range (w : BinaryWord) (c : GInt) :
    (vpPiece w c).ts = (List.range w.length).map
      (fun k => (letterZTile (lettersOf w false k), posF .vertical false (lettersOf w false) k + c)) := by
  simp only [vpPiece, PTFamily.translate, vtP, zoForwardV, List.map_map, Function.comp_def]

theorem vpPiece_n (w : BinaryWord) (c : GInt) : (vpPiece w c).n = w.length := by
  simp [PTFamily.n, vpPiece_ts_range]

theorem vpPiece_tile (w : BinaryWord) (c : GInt) (J : ℕ) (hJ : J < w.length) :
    (vpPiece w c).tile J = (letterZTile (lettersOf w false J), posF .vertical false (lettersOf w false) J + c) := by
  unfold PTFamily.tile
  rw [vpPiece_ts_range]
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hJ]

theorem vpPiece_a (w : BinaryWord) (c : GInt) (J : ℕ) : (vpPiece w c).a J = vtAff (lettersOf w false) J := rfl

theorem vpPiece_b (w : BinaryWord) (c : GInt) (J : ℕ) :
    (vpPiece w c).b J = vtCP (lettersOf w false) J
      - ptDot (vtAff (lettersOf w false) J) (posF .vertical false (lettersOf w false) J)
      - ptDot (vtAff (lettersOf w false) J) c := rfl

theorem vpPiece_odo (w : BinaryWord) (c : GInt) (J : ℕ) (hJ : J < w.length) (x : GInt) :
    (vpPiece w c).odo J x =
      zTileOdo (letterZTile (lettersOf w false J)) (x - (posF .vertical false (lettersOf w false) J + c))
      + (vtAff (lettersOf w false) J).1 * x.1 + (vtAff (lettersOf w false) J).2 * x.2
      + (vtCP (lettersOf w false) J - ptDot (vtAff (lettersOf w false) J) (posF .vertical false (lettersOf w false) J)
        - ptDot (vtAff (lettersOf w false) J) c) := by
  unfold PTFamily.odo
  rw [vpPiece_tile w c J hJ, vpPiece_a, vpPiece_b]

/-! ### The letters, positions and constants of `p^m q` read forwards -/

theorem lettersOf_fwd (m j : ℕ) :
    lettersOf (List.replicate m Letter.p ++ [Letter.q]) false j = if j = m then Letter.q else Letter.p := by
  unfold lettersOf
  by_cases h : j = m
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · rcases Nat.lt_or_gt_of_ne h with hl | hg
    · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left, hl, h]
    · rw [List.getD_eq_default _ _ (by simp; omega), if_neg h]

theorem vtCnt_fwd (m : ℕ) : ∀ j : ℕ, j ≤ m →
    vtCnt (lettersOf (List.replicate m Letter.p ++ [Letter.q]) false) j = 0 := by
  intro j
  induction j with
  | zero => intro _; simp [vtCnt]
  | succ n ih =>
    intro hn
    rw [show vtCnt (lettersOf (List.replicate m Letter.p ++ [Letter.q]) false) (n + 1)
        = vtCnt (lettersOf (List.replicate m Letter.p ++ [Letter.q]) false) n
          + (if lettersOf (List.replicate m Letter.p ++ [Letter.q]) false n = Letter.q then 1 else 0) from rfl,
      ih (by omega)]
    simp [lettersOf_fwd, show n ≠ m by omega]

/-- The positions of the zero tiles: `posF j = (-j, j)` for `j + 1 ≤ m`. -/
theorem posF_fwd_zero (m : ℕ) : ∀ j : ℕ, j + 1 ≤ m →
    posF .vertical false (lettersOf (List.replicate m Letter.p ++ [Letter.q]) false) j = (-(j : ℤ), (j : ℤ)) := by
  intro j
  induction j with
  | zero => intro _; simp [posF]; rfl
  | succ n ih =>
    intro hn
    rw [show posF .vertical false (lettersOf (List.replicate m Letter.p ++ [Letter.q]) false) (n + 1)
        = posF .vertical false (lettersOf (List.replicate m Letter.p ++ [Letter.q]) false) n
          + stepOf .vertical false (lettersOf (List.replicate m Letter.p ++ [Letter.q]) false n)
            (lettersOf (List.replicate m Letter.p ++ [Letter.q]) false (n + 1)) from rfl,
      ih (by omega), lettersOf_fwd m (n + 1), if_neg (by omega)]
    simp only [stepOf, zeroOneVerticalStep]
    ext
    all_goals simp
    all_goals ring

/-- The position of the one tile at index `2k+1`: `posF (2k+1) = (-2k, 2k+2)`. -/
theorem posF_fwd_last (k : ℕ) :
    posF .vertical false (lettersOf (List.replicate (2 * k + 1) Letter.p ++ [Letter.q]) false) (2 * k + 1)
      = (-(2 * (k : ℤ)), 2 * (k : ℤ) + 2) := by
  rw [show posF .vertical false (lettersOf (List.replicate (2 * k + 1) Letter.p ++ [Letter.q]) false) (2 * k + 1)
      = posF .vertical false (lettersOf (List.replicate (2 * k + 1) Letter.p ++ [Letter.q]) false) (2 * k)
        + stepOf .vertical false (lettersOf (List.replicate (2 * k + 1) Letter.p ++ [Letter.q]) false (2 * k))
          (lettersOf (List.replicate (2 * k + 1) Letter.p ++ [Letter.q]) false (2 * k + 1)) from rfl,
    posF_fwd_zero (2 * k + 1) (2 * k) (by omega), lettersOf_fwd (2 * k + 1) (2 * k + 1)]
  simp only [stepOf, zeroOneVerticalStep]
  ext
  all_goals simp

/-- The centred constants of the zero tiles: `2 vtCP j = -j(j-1)` for `j + 1 ≤ m`. -/
theorem vtCP_fwd (m : ℕ) : ∀ j : ℕ, j + 1 ≤ m →
    2 * vtCP (lettersOf (List.replicate m Letter.p ++ [Letter.q]) false) j = -((j : ℤ) * ((j : ℤ) - 1)) := by
  intro j
  induction j with
  | zero => intro _; simp [vtCP]
  | succ n ih =>
    intro hn
    rw [show vtCP (lettersOf (List.replicate m Letter.p ++ [Letter.q]) false) (n + 1)
        = vtCP (lettersOf (List.replicate m Letter.p ++ [Letter.q]) false) n
          + vtBetaP (lettersOf (List.replicate m Letter.p ++ [Letter.q]) false n)
            (lettersOf (List.replicate m Letter.p ++ [Letter.q]) false (n + 1))
          + ptDot (vtAff (lettersOf (List.replicate m Letter.p ++ [Letter.q]) false) n)
            (zeroOneVerticalStep (lettersOf (List.replicate m Letter.p ++ [Letter.q]) false (n + 1))) from rfl]
    rw [lettersOf_fwd m n, lettersOf_fwd m (n + 1), if_neg (by omega), if_neg (by omega)]
    have hA : vtAff (lettersOf (List.replicate m Letter.p ++ [Letter.q]) false) n = (0, -(n : ℤ)) := by
      simp [vtAff, vtCnt_fwd m n (by omega)]
    rw [hA]
    simp only [vtBetaP, zeroOneVerticalStep, ptDot]
    have ih' := ih (by omega)
    push_cast
    linarith

/-- The centred constant of the one tile at index `2k+1`: `2 vtCP (2k+1) = -2k(2k-1) - 2 - 8k`. -/
theorem vtCP_last (k : ℕ) :
    2 * vtCP (lettersOf (List.replicate (2 * k + 1) Letter.p ++ [Letter.q]) false) (2 * k + 1)
      = -((2 * (k : ℤ)) * (2 * (k : ℤ) - 1)) - 2 - 8 * (k : ℤ) := by
  have hprev := vtCP_fwd (2 * k + 1) (2 * k) (by omega)
  rw [show vtCP (lettersOf (List.replicate (2 * k + 1) Letter.p ++ [Letter.q]) false) (2 * k + 1)
      = vtCP (lettersOf (List.replicate (2 * k + 1) Letter.p ++ [Letter.q]) false) (2 * k)
        + vtBetaP (lettersOf (List.replicate (2 * k + 1) Letter.p ++ [Letter.q]) false (2 * k))
          (lettersOf (List.replicate (2 * k + 1) Letter.p ++ [Letter.q]) false (2 * k + 1))
        + ptDot (vtAff (lettersOf (List.replicate (2 * k + 1) Letter.p ++ [Letter.q]) false) (2 * k))
          (zeroOneVerticalStep (lettersOf (List.replicate (2 * k + 1) Letter.p ++ [Letter.q]) false (2 * k + 1))) from rfl]
  rw [lettersOf_fwd (2 * k + 1) (2 * k), lettersOf_fwd (2 * k + 1) (2 * k + 1), if_neg (by omega), if_pos rfl]
  have hA : vtAff (lettersOf (List.replicate (2 * k + 1) Letter.p ++ [Letter.q]) false) (2 * k) = (0, -(2 * (k : ℤ))) := by
    simp [vtAff, vtCnt_fwd (2 * k + 1) (2 * k) (by omega)]
  rw [hA]
  simp only [vtBetaP, zeroOneVerticalStep, ptDot]
  push_cast at hprev ⊢
  linarith

/-! ### The paper ladder values on the tiles of the forward piece -/

/-- The zero-tile values: `P(4k+3-j+a, 1+j+b)` for `0 ≤ j ≤ 2k`, `(a,b)` in the zero tile. -/
theorem ladder_vp_zero (k j a b : ℤ) (hk : 1 ≤ k) (hj0 : 0 ≤ j) (hj : j ≤ 2 * k) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb2 : b ≤ 2) :
    paperLadderValue (2 * k + 2) (4 * k + 3 - j + a, 1 + j + b) =
      -((1 + j + b) * (1 + j + b + 1) / 2) + (1 + j + b) + (j - 2 * k - a) + (2 * k + a + b) := by
  have hnot : (4 * k + 3 - j + a, 1 + j + b) ∉ paperLadderA (2 * k + 2) ∪ paperLadderB (2 * k + 2) := by
    rintro (h | h)
    · simp only [paperLadderA, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    · simp only [paperLadderB, Set.mem_setOf_eq] at h
      omega
  unfold paperLadderValue
  dsimp only
  rw [Set.indicator_of_notMem hnot]
  simp only [min_def, max_def]
  split_ifs <;> omega

/-- The one-tile values at `(2k+3+a, 2k+3+b)`, `(a,b)` in the one tile, with the indicator at `(1,1)`. -/
theorem ladder_vp_one (k a b : ℤ) (hk : 0 ≤ k) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    paperLadderValue (2 * k + 2) (2 * k + 3 + a, 2 * k + 3 + b) =
      -((2 * k + 3 + b) * (2 * k + 3 + b + 1) / 2) + (4 * k + 5 + 2 * b)
        + (if a = 1 ∧ b = 1 then 1 else 0) := by
  have hmem : (2 * k + 3 + a, 2 * k + 3 + b) ∈ paperLadderA (2 * k + 2) ∪ paperLadderB (2 * k + 2) ↔
      (a = 1 ∧ b = 1) := by
    simp only [paperLadderA, paperLadderB, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_setOf_eq, Prod.mk.injEq]
    constructor <;> intro h <;> omega
  unfold paperLadderValue
  dsimp only
  by_cases h11 : a = 1 ∧ b = 1
  · rw [if_pos h11, Set.indicator_of_mem (hmem.2 h11)]
    simp only [min_def, max_def]
    split_ifs <;> omega
  · rw [if_neg h11, Set.indicator_of_notMem (fun h => h11 (hmem.1 h))]
    simp only [min_def, max_def]
    split_ifs <;> omega

/-- The zero tile at index `j` of the forward piece: the paper value equals the odometer of the family. -/
theorem vp_zero_pt (k : ℕ) (hk : 1 ≤ k) (j : ℕ) (hj : j < 2 * k + 1) (y : GInt) (hy : y ∈ tileShape ZTile.zero) :
    paperLadderValue (2 * (k : ℤ) + 2) (y + ((-(j : ℤ), (j : ℤ)) + (4 * (k : ℤ) + 3, 1))) =
      (vpPiece (List.replicate (2 * k + 1) Letter.p ++ [Letter.q]) (4 * (k : ℤ) + 3, 1)).odo j
        (y + ((-(j : ℤ), (j : ℤ)) + (4 * (k : ℤ) + 3, 1))) := by
  have hk' : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  have hw : j < (List.replicate (2 * k + 1) Letter.p ++ [Letter.q]).length := by simp; omega
  have hV := vtCP_fwd (2 * k + 1) j (by omega)
  obtain ⟨a, b⟩ := y
  have hT := Int.two_mul_ediv_two_of_even (Int.even_mul_succ_self (1 + (j : ℤ) + b))
  have hab : (a, b) = (0, 0) ∨ (a, b) = (0, 1) ∨ (a, b) = (0, 2) ∨ (a, b) = (1, 0) ∨ (a, b) = (1, 1)
      ∨ (a, b) = (1, 2) := by
    simpa [tileShape] using hy
  have ha : 0 ≤ a ∧ a ≤ 1 := by
    rcases hab with h | h | h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> omega
  have hb : 0 ≤ b ∧ b ≤ 2 := by
    rcases hab with h | h | h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> omega
  have e1 : (a, b) + ((-(j : ℤ), (j : ℤ)) + (4 * (k : ℤ) + 3, 1)) = (4 * (k : ℤ) + 3 - j + a, 1 + j + b) :=
    Prod.ext (by simp only [Prod.fst_add]; ring) (by simp only [Prod.snd_add]; ring)
  have e2 : (4 * (k : ℤ) + 3 - j + a, 1 + j + b) - ((-(j : ℤ), (j : ℤ)) + (4 * (k : ℤ) + 3, 1)) = (a, b) :=
    Prod.ext (by simp only [Prod.fst_sub, Prod.fst_add]; ring) (by simp only [Prod.snd_sub, Prod.snd_add]; ring)
  rw [vpPiece_odo _ _ j hw]
  rw [posF_fwd_zero (2 * k + 1) j (by omega), lettersOf_fwd (2 * k + 1) j, if_neg (by omega)]
  have hA : vtAff (lettersOf (List.replicate (2 * k + 1) Letter.p ++ [Letter.q]) false) j = (0, -(j : ℤ)) := by
    simp [vtAff, vtCnt_fwd (2 * k + 1) j (by omega)]
  have hz : letterZTile Letter.p = ZTile.zero := rfl
  rw [hA, hz, e1, e2]
  rw [ladder_vp_zero (k : ℤ) (j : ℤ) a b hk' (by positivity) (by omega) ha.1 ha.2 hb.1 hb.2]
  rcases hab with h | h | h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h <;>
    norm_num [zeroOdometer, zTileOdo, ptDot] at hT hV ⊢ <;> linarith

/-- The one tile at index `2k+1` of the forward piece. -/
theorem vp_one_pt (k : ℕ) (hk : 1 ≤ k) (y : GInt) (hy : y ∈ tileShape ZTile.one) :
    paperLadderValue (2 * (k : ℤ) + 2) (y + ((-(2 * (k : ℤ)), 2 * (k : ℤ) + 2) + (4 * (k : ℤ) + 3, 1))) =
      (vpPiece (List.replicate (2 * k + 1) Letter.p ++ [Letter.q]) (4 * (k : ℤ) + 3, 1)).odo (2 * k + 1)
        (y + ((-(2 * (k : ℤ)), 2 * (k : ℤ) + 2) + (4 * (k : ℤ) + 3, 1))) := by
  have hk0 : (0 : ℤ) ≤ (k : ℤ) := by positivity
  have hw : 2 * k + 1 < (List.replicate (2 * k + 1) Letter.p ++ [Letter.q]).length := by simp
  have hV := vtCP_last k
  obtain ⟨a, b⟩ := y
  have hT := Int.two_mul_ediv_two_of_even (Int.even_mul_succ_self (2 * (k : ℤ) + 3 + b))
  have hab : (a, b) = (0, 0) ∨ (a, b) = (0, 1) ∨ (a, b) = (1, 0) ∨ (a, b) = (1, 1) := by
    simpa [tileShape] using hy
  have ha : 0 ≤ a ∧ a ≤ 1 := by
    rcases hab with h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> omega
  have hb : 0 ≤ b ∧ b ≤ 1 := by
    rcases hab with h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> omega
  have e1 : (a, b) + ((-(2 * (k : ℤ)), 2 * (k : ℤ) + 2) + (4 * (k : ℤ) + 3, 1))
      = (2 * (k : ℤ) + 3 + a, 2 * (k : ℤ) + 3 + b) :=
    Prod.ext (by simp only [Prod.fst_add]; ring) (by simp only [Prod.snd_add]; ring)
  have e2 : (2 * (k : ℤ) + 3 + a, 2 * (k : ℤ) + 3 + b)
      - ((-(2 * (k : ℤ)), 2 * (k : ℤ) + 2) + (4 * (k : ℤ) + 3, 1)) = (a, b) :=
    Prod.ext (by simp only [Prod.fst_sub, Prod.fst_add]; ring) (by simp only [Prod.snd_sub, Prod.snd_add]; ring)
  rw [vpPiece_odo _ _ (2 * k + 1) hw]
  rw [posF_fwd_last k, lettersOf_fwd (2 * k + 1) (2 * k + 1), if_pos rfl]
  have hA : vtAff (lettersOf (List.replicate (2 * k + 1) Letter.p ++ [Letter.q]) false) (2 * k + 1)
      = (0, -(2 * (k : ℤ) + 1)) := by
    simp [vtAff, vtCnt_fwd (2 * k + 1) (2 * k + 1) le_rfl]
  have hz : letterZTile Letter.q = ZTile.one := rfl
  rw [hA, hz, e1, e2]
  rw [ladder_vp_one (k : ℤ) a b hk0 ha.1 ha.2 hb.1 hb.2]
  rcases hab with h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h <;>
    norm_num [oneOdometer, zTileOdo, ptDot] at hT hV ⊢ <;> linarith

/-- The forward vertical base piece of the odd `3^k` word (`k ≥ 1`), anchored at `(4k+3, 1)`, respects its string, with the
paper ladder value of depth `2k+2` as odometer. -/
theorem vp_odd_respects (k : ℕ) (hk : 1 ≤ k) :
    RespectsTiles .vertical false
      (vStringAt (vWordOf (List.replicate k Digit.three) false)
        (lastPosOf (hStringAt (hWordOf (List.replicate k Digit.three) false) (0, 0))))
      (paperLadderValue (2 * (k : ℤ) + 2)) := by
  rw [anchor_three k, FLatticePaper.Tiles.BaseVertPiece.vWordOf_three_false]
  have hR : (vpPiece (List.replicate (2 * k + 1) Letter.p ++ [Letter.q]) (4 * (k : ℤ) + 3, 1)).Respects
      .vertical false :=
    PTFamily.translate_respects _ _ _ _ (vtP_respects _)
  refine ⟨vpPiece _ _, vpPiece_ts _ _, ?_, hR⟩
  intro J hJ x hx
  rw [vpPiece_n] at hJ
  simp only [List.length_append, List.length_replicate, List.length_singleton] at hJ
  rcases (show J < 2 * k + 1 ∨ J = 2 * k + 1 by omega) with hJ' | rfl
  · unfold PTFamily.dom at hx
    rw [vpPiece_tile _ _ J (by simp; omega), lettersOf_fwd (2 * k + 1) J, if_neg (by omega),
      posF_fwd_zero (2 * k + 1) J (by omega)] at hx
    have hz : letterZTile Letter.p = ZTile.zero := rfl
    rw [hz] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact vp_zero_pt k hk J hJ' y hy
  · unfold PTFamily.dom at hx
    rw [vpPiece_tile _ _ (2 * k + 1) (by simp), lettersOf_fwd (2 * k + 1) (2 * k + 1), if_pos rfl,
      posF_fwd_last k] at hx
    have hz : letterZTile Letter.q = ZTile.one := rfl
    rw [hz] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact vp_one_pt k hk y hy

end FLatticePaper.Tiles.BaseVertVp
