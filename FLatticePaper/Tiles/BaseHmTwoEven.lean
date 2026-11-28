import FLatticePaper.Tiles.BaseHmTwoOdd
import FLatticePaper.Tiles.BaseHpNearEven
import FLatticePaper.Tiles.BaseTwoEven
import FLatticePaper.Tiles.BaseHmTwoAnchor

/-! # The reversed horizontal base piece of the even `2^k` word (`k ≥ 1`)

The forward word of the even child of `2^k` is `wEv k = q^{2k+1} p`; its reversed word is `p q^{2k+1}`, and the reversed
horizontal string is anchored at `(-1, 4k+2)`, the last point of the reversed vertical string (`BaseTwoEven.wv_even2`). The
family has a `zero` tile at `(-1, 4k+2)` and `one`/`oneD` tiles at `(j, j+4k+2)`, `1 ≤ j ≤ 2k+1`. The affine factors are
`(2k+1, -(2k+2))` at `0` and `(2k, -(2k+2))` from `1` on; the centred constants are `-(2k+1)(2k+3)` at `0` and
`-(4k²+6k+1) - 2j` from `1` on. The odometer is `paperNearLadderValue (2k+2) (x + (0,1))`. -/

namespace FLatticePaper.Tiles.BaseHmTwoEven

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.SiteStrings
open FLatticePaper.Tiles.BaseHpNearEven FLatticePaper.Tiles.BaseHmTwoOdd
open FLatticePaper.Tiles.BaseTileProps FLatticePaper.Tiles.VerticalRevBridge
open FLatticePaper.Tiles.BaseHmAnchor FLatticePaper.Tiles.BaseHmTwoAnchor

theorem wEv_rev (k : ℕ) : (wEv k).reverse = Letter.p :: List.replicate (2 * k + 1) Letter.q := by
  simp [wEv, List.reverse_append]

theorem lettersOf_wEv (k j : ℕ) :
    lettersOf (wEv k) true j = if j = 0 then Letter.p else if j ≤ 2 * k + 1 then Letter.q else Letter.p := by
  have hr := wEv_rev k
  unfold lettersOf
  simp only [if_true]
  rw [hr]
  cases j with
  | zero => simp
  | succ i =>
    rw [List.getD_cons_succ, FLatticePaper.Tiles.BaseTwoOdd.getD_rep_q]
    by_cases h1 : i < 2 * k + 1
    · rw [if_pos h1, if_neg (show ¬(i + 1 = 0) by omega), if_pos (show i + 1 ≤ 2 * k + 1 by omega)]
    · rw [if_neg h1, if_neg (show ¬(i + 1 = 0) by omega), if_neg (show ¬(i + 1 ≤ 2 * k + 1) by omega)]

/-- The positions of the reversed tiles of the even `2^k` piece. -/
def posE (k j : ℕ) : GInt :=
  if j = 0 then (-1, 4 * (k : ℤ) + 2) else ((j : ℤ), (j : ℤ) + 4 * (k : ℤ) + 2)

theorem posE_succ (k j : ℕ) (hj : j + 1 < 2 * k + 2) :
    posE k (j + 1) = posE k j +
      zeroOneHorizontalReversedStep (lettersOf (wEv k) true j) (lettersOf (wEv k) true (j + 1)) := by
  by_cases h0 : j = 0
  · subst h0
    rw [lettersOf_wEv, lettersOf_wEv, if_pos rfl, if_neg (show ¬((0 : ℕ) + 1 = 0) by omega),
      if_pos (show (0 : ℕ) + 1 ≤ 2 * k + 1 by omega)]
    unfold posE zeroOneHorizontalReversedStep
    simp only [if_neg (show ¬((0 : ℕ) + 1 = 0) by omega)]
    ext
    all_goals simp
    all_goals ring
  · rw [lettersOf_wEv, lettersOf_wEv, if_neg h0, if_neg (show ¬(j + 1 = 0) by omega),
      if_pos (show j ≤ 2 * k + 1 by omega), if_pos (show j + 1 ≤ 2 * k + 1 by omega)]
    unfold posE zeroOneHorizontalReversedStep
    simp only [if_neg (show ¬(j + 1 = 0) by omega), if_neg h0]
    ext
    all_goals simp
    all_goals ring

/-- The affine factor of the reversed even `2^k` piece: the letter factor plus the shift `(2k+1, -(2k+3))`. -/
def aE (k j : ℕ) : GInt :=
  alphaH (lettersOf (wEv k) true j) + ((2 * (k : ℤ) + 1), -(2 * (k : ℤ) + 3))

theorem aE_zero (k : ℕ) : aE k 0 = ((2 * (k : ℤ) + 1), -(2 * (k : ℤ) + 2)) := by
  rw [aE, lettersOf_wEv, if_pos rfl]
  refine Prod.ext ?_ ?_
  all_goals simp [alphaH]
  all_goals ring

theorem aE_pos (k j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ 2 * k + 1) :
    aE k j = ((2 * (k : ℤ)), -(2 * (k : ℤ) + 2)) := by
  rw [aE, lettersOf_wEv, if_neg (show ¬(j = 0) by omega), if_pos h2]
  refine Prod.ext ?_ ?_
  all_goals simp [alphaH]
  all_goals ring

/-- The centred constant of the reversed even `2^k` piece. -/
def cE (k j : ℕ) : ℤ :=
  if j = 0 then -((2 * (k : ℤ) + 1) * (2 * (k : ℤ) + 3))
  else -(4 * (k : ℤ) ^ 2 + 6 * (k : ℤ) + 1) - 2 * (j : ℤ)

theorem cE_succ (k j : ℕ) (hj : j + 1 < 2 * k + 2) :
    cE k (j + 1) = cE k j +
      ptDot (aE k j) (zeroOneHorizontalReversedStep (lettersOf (wEv k) true j) (lettersOf (wEv k) true (j + 1))) := by
  by_cases h0 : j = 0
  · subst h0
    rw [lettersOf_wEv, lettersOf_wEv, if_pos rfl, if_neg (show ¬((0 : ℕ) + 1 = 0) by omega),
      if_pos (show (0 : ℕ) + 1 ≤ 2 * k + 1 by omega), aE_zero]
    unfold cE ptDot zeroOneHorizontalReversedStep
    simp only [if_neg (show ¬((0 : ℕ) + 1 = 0) by omega)]
    push_cast
    ring
  · rw [lettersOf_wEv, lettersOf_wEv, if_neg h0, if_neg (show ¬(j + 1 = 0) by omega),
      if_pos (show j ≤ 2 * k + 1 by omega), if_pos (show j + 1 ≤ 2 * k + 1 by omega), aE_pos k j (by omega) (by omega)]
    unfold cE ptDot zeroOneHorizontalReversedStep
    simp only [if_neg (show ¬(j + 1 = 0) by omega), if_neg h0]
    push_cast
    ring

/-- The even `2^k` reversed horizontal family. -/
def HmEvenF (k : ℕ) : PTFamily :=
  { ts := (List.range (2 * k + 2)).map (fun j => (hTileAt (lettersOf (wEv k) true) j, posE k j)),
    a := fun j => aE k j,
    b := fun j => cE k j - ptDot (aE k j) (posE k j) }

theorem HmEvenF_n (k : ℕ) : (HmEvenF k).n = 2 * k + 2 := by
  simp [HmEvenF, PTFamily.n]

theorem HmEvenF_tile (k j : ℕ) (hj : j < 2 * k + 2) :
    (HmEvenF k).tile j = (hTileAt (lettersOf (wEv k) true) j, posE k j) := by
  unfold PTFamily.tile HmEvenF
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  simp

theorem HmEvenF_respects (k : ℕ) :
    (HmEvenF k).Respects .horizontal true :=
  PTFamily.respects_of_triples (HmEvenF k) .horizontal true (lettersOf (wEv k) true) (hPrev (lettersOf (wEv k) true))
    (fun j => posE k j) hTt
    (fun y z => zeroOneHorizontalReversedStep y z) (fun _ y z => alphaH z - alphaH y)
    (fun j => cE k j) (fun _ _ _ => (0 : ℤ)) (fun _ _ _ => True)
    (fun j hj => by
      rw [HmEvenF_n] at hj
      rw [HmEvenF_tile k j hj]
      rfl)
    (fun j _ => hPrev_succ _ j)
    (fun j hj => by
      rw [HmEvenF_n] at hj
      exact posE_succ k j (by omega))
    (fun j hj => by
      rw [HmEvenF_n] at hj
      show aE k (j + 1) = aE k j + (alphaH (lettersOf (wEv k) true (j + 1)) - alphaH (lettersOf (wEv k) true j))
      unfold aE
      abel)
    (fun j _ => rfl)
    (fun j hj => by
      rw [HmEvenF_n] at hj
      show cE k (j + 1) = cE k j + (0 : ℤ) +
        ptDot (aE k j) (zeroOneHorizontalReversedStep (lettersOf (wEv k) true j) (lettersOf (wEv k) true (j + 1)))
      rw [cE_succ k j (by omega)]
      ring)
    (fun _ _ => trivial)
    (fun x y => hTt_letter x y)
    (fun x y z _ => by
      cases y <;> cases z <;> simp [hTt_base_p, hTt_base_q, surgicalSlopeDiff, alphaH, Prod.ext_iff] <;> norm_num)
    (fun _ x y z _ u hu v hv hno hunit => hE_rev x y z u hu v hv hno hunit)
    (fun h => by cases h)

theorem sq_helper (k m : ℤ) : (4 * k + m) ^ 2 / 4 = 4 * k ^ 2 + 2 * m * k + m ^ 2 / 4 := by
  have h : (4 * k + m) ^ 2 = m ^ 2 + (4 * k ^ 2 + 2 * m * k) * 4 := by ring
  rw [h, Int.add_mul_ediv_right _ _ (by norm_num)]
  ring

theorem posE_zero (k : ℕ) : posE k 0 = (-1, 4 * (k : ℤ) + 2) := by
  unfold posE; rw [if_pos rfl]

theorem posE_pos (k j : ℕ) (hj : 1 ≤ j) :
    posE k j = ((j : ℤ), (j : ℤ) + 4 * (k : ℤ) + 2) := by
  unfold posE; rw [if_neg (by omega)]

theorem tileE_zero (k : ℕ) : hTileAt (lettersOf (wEv k) true) 0 = ZTile.zero := by
  unfold hTileAt hPrev
  rw [if_pos rfl, lettersOf_wEv, if_pos rfl]
  rfl

theorem tileE_one (k : ℕ) : hTileAt (lettersOf (wEv k) true) 1 = ZTile.one := by
  unfold hTileAt hPrev
  rw [if_neg (show ¬ (1 : ℕ) = 0 by omega), show (1 : ℕ) - 1 = 0 from rfl, lettersOf_wEv, if_pos rfl,
    lettersOf_wEv, if_neg (show ¬ (1 : ℕ) = 0 by omega), if_pos (show (1 : ℕ) ≤ 2 * k + 1 by omega)]
  rfl

theorem tileE_D (k j : ℕ) (hj1 : 2 ≤ j) (hj2 : j ≤ 2 * k + 1) :
    hTileAt (lettersOf (wEv k) true) j = ZTile.oneD := by
  unfold hTileAt hPrev
  rw [if_neg (show ¬ j = 0 by omega), lettersOf_wEv, if_neg (show ¬ (j - 1 = 0) by omega),
    if_pos (show j - 1 ≤ 2 * k + 1 by omega), lettersOf_wEv, if_neg (show ¬ j = 0 by omega), if_pos hj2]
  rfl

theorem evenE_zero (k : ℕ) (hk : 1 ≤ k) (u : GInt) (hu : u ∈ tileShape ZTile.zero) :
    paperNearLadderValue (2 * (k : ℤ) + 2) (u + posE k 0 + (0, 1)) =
      zTileOdo ZTile.zero u + ptDot (aE k 0) u + cE k 0 := by
  have hk' : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  obtain ⟨u1, u2⟩ := u
  rw [posE_zero, aE_zero, cE, if_pos rfl,
    show -((2 * (k : ℤ) + 1) * (2 * (k : ℤ) + 3)) = -(4 * (k : ℤ) ^ 2 + 8 * (k : ℤ) + 3) by ring]
  rw [show ((u1, u2) + (-1, 4 * (k : ℤ) + 2) + (0, 1) : GInt) = (u1 - 1, u2 + 4 * (k : ℤ) + 3) by
    ext <;> ((try simp); (try ring))]
  rw [pnlV, show u2 + 4 * (k : ℤ) + 3 - (u1 - 1) = 4 * (k : ℤ) + (u2 - u1 + 4) by ring, sq_helper]
  generalize (k : ℤ) ^ 2 = K2
  simp only [tileShape, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hu
  rcases hu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    (norm_num [zTileOdo, zeroOdometer, ptDot, min_def, max_def]; (try split_ifs) <;> omega)

theorem evenE_one (k : ℕ) (hk : 1 ≤ k) (u : GInt) (hu : u ∈ tileShape ZTile.one) :
    paperNearLadderValue (2 * (k : ℤ) + 2) (u + posE k 1 + (0, 1)) =
      zTileOdo ZTile.one u + ptDot (aE k 1) u + cE k 1 := by
  have hk' : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  have hp : posE k 1 = (1, 4 * (k : ℤ) + 3) := by
    rw [posE_pos k 1 le_rfl]; ext <;> ((try simp); (try ring))
  obtain ⟨u1, u2⟩ := u
  rw [hp, aE_pos k 1 le_rfl (by omega), cE, if_neg (show ¬ (1 : ℕ) = 0 by omega)]
  rw [show ((u1, u2) + (1, 4 * (k : ℤ) + 3) + (0, 1) : GInt) = (u1 + 1, u2 + 4 * (k : ℤ) + 4) by
    ext <;> ((try simp); (try ring))]
  rw [pnlV, show u2 + 4 * (k : ℤ) + 4 - (u1 + 1) = 4 * (k : ℤ) + (u2 - u1 + 3) by ring, sq_helper]
  generalize (k : ℤ) ^ 2 = K2
  simp only [tileShape, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hu
  rcases hu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    (norm_num [zTileOdo, oneOdometer, ptDot, min_def, max_def]; (try split_ifs) <;> omega)

theorem evenE_D (k j : ℕ) (hk : 1 ≤ k) (hj1 : 2 ≤ j) (hj2 : j ≤ 2 * k + 1) (u : GInt)
    (hu : u ∈ tileShape ZTile.oneD) :
    paperNearLadderValue (2 * (k : ℤ) + 2) (u + posE k j + (0, 1)) =
      zTileOdo ZTile.oneD u + ptDot (aE k j) u + cE k j := by
  have hk' : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  have hj' : (2 : ℤ) ≤ (j : ℤ) := by exact_mod_cast hj1
  have hj2' : (j : ℤ) ≤ 2 * (k : ℤ) + 1 := by exact_mod_cast hj2
  obtain ⟨u1, u2⟩ := u
  rw [posE_pos k j (by omega), aE_pos k j (by omega) hj2, cE, if_neg (show ¬ j = 0 by omega)]
  rw [show ((u1, u2) + ((j : ℤ), (j : ℤ) + 4 * (k : ℤ) + 2) + (0, 1) : GInt) =
      (u1 + (j : ℤ), u2 + (j : ℤ) + 4 * (k : ℤ) + 3) by ext <;> ((try simp); (try ring))]
  simp only [tileShape, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hu
  obtain ⟨hu1a, hu1b, hu2a, hu2b⟩ : -1 ≤ u1 ∧ u1 ≤ 1 ∧ -1 ≤ u2 ∧ u2 ≤ 1 := by omega
  rw [pnlV, show u2 + (j : ℤ) + 4 * (k : ℤ) + 3 - (u1 + (j : ℤ)) = 4 * (k : ℤ) + (u2 - u1 + 3) by ring,
    sq_helper]
  rw [min_eq_right (show 2 * (k : ℤ) + 2 - (u2 + (j : ℤ) + 4 * (k : ℤ) + 3) ≤ 0 by omega),
    min_eq_right (show 2 * (2 * (k : ℤ) + 2) - (u2 + (j : ℤ) + 4 * (k : ℤ) + 3) ≤ 0 by omega),
    max_eq_left (show (0 : ℤ) ≤ 4 * (k : ℤ) + (u2 - u1 + 3) - (2 * (k : ℤ) + 2) by omega)]
  split_ifs with hind
  · exfalso
    simp only [Prod.mk.injEq] at hind
    omega
  generalize (k : ℤ) ^ 2 = K2
  rcases hu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    (norm_num [zTileOdo, oneOdometer, ptDot]; omega)

theorem lastPos_vRev_run (n : ℕ) (T : BinaryWord) (c : GInt) :
    lastPosOf (vRevStringAt (List.replicate (n + 1) Letter.q ++ (Letter.p :: T)) c) =
      lastPosOf (vRevStringAt (Letter.p :: T) (c + (0, 2 * (n : ℤ) + 1))) := by
  induction n generalizing c with
  | zero =>
    show lastPosOf (vRevStringAt (Letter.q :: (Letter.p :: T)) c) = _
    rw [vRevStringAt_cons2, lastPosOf_cons_of_ne _ _ (by simp [vRevStringAt])]
    ext <;> simp [vRevOffset]
  | succ n ih =>
    have h1 : List.replicate (n + 1 + 1) Letter.q ++ (Letter.p :: T) =
        Letter.q :: Letter.q :: (List.replicate n Letter.q ++ (Letter.p :: T)) := by
      simp [List.replicate_succ]
    have h2 : Letter.q :: (List.replicate n Letter.q ++ (Letter.p :: T)) =
        List.replicate (n + 1) Letter.q ++ (Letter.p :: T) := by
      simp [List.replicate_succ]
    rw [h1, vRevStringAt_cons2, h2, lastPosOf_cons_of_ne _ _ (by simp [vRevStringAt]), ih]
    rw [show (c + vRevOffset Letter.q Letter.q + (0, 2 * (n : ℤ) + 1) : GInt) =
        c + (0, 2 * ((n + 1 : ℕ) : ℤ) + 1) by ext <;> ((try simp [vRevOffset]); (try ring))]

theorem tailE (k : ℕ) (c : GInt) :
    lastPosOf (vRevStringAt (Letter.p :: (List.replicate k Letter.q ++ [Letter.p])) c) =
      c + (-1, 2 * (k : ℤ) + 1) := by
  cases k with
  | zero =>
    show lastPosOf (vRevStringAt [Letter.p, Letter.p] c) = _
    rw [vRevStringAt_cons, vRevStringAt_single_p]
    ext <;> simp [lastPosOf, vRevOffset]
  | succ k =>
    have h : Letter.p :: (List.replicate (k + 1) Letter.q ++ [Letter.p]) =
        Letter.p :: Letter.q :: (List.replicate k Letter.q ++ [Letter.p]) := by
      simp [List.replicate_succ]
    have h2 : Letter.q :: (List.replicate k Letter.q ++ [Letter.p]) =
        List.replicate (k + 1) Letter.q ++ [Letter.p] := by
      simp [List.replicate_succ]
    rw [h, vRevStringAt_cons2, h2, lastPosOf_cons_of_ne _ _ (by simp [vRevStringAt]), lastPos_vRev_qq_p k]
    ext <;> ((try simp [vRevOffset]); (try ring))

theorem anchor_hm_even (k : ℕ) :
    lastPosOf (vRevStringAt (vWordOf (List.replicate k Digit.two) true).reverse (0, 0)) = posE k 0 := by
  rw [BaseTwoEven.wv_even2 k]
  simp only [BaseTwoEven.W4]
  have hrev : (Letter.p :: (List.replicate k Letter.q ++ (Letter.p :: List.replicate (k + 1) Letter.q))).reverse =
      List.replicate (k + 1) Letter.q ++ (Letter.p :: (List.replicate k Letter.q ++ [Letter.p])) := by
    simp [List.reverse_append, List.reverse_replicate]
  rw [hrev, lastPos_vRev_run k _ (0, 0), tailE k, posE_zero]
  ext <;> ((try simp); (try ring))

theorem evenOdo_eq (k j : ℕ) (hk : 1 ≤ k) (hj : j < 2 * k + 2) (x : GInt) (hx : x ∈ (HmEvenF k).dom j) :
    paperNearLadderValue (2 * (k : ℤ) + 2) (x + (0, 1)) = (HmEvenF k).odo j x := by
  have hdom := hx
  unfold PTFamily.dom at hdom
  rw [HmEvenF_tile k j hj] at hdom
  simp only [List.mem_map] at hdom
  obtain ⟨u, hu, rfl⟩ := hdom
  have key : paperNearLadderValue (2 * (k : ℤ) + 2) (u + posE k j + (0, 1)) =
      zTileOdo (hTileAt (lettersOf (wEv k) true) j) u + ptDot (aE k j) u + cE k j := by
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [tileE_zero] at hu ⊢
      exact evenE_zero k hk u hu
    · rcases Nat.lt_or_ge j 2 with hj2 | hj2
      · obtain rfl : j = 1 := by omega
        rw [tileE_one] at hu ⊢
        exact evenE_one k hk u hu
      · rw [tileE_D k j hj2 (by omega)] at hu ⊢
        exact evenE_D k j hk hj2 (by omega) u hu
  unfold PTFamily.odo
  rw [HmEvenF_tile k j hj]
  show paperNearLadderValue _ (u + posE k j + (0, 1)) =
    zTileOdo (hTileAt (lettersOf (wEv k) true) j) (u + posE k j - posE k j) + (aE k j).1 * (u + posE k j).1 +
      (aE k j).2 * (u + posE k j).2 + (cE k j - ptDot (aE k j) (posE k j))
  rw [key, add_sub_cancel_right]
  unfold ptDot
  simp only [Prod.fst_add, Prod.snd_add]
  ring

/-- The reversed horizontal string of the even `2^k` word, anchored at `posE k 0`, is respected by the near-ladder value
`paperNearLadderValue (2k+2)` shifted by `(0,1)`. -/
theorem respects_hm_even (k : ℕ) (hk : 1 ≤ k) :
    RespectsTiles .horizontal true (hRevStringAt (wEv k).reverse (posE k 0))
      (fun x => paperNearLadderValue (2 * (k : ℤ) + 2) (x + (0, 1))) := by
  have hl : lettersOf (wEv k) true = lettersOf (wEv k).reverse false := rfl
  have hts : (HmEvenF k).ts = hRevStringAt (wEv k).reverse (posE k 0) := by
    rw [hRevStringAt_eq_map (wEv k).reverse (posE k 0) (posE k) rfl (fun j hj => by
      rw [List.length_reverse, wEv_length] at hj
      exact posE_succ k j (by omega))]
    unfold HmEvenF
    rw [hl, List.length_reverse, wEv_length]
  exact ⟨HmEvenF k, hts, fun j hj x hx => evenOdo_eq k j hk (by rw [HmEvenF_n] at hj; exact hj) x hx,
    HmEvenF_respects k⟩

end FLatticePaper.Tiles.BaseHmTwoEven
